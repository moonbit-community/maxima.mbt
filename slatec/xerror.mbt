// SLATEC error-message routines XERMSG, XERPRN and XERSVE, ported by hand
// from Maxima's f2cl translations (numerical/slatec/xermsg.lisp, xerprn.lisp,
// xersve.lisp) because they work on Fortran CHARACTER variables and
// formatted output.  The control flow, the message table and the counters
// follow the Lisp exactly (including f2cl-lib's INDEX returning a 0-based
// position), so callers see identical error-control behaviour; the messages
// are printed to standard output, as the Lisp does for unit 6.

///|
/// Fortran CHARACTER*n assignment: pad with blanks or truncate to `n`.
fn fstr(s : String, n : Int) -> String {
  let len = s.length()
  if len == n {
    s
  } else if len > n {
    fsub(s, 1, n)
  } else {
    s + String::make(n - len, ' ')
  }
}

///|
/// Fortran substring s(a:b), 1-based and inclusive.
fn fsub(s : String, a : Int, b : Int) -> String {
  let sb = StringBuilder()
  for k in (a - 1)..<b {
    sb.write_char(s.get_char(k).unwrap())
  }
  sb.to_string()
}

///|
/// A fixed-length Fortran character buffer.
priv struct CharBuf {
  chars : FixedArray[Char]
}

///|
fn CharBuf::new(n : Int) -> CharBuf {
  { chars: FixedArray::make(n, ' ') }
}

///|
/// f2cl-lib FSET-STRING of buf(a:b) = src: replaces min(b-a+1, len(src))
/// characters starting at position a.
fn CharBuf::set(self : CharBuf, a : Int, b : Int, src : String) -> Unit {
  let n = i_min(b - a + 1, src.length())
  for k in 0..<n {
    self.chars[a - 1 + k] = src.get_char(k).unwrap()
  }
}

///|
fn CharBuf::sub(self : CharBuf, a : Int, b : Int) -> String {
  let sb = StringBuilder()
  for k in (a - 1)..<b {
    sb.write_char(self.chars[k])
  }
  sb.to_string()
}

///|
/// f2cl-lib INDEX: (or (search s2 s1) 0) -- a 0-based position, or 0.
fn f2cl_index(s1 : String, s2 : String) -> Int {
  match s1.find(s2) {
    Some(p) => p
    None => 0
  }
}

///|
/// Output of FFORMAT to a Fortran unit; units 5/6 are standard I/O in f2cl,
/// everything is printed to standard output here.
fn fortran_write_line(_unit : Int, line : String) -> Unit {
  println(line)
}

///|
/// XERPRN: print an error message, splitting it at "$$" markers and wrapping
/// at NWRAP columns, each line preceded by PREFIX.
pub fn xerprn(prefix : String, npref : Int, messg : String, nwrap : Int) -> Unit {
  let iu : FixedArray[Int] = FixedArray::make(5, 0)
  let nunit = xgetua(iu, 0)
  let n0 = i1mach(4)
  for i in 1..=nunit {
    if iu[i - 1] == 0 {
      iu[i - 1] = n0
    }
  }
  let cbuff = CharBuf::new(148)
  let mut lpref = if npref < 0 { prefix.length() } else { npref }
  lpref = i_min(16, lpref)
  if lpref != 0 {
    cbuff.set(1, lpref, prefix)
  }
  let lwrap = i_max(16, i_min(132, nwrap))
  let mut lenmsg = messg.length()
  let n = lenmsg
  for _i in 1..=n {
    if fsub(messg, lenmsg, lenmsg) != " " {
      break
    }
    lenmsg = lenmsg - 1
  }
  if lenmsg == 0 {
    cbuff.set(lpref + 1, lpref + 1, " ")
    for i in 1..=nunit {
      fortran_write_line(iu[i - 1], cbuff.sub(1, lpref + 1))
    }
    return
  }
  let mut nextc = 1
  while true {
    // label50
    let mut lpiece = f2cl_index(fsub(messg, nextc, lenmsg), "$$")
    if lpiece == 0 {
      let mut idelta = 0
      lpiece = i_min(lwrap, lenmsg + 1 - nextc)
      if lpiece < lenmsg + 1 - nextc {
        let mut i = lpiece + 1
        while i >= 2 {
          if fsub(messg, nextc + i - 1, nextc + i - 1) == " " {
            lpiece = i - 1
            idelta = 1
            break
          }
          i = i - 1
        }
      }
      cbuff.set(lpref + 1, lpref + lpiece, fsub(messg, nextc, nextc + lpiece - 1))
      nextc = nextc + lpiece + idelta
    } else if lpiece == 1 {
      nextc = nextc + 2
      continue
    } else if lpiece > lwrap + 1 {
      let mut idelta = 0
      lpiece = lwrap
      let mut i = lpiece + 1
      while i >= 2 {
        if fsub(messg, nextc + i - 1, nextc + i - 1) == " " {
          lpiece = i - 1
          idelta = 1
          break
        }
        i = i - 1
      }
      cbuff.set(lpref + 1, lpref + lpiece, fsub(messg, nextc, nextc + lpiece - 1))
      nextc = nextc + lpiece + idelta
    } else {
      lpiece = lpiece - 1
      cbuff.set(lpref + 1, lpref + lpiece, fsub(messg, nextc, nextc + lpiece - 1))
      nextc = nextc + lpiece + 2
    }
    for i in 1..=nunit {
      fortran_write_line(iu[i - 1], cbuff.sub(1, lpref + lpiece))
    }
    if nextc > lenmsg {
      break
    }
  }
}

///|
let xersve_lentab : Int = 10

///|
let xersve_nmsg : Ref[Int] = { val: 0 }

///|
let xersve_kountx : Ref[Int] = { val: 0 }

///|
let xersve_kount : FixedArray[Int] = FixedArray::make(10, 0)

///|
let xersve_levtab : FixedArray[Int] = FixedArray::make(10, 0)

///|
let xersve_nertab : FixedArray[Int] = FixedArray::make(10, 0)

///|
let xersve_mestab : FixedArray[String] = FixedArray::make(10, fstr("", 20))

///|
let xersve_subtab : FixedArray[String] = FixedArray::make(10, fstr("", 8))

///|
let xersve_libtab : FixedArray[String] = FixedArray::make(10, fstr("", 8))

///|
/// Right-justify `n` in a field of `w` columns (CL ~wD).
fn fmt_int(n : Int, w : Int) -> String {
  let s = n.to_string()
  if s.length() >= w {
    s
  } else {
    String::make(w - s.length(), ' ') + s
  }
}

///|
/// XERSVE: record that an error message has occurred (KFLAG > 0) and return
/// how many times it has been seen, or print and/or clear the summary table
/// (KFLAG <= 0).  Returns the updated ICOUNT.
pub fn xersve(
  librar : String,
  subrou : String,
  messg : String,
  kflag : Int,
  nerr : Int,
  level : Int,
  icount : Int,
) -> Int {
  if kflag <= 0 {
    if xersve_nmsg.val == 0 {
      return icount
    }
    let lun : FixedArray[Int] = FixedArray::make(5, 0)
    let nunit = xgetua(lun, 0)
    for kunit in 1..=nunit {
      let mut iunit = lun[kunit - 1]
      if iunit == 0 {
        iunit = i1mach(4)
      }
      fortran_write_line(iunit, "0          ERROR MESSAGE SUMMARY")
      fortran_write_line(
        iunit, " LIBRARY    SUBROUTINE MESSAGE START             NERR     LEVEL     COUNT",
      )
      for i in 1..=xersve_nmsg.val {
        fortran_write_line(
          iunit,
          " " +
          xersve_libtab[i - 1] +
          "   " +
          xersve_subtab[i - 1] +
          "   " +
          xersve_mestab[i - 1] +
          fmt_int(xersve_nertab[i - 1], 10) +
          fmt_int(xersve_levtab[i - 1], 10) +
          fmt_int(xersve_kount[i - 1], 10),
        )
      }
      if xersve_kountx.val != 0 {
        fortran_write_line(
          iunit,
          "0OTHER ERRORS NOT INDIVIDUALLY TABULATED = " +
          fmt_int(xersve_kountx.val, 10),
        )
      }
      fortran_write_line(iunit, " ")
    }
    if kflag == 0 {
      xersve_nmsg.val = 0
      xersve_kountx.val = 0
    }
    return icount
  }
  let lib = fstr(librar, 8)
  let sub = fstr(subrou, 8)
  let mes = fstr(messg, 20)
  let nmsg = xersve_nmsg.val
  for i in 1..=nmsg {
    if lib == xersve_libtab[i - 1] &&
      sub == xersve_subtab[i - 1] &&
      mes == xersve_mestab[i - 1] &&
      nerr == xersve_nertab[i - 1] &&
      level == xersve_levtab[i - 1] {
      xersve_kount[i - 1] = xersve_kount[i - 1] + 1
      return xersve_kount[i - 1]
    }
  }
  if nmsg < xersve_lentab {
    // After the search loop the DO variable is NMSG + 1.
    let i = nmsg + 1
    xersve_nmsg.val = nmsg + 1
    xersve_libtab[i - 1] = lib
    xersve_subtab[i - 1] = sub
    xersve_mestab[i - 1] = mes
    xersve_nertab[i - 1] = nerr
    xersve_levtab[i - 1] = level
    xersve_kount[i - 1] = 1
    1
  } else {
    xersve_kountx.val = xersve_kountx.val + 1
    0
  }
}

///|
/// XERMSG: process an error (diagnostic) message.  LEVEL is -1 (warning
/// printed once), 0 (warning), 1 (recoverable error) or 2 (fatal error).
/// Printing is controlled by J4SAVE(2) (default 2: full messages) and
/// J4SAVE(4) (default 10: maximum times a message is printed).  The final
/// XERHLT is f2cl's STOP, which only returns (*STOP-SIGNALS-ERROR-P* is NIL),
/// so XERMSG always returns to its caller.
pub fn xermsg(
  librar : String,
  subrou : String,
  messg : String,
  nerr : Int,
  level : Int,
) -> Unit {
  let mut kdummy = 0
  let mut kount = 0
  let mut lkntrl = j4save(2, 0, false)
  let maxmes = j4save(4, 0, false)
  if nerr < -9999999 ||
    nerr > 99999999 ||
    nerr == 0 ||
    level < -1 ||
    level > 2 {
    xerprn(
      " ***",
      -1,
      "FATAL ERROR IN...$$ " +
      "XERMSG -- INVALID ERROR NUMBER OR LEVEL$$ " +
      "JOB ABORT DUE TO FATAL ERROR.",
      72,
    )
    kdummy = xersve(" ", " ", " ", 0, 0, 0, kdummy)
    xerhlt(" ***XERMSG -- INVALID INPUT")
    return
  }
  let _ = j4save(1, nerr, true)
  kount = xersve(librar, subrou, messg, 1, nerr, level, kount)
  if level == -1 && kount > 1 {
    return
  }
  let xlibr = fstr(librar, 8)
  let xsubr = fstr(subrou, 8)
  let lfirst = fstr(messg, 20)
  xercnt(xlibr, xsubr, lfirst, nerr, level, lkntrl)
  lkntrl = i_max(-2, i_min(2, lkntrl))
  let mkntrl = i_abs(lkntrl)
  let skip = (level < 2 && lkntrl == 0) ||
    (level == 0 && kount > maxmes) ||
    (level == 1 && kount > maxmes && mkntrl == 1) ||
    (level == 2 && kount > i_max(1, maxmes))
  if !skip {
    let temp = CharBuf::new(72)
    if lkntrl != 0 {
      temp.set(1, 21, "MESSAGE FROM ROUTINE ")
      let mut i = i_min(subrou.length(), 16)
      temp.set(22, 21 + i, fsub(subrou, 1, i))
      temp.set(22 + i, 33 + i, " IN LIBRARY ")
      let mut ltemp = 33 + i
      i = i_min(librar.length(), 16)
      temp.set(ltemp + 1, ltemp + i, fsub(librar, 1, i))
      temp.set(ltemp + i + 1, ltemp + i + 1, ".")
      ltemp = ltemp + i + 1
      xerprn(" ***", -1, temp.sub(1, ltemp), 72)
    }
    if lkntrl > 0 {
      let mut ltemp = 0
      if level <= 0 {
        temp.set(1, 20, "INFORMATIVE MESSAGE,")
        ltemp = 20
      } else if level == 1 {
        temp.set(1, 30, "POTENTIALLY RECOVERABLE ERROR,")
        ltemp = 30
      } else {
        temp.set(1, 12, "FATAL ERROR,")
        ltemp = 12
      }
      if (mkntrl == 2 && level >= 1) || (mkntrl == 1 && level == 2) {
        temp.set(ltemp + 1, ltemp + 14, " PROG ABORTED,")
        ltemp = ltemp + 14
      } else {
        temp.set(ltemp + 1, ltemp + 16, " PROG CONTINUES,")
        ltemp = ltemp + 16
      }
      if lkntrl > 0 {
        temp.set(ltemp + 1, ltemp + 20, " TRACEBACK REQUESTED")
        ltemp = ltemp + 20
      } else {
        temp.set(ltemp + 1, ltemp + 24, " TRACEBACK NOT REQUESTED")
        ltemp = ltemp + 24
      }
      xerprn(" ***", -1, temp.sub(1, ltemp), 72)
    }
    xerprn(" *  ", -1, messg, 72)
    if lkntrl > 0 {
      // (fformat temp ("ERROR NUMBER = " 1 (("~8D")) "~%") nerr)
      let line = "ERROR NUMBER = " + fmt_int(nerr, 8) + "\n"
      temp.set(1, line.length(), line)
      let mut i = 16
      while i <= 22 {
        if temp.sub(i, i) != " " {
          break
        }
        i = i + 1
      }
      xerprn(" *  ", -1, temp.sub(1, 15) + temp.sub(i, 23), 72)
      fdump()
    }
    if lkntrl != 0 {
      xerprn(" *  ", -1, " ", 72)
      xerprn(" ***", -1, "END OF MESSAGE", 72)
      xerprn("    ", 0, " ", 72)
    }
  }
  // label30
  if level <= 0 || (level == 1 && mkntrl <= 1) {
    return
  }
  if lkntrl > 0 && kount < i_max(1, maxmes) {
    if level == 1 {
      xerprn(" ***", -1, "JOB ABORT DUE TO UNRECOVERED ERROR.", 72)
    } else {
      xerprn(" ***", -1, "JOB ABORT DUE TO FATAL ERROR.", 72)
    }
    kdummy = xersve(" ", " ", " ", -1, 0, 0, kdummy)
    xerhlt(" ")
  } else {
    xerhlt(messg)
  }
}
