// Port of src/float.lisp, part 4: reading and printing bigfloats
// (FPSCAN, FPFORMAT, the ~E/~F/~G helpers), and conversion of bigfloats to
// rationals.

///|
/// `#.(/ (log 10.0) (log 2.0))`
let float__log2_10 : Double = @math.ln(10.0) / @math.ln(2.0)

///|
/// FPSCAN is called by lexical scan when a bigfloat is encountered.  For
/// example, 12.01B-3 would be the result of (FPSCAN '(/1 /2) '(/0 /1) '(/- /3))
/// Arguments to FPSCAN are a list of characters to the left of the decimal
/// point, to the right of the decimal point, and in the exponent.
fn fpscan(lft : Value, rt : Value, exp_ : Value) -> Value raise {
  with_specials(
    [(q_ear_read_base, Fix(10L)), (q_n_starm, Fix(1L)), (q_n_starcancelled, Fix(0L))],
    () => {
      let exp = readlist(exp_)
      bigfloatp(
        with_specials(
          [
            (
              q_fpprec,
              num_add(
                num_add(
                  num_add(Fix(4L), float__prec()),
                  int(integer_length(exp)),
                ),
                floor1(Flo(1.0 + float__log2_10 * length(lft).to_double())),
              ),
            ),
            (q_d_float, Nil),
          ],
          () => {
            let temp = add2(
              readlist(lft),
              div(readlist(rt), expt(Fix(10L), int(length(rt)))),
            )
            d_bfloat(
              if num_gt(num_abs(exp), Fix(1000L)) {
                cons(list1(q_mtimes), list2(temp, mk(q_mexpt, [Fix(10L), exp])))
              } else {
                mul2(temp, power(Fix(10L), exp))
              },
            )
          },
        ),
      )
    },
  )
}

///|
fn dim_bigfloat(form : Value, result : Value) -> Value raise {
  with_special(q_d_lispdisp, Nil, () => dimension_atom(
    maknam(fpformat(form)),
    result,
  ))
}

///|
/// Converts the bigfloat L to list of digits including |.| and the exponent
/// marker |b|. The number of significant digits is controlled by
/// $fpprintprec.
fn fpformat(l0 : Value) -> Value raise {
  let mut l = l0
  if memq(q_simp, cdar(l)) is Nil {
    l = cons(cons(caar(l), cons(q_simp, cdar(l))), cdr(l))
  }
  if equal(cadr(l), Fix(0L)) {
    if !equal(caddr(l), Fix(0L)) {
      mtell(
        list([
          Str("FPFORMAT: warning: detected an incorrect form of 0.0b0: ~M, ~M~%"),
          cadr(l),
          caddr(l),
        ]),
      )
      |> ignore
    }
    return list([q_n0, q_op_dot, q_n0, q_b, q_n0])
  }
  // L IS ALWAYS POSITIVE FP NUMBER
  let extradigs = floor1(
    num_add(
      Fix(1L),
      float__quot(int(integer_length(caddr(l))), Flo(float__log2_10)),
    ),
  )
  with_specials(
    [
      (
        q_fpprec,
        num_add(extradigs, decimalsin(num_sub(bigfloat_prec(l), Fix(2L)))),
      ),
      (q_n_starm, Fix(1L)),
      (q_n_starcancelled, Fix(0L)),
    ],
    () => {
      let lv = with_special(q_n_stardecfp, t, () => {
        let of = bigfloat_prec(l)
        let l = cdr(l)
        let expon = num_sub(cadr(l), of)
        let l = if minusp(expon) {
          fpquotient(intofp(car(l)), fpintexpt(Fix(2L), num_neg(expon), of))
        } else {
          fptimes_star(intofp(car(l)), fpintexpt(Fix(2L), expon, of))
        }
        set(q_fpprec, num_add(float__prec(), num_neg(extradigs))) |> ignore
        let m = fpround(car(l))
        list([
          m,
          num_add(num_add(num_neg(extradigs), symval(q_n_starm)), cadr(l)),
        ])
      })
      with_specials([(q_ear_print_base, Fix(10L)), (q_ear_print_radix, Nil)], () => {
        let prec = float__prec()
        let pp = symval(q_d_fpprintprec)
        let effective_printprec = if num_eq(pp, Fix(0L)) || num_gt(pp, prec) {
          prec
        } else {
          pp
        }
        let integer_to_explode = num_round(
          car(lv),
          b=expt(Fix(10L), num_sub(prec, effective_printprec)),
        ).0
        let mut exploded_integer = explodec(integer_to_explode)
        // If the rounded integer has more digits than expected, we need to
        // adjust the exponent by this amount.  This also means we need to
        // remove these extra digits so that the result has the desired
        // number of digits.
        let expo_adjust = num_sub(
          int(length(exploded_integer)),
          effective_printprec,
        )
        if plusp(expo_adjust) {
          exploded_integer = butlast(exploded_integer, n=to_int(expo_adjust))
        }
        let l1 = if symval(q_d_bftrunc).truthy() {
          let mut ll = nreverse(exploded_integer)
          while eq(q_n0, car(ll)) {
            ll = cdr(ll)
          }
          nreverse(ll)
        } else {
          exploded_integer
        }
        nconc_n([
          list1(car(l1)),
          list1(q_op_dot),
          if cdr(l1).truthy() {
            cdr(l1)
          } else {
            list1(q_n0)
          },
          list1(q_b),
          explodec(num_add(one_minus(cadr(lv)), expo_adjust)),
        ])
      })
    },
  )
}

///|
/// `(format nil "~{~A~}" list)`
fn float__concat(l : Value) -> String {
  let sb = StringBuilder::new()
  for x in l.iter() {
    sb.write_string(princ_to_string(x))
  }
  sb.to_string()
}

///|
/// Compute the (decimal exponent) of the bfloat number X.
fn float__exponent_value(x : Value) -> Int raise {
  with_special(q_d_fpprintprec, Fix(1L), () => {
    let f = fpformat(x)
    let marker = position(q_b, f)
    let s = float__concat(nthcdr(marker + 1, f))
    match parse_integer(s) {
      Some(v) => to_int(v)
      None => raise LispError::SimpleError("bad bigfloat exponent: " + s)
    }
  })
}

///|
fn float__make_list(n : Int, x : Value) -> Value {
  let c = Collector::new()
  for _ in 0..<n {
    c.add(x)
  }
  c.result()
}

///|
fn float__zeros(n : Int) -> String {
  let sb = StringBuilder::new()
  for _ in 0..<n {
    sb.write_char('0')
  }
  sb.to_string()
}

///|
fn float__write_n(c : Value, n : Int, stream : Value) -> Unit raise {
  for _ in 0..<n {
    match c {
      Char(ch) => write_char(ch, stream~)
      _ => raise LispError::SimpleError("write-char: not a character")
    }
  }
}

///|
fn float__write_c(c : Value, stream : Value) -> Unit raise {
  float__write_n(c, 1, stream)
}

///|
fn float__opt_int(v : Value) -> Int? raise {
  if v is Nil {
    None
  } else {
    Some(to_int(v))
  }
}

///|
/// The BFLOAT-TO-STRING of BFLOAT-FORMAT-E and BFLOAT-FORMAT-G: print the
/// bfloat X with FDIGITS after the decimal point, with $fpprintprec bound
/// to PRINTPREC, moving the decimal point according to K.
fn float__bts_eg(
  x : Value,
  fdigits : Int?,
  printprec : Int,
  k : Int,
) -> (String, Int, Bool, Bool) raise {
  with_special(q_d_fpprintprec, int(printprec), () => {
    let f = fpformat(bcons(fpabs(cdr(x))))
    let marker = position(q_b, f)
    let mut digits = remove(q_op_dot, subseq(f, 0, end=marker))
    // DIGITS was printed assuming the decimal point is after the first
    // digit. But if fdigits = 0, fpformat actually printed out one too many
    // digits, so we need to remove that.
    if fdigits is Some(0) {
      digits = butlast(digits)
    }
    if k == 0 {
      digits = cons(q_op_dot, digits)
    } else if k < 0 {
      // Put the leading decimal and then some zeroes
      for _ in 0..<(-k) {
        digits = cons(Char('0'), digits)
      }
      digits = cons(q_op_dot, digits)
    } else {
      // The number is scaled by 10^k. Do this by putting the decimal point
      // in the right place, appending zeroes if needed.
      let n = length(digits)
      digits = if k > n {
        append_n([digits, float__make_list(k - n, Char('0')), list1(q_op_dot)])
      } else {
        append_n([
          subseq(digits, 0, end=k),
          list1(q_op_dot),
          subseq(digits, k),
        ])
      }
    }
    let mut str = float__concat(digits)
    let mut len = str.length()
    match fdigits {
      Some(fd) if fd >= len => {
        // Append some zeroes to get the desired number of digits
        str = str + float__zeros(1 + k + (fd - len))
        len = str.length()
      }
      _ => ()
    }
    (str, len, str[0] == '.', str[str.length() - 1] == '.')
  })
}

///|
/// A modified version of FORMAT-EXP-AUX from CMUCL to support printing of
/// bfloats.
fn bfloat_format_e(
  stream : Value,
  arg : Value,
  colonp : Value,
  atp : Value,
  w? : Value = Nil,
  d? : Value = Nil,
  e? : Value = Nil,
  k? : Value = Fix(1L),
  overflowchar? : Value = Nil,
  padchar? : Value = Char(' '),
  exponentchar? : Value = Nil,
) -> Value raise {
  ignore(colonp)
  let wi = float__opt_int(w)
  let di = float__opt_int(d)
  let ei = float__opt_int(e)
  let ki = to_int(k)
  let num_expt = float__exponent_value(arg)
  let expt_ = if zerop(second(arg)) { 0 } else { 1 + (num_expt - ki) }
  let estr = (if expt_ < 0 { -expt_ } else { expt_ }).to_string()
  let elen = match ei {
    Some(ev) => if estr.length() > ev { estr.length() } else { ev }
    None => estr.length()
  }
  let mut add_zero_p = false
  if wi is Some(_) && overflowchar.truthy() && ei is Some(ev) && elen > ev {
    // Exponent overflow
    float__write_n(overflowchar, wi.unwrap(), stream)
  } else {
    let fdig = match di {
      Some(dv) => Some(if ki > 0 { 1 + (dv - ki) } else { dv })
      None => None
    }
    let mut spaceleft = match wi {
      Some(wv) =>
        wv -
        2 -
        elen -
        (if atp.truthy() || minusp(second(arg)) { 1 } else { 0 })
      None => 0
    }
    let scale = if k.truthy() { ki } else { 1 }
    let printprec = match fdig {
      Some(fd) => if fd == 0 { 1 } else { fd + scale }
      None => 0
    }
    let (fstr, flen, lpoint0, tpoint0) = float__bts_eg(arg, fdig, printprec, ki)
    let mut lpoint = lpoint0
    let mut tpoint = tpoint0
    if di is Some(0) {
      tpoint = false
    }
    if wi is Some(_) {
      spaceleft -= flen
      // See CLHS 22.3.3.2.  "If the parameter d is omitted, ... [and] if
      // the fraction to be printed is zero then a single zero digit should
      // appear after the decimal point."
      if di is None && fstr[flen - 1] == '.' {
        add_zero_p = true
        spaceleft -= 1
      }
      if lpoint {
        if spaceleft > 0 || tpoint {
          spaceleft -= 1
        } else {
          lpoint = false
        }
      }
      if tpoint && spaceleft <= 0 {
        tpoint = false
      }
    }
    if wi is Some(_) && spaceleft < 0 && overflowchar.truthy() {
      // Significand overflow; output the overflow char
      float__write_n(overflowchar, wi.unwrap(), stream)
    } else {
      if wi is Some(_) {
        float__write_n(padchar, spaceleft, stream)
      }
      if minusp(second(arg)) {
        write_char('-', stream~)
      } else if atp.truthy() {
        write_char('+', stream~)
      }
      if lpoint {
        write_char('0', stream~)
      }
      write_string(fstr, stream~)
      // Add a zero if we need it.
      if add_zero_p || (wi is None && fstr[flen - 1] == '.') {
        write_char('0', stream~)
      }
      if exponentchar.truthy() {
        float__write_c(exponentchar, stream)
      } else {
        write_char('b', stream~)
      }
      write_char(if expt_ < 0 { '-' } else { '+' }, stream~)
      match ei {
        Some(ev) =>
          for _ in 0..<(ev - estr.length()) {
            write_char('0', stream~)
          }
        None => ()
      }
      write_string(estr, stream~)
    }
  }
  Nil
}

///|
/// A modified version of FORMAT-FIXED-AUX from CMUCL to support printing
/// of bfloats.
fn bfloat_format_f(
  stream : Value,
  number : Value,
  colonp : Value,
  atsign : Value,
  w? : Value = Nil,
  d? : Value = Nil,
  k? : Value = Fix(0L),
  ovf? : Value = Nil,
  pad? : Value = Char(' '),
) -> Value raise {
  ignore(colonp)
  let wi = float__opt_int(w)
  let fdigits = float__opt_int(d)
  let ki = to_int(k)
  // Print the bfloat X with FDIGITS after the decimal point.  fpformat
  // always produces exponential output: with exponent E we need FDIGITS + E
  // digits printed.
  fn bfloat_to_string(
    x : Value,
    scale : Int,
    spaceleft : Int?,
  ) -> (String, Int, Bool, Bool) raise {
    let exp = ki + float__exponent_value(x)
    let printprec = match fdigits {
      Some(fd) => fd + exp + 1
      None =>
        match spaceleft {
          Some(sl) => if sl - 1 > 1 + exp { sl - 1 } else { 1 + exp }
          None => if 1 + exp > 0 { 1 + exp } else { 0 }
        }
    }
    with_special(q_d_fpprintprec, int(printprec), () => {
      let f = with_special(q_d_bftrunc, Nil, () => fpformat(
        bcons(fpabs(cdr(x))),
      ))
      let marker = position(q_b, f)
      let mut digits = remove(q_op_dot, subseq(f, 0, end=marker))
      // Figure out where the decimal point should go.  An exponent of 0
      // means the decimal is after the first digit.
      if exp < 0 {
        for _ in 0..<((if exp < 0 { -exp } else { exp }) - 1) {
          digits = cons(q_n0, digits)
        }
        digits = cons(q_op_dot, digits)
      } else if exp < length(digits) {
        digits = append_n([
          subseq(digits, 0, end=1 + exp),
          list1(q_op_dot),
          subseq(digits, 1 + exp),
        ])
      } else {
        digits = append(digits, list1(q_op_dot))
      }
      let mut str = float__concat(digits)
      let mut len = str.length()
      match fdigits {
        Some(fd) if fd >= len => {
          // Append some zeroes to get the desired number of digits
          str = str + float__zeros(1 + scale + (fd - len))
          len = str.length()
        }
        _ => ()
      }
      (str, len, str[0] == '.', str[str.length() - 1] == '.')
    })
  }

  let mut spaceleft = wi
  if wi is Some(wv) && (atsign.truthy() || minusp(second(number))) {
    spaceleft = Some(wv - 1)
  }
  let (str, len, lpoint0, tpoint0) = bfloat_to_string(number, ki, spaceleft)
  let mut lpoint = lpoint0
  let mut tpoint = tpoint0
  // if caller specifically requested no fraction digits, suppress the
  // optional trailing zero
  if fdigits is Some(0) {
    tpoint = false
  }
  let mut sl = match spaceleft {
    Some(s) => s
    None => 0
  }
  if wi is Some(_) {
    sl -= len
    // optional leading zero
    if lpoint {
      if sl > 0 || tpoint {
        // force at least one digit
        sl -= 1
      } else {
        lpoint = false
      }
    }
    // optional trailing zero
    if tpoint {
      if sl > 0 {
        sl -= 1
      } else {
        tpoint = false
      }
    }
  }
  if wi is Some(wv) && sl < 0 && ovf.truthy() {
    // field width overflow
    float__write_n(ovf, wv, stream)
    t
  } else {
    if wi is Some(_) {
      float__write_n(pad, sl, stream)
    }
    if minusp(second(number)) {
      write_char('-', stream~)
    } else if atsign.truthy() {
      write_char('+', stream~)
    }
    if lpoint {
      write_char('0', stream~)
    }
    write_string(str, stream~)
    if tpoint {
      write_char('0', stream~)
    }
    Nil
  }
}

///|
/// A modified version of FORMAT-EXP-AUX from CMUCL to support printing of
/// bfloats.
fn bfloat_format_g(
  stream : Value,
  arg : Value,
  colonp : Value,
  atsign : Value,
  w? : Value = Nil,
  d? : Value = Nil,
  e? : Value = Nil,
  k? : Value = Fix(1L),
  ovf? : Value = Nil,
  pad? : Value = Char(' '),
  exponentchar? : Value = Nil,
) -> Value raise {
  ignore(colonp)
  let ki = to_int(k)
  let n = 1 + float__exponent_value(arg)
  let orig_d = d
  // Default d if omitted, as in CLHS 22.3.3.3.
  let dv = match float__opt_int(d) {
    Some(dv) => dv
    None => {
      let (_, len, _, _) = float__bts_eg(arg, None, 0, ki)
      let q = len - 1
      let m = if n < 7 { n } else { 7 }
      if q > m {
        q
      } else {
        m
      }
    }
  }
  let ee = match float__opt_int(e) {
    Some(ev) => ev + 2
    None => 4
  }
  let ww = match float__opt_int(w) {
    Some(wv) => int(wv - ee)
    None => Nil
  }
  let dd = dv - n
  if 0 <= dd && dd <= dv {
    // Use dd fraction digits, even if that would cause the width to be
    // exceeded.  We choose accuracy over width in this case.
    let fill_char = if bfloat_format_f(
        stream,
        arg,
        Nil,
        atsign,
        w=ww,
        d=int(dd),
        k=Fix(0L),
        ovf~,
        pad~,
      ).truthy() {
      ovf
    } else {
      Char(' ')
    }
    float__write_n(fill_char, ee, stream)
    Nil
  } else {
    bfloat_format_e(
      stream,
      arg,
      Nil,
      atsign,
      w~,
      d=orig_d,
      e~,
      k=if k.truthy() { k } else { Fix(1L) },
      overflowchar=ovf,
      padchar=pad,
      exponentchar~,
    )
  }
}

///|
fn bigfloat2rat(x0 : Value) -> Value raise {
  let x = bigfloatp(x0)
  with_special(q_d_float2bf, t, () => {
    let mut sign = false
    let exp = if minusp(cadr(x)) {
      sign = true
      let y = fpration1(cons(car(x), fpabs(cdr(x))))
      rplaca(y, num_mul(Fix(-1L), car(y)))
    } else {
      fpration1(x)
    }
    if symval(q_d_ratprint).truthy() {
      let sign_str : Value = Str(if sign { "-" } else { "" })
      mtell(
        list([
          Str("~&rat: replaced ~A~A by"),
          sign_str,
          maknam(fpformat(cons(car(x), fpabs(cdr(x))))),
        ]),
      )
      |> ignore
      let x = d_bfloat(mk_simp(q_rat, [car(exp), cdr(exp)]))
      mtell(
        list([
          Str(" ~A/~A = ~A~A~%"),
          car(exp),
          cdr(exp),
          sign_str,
          maknam(fpformat(cons(car(x), fpabs(cdr(x))))),
        ]),
      )
      |> ignore
    }
    exp
  })
}

///|
fn fpration1(x : Value) -> Value raise {
  let fprateps = cdr(
    d_bfloat(
      if symval(q_d_bftorat).truthy() {
        mk_simp(q_rat, [
          Fix(1L),
          exptrl(Fix(2L), one_minus(float__prec())),
        ])
      } else {
        symval(q_d_ratepsilon)
      },
    ),
  )
  if equal(x, symval(q_ear_bigfloatzero)) {
    return cons(Fix(0L), Fix(1L))
  }
  let mut xx = x
  let mut a = fpentier(x)
  let mut num = a
  let mut den : Value = Fix(1L)
  let mut onum : Value = Fix(1L)
  let mut oden : Value = Fix(0L)
  while true {
    if !zerop(den) &&
      !fpgreaterp(
        fpabs(
          fpquotient(
            fpdifference(
              cdr(x),
              fpquotient(cdr(d_bfloat(num)), cdr(d_bfloat(den))),
            ),
            cdr(x),
          ),
        ),
        fprateps,
      ).truthy() {
      return cons(num, den)
    }
    let y = invertbigfloat(bcons(fpdifference(cdr(xx), cdr(d_bfloat(a)))))
    a = fpentier(y)
    let new_num = num_add(num_mul(a, num), onum)
    let new_den = num_add(num_mul(a, den), oden)
    onum = num
    oden = den
    num = new_num
    den = new_den
    xx = y
  }
  Nil
}
