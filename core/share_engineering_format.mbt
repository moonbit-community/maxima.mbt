// Port of share/contrib/engineering-format.lisp (Robert Dodier, 2014):
// display floats with an exponent which is a multiple of 3.

///|
/// CL `(format nil "~,d,,ke" x)` as SBCL prints it, for a nonzero double x:
/// k digits before the decimal point and d-k+1 after it, exponent marker
/// `e` and a signed exponent. A rounding carry lengthens the integer part
/// (SBCL prints 999.9 with d=2, k=3 as "1000.e+0").
fn share_engineering_format__format_e(x : Double, d : Int, k : Int) -> String {
  let sign = if x < 0.0 { "-" } else { "" }
  // x = 0.DIGITS * 10^e
  let (digits, e) = float_digits(x.abs())
  let nfrac = (d - k + 1).max(0)
  let n = k + nfrac
  // Round the digit string to n significant digits.
  let ds = if digits.length() <= n {
    digits + "0".repeat(n - digits.length())
  } else {
    let head = digits.substring(end=n)
    if digits[n] >= '5' {
      let bytes = head.to_array()
      let mut i = n - 1
      let mut carry = true
      while carry && i >= 0 {
        if bytes[i] == '9' {
          bytes[i] = '0'
          i -= 1
        } else {
          bytes[i] = (bytes[i].to_int() + 1).unsafe_to_char()
          carry = false
        }
      }
      let s = String::from_array(bytes)
      if carry {
        "1" + s
      } else {
        s
      }
    } else {
      head
    }
  }
  let ilen = ds.length() - nfrac
  let ip = ds.substring(end=ilen)
  let fp = ds.substring(start=ilen)
  let ex = e - k
  sign +
  ip +
  "." +
  fp +
  "e" +
  (if ex < 0 { "-" } else { "+" }) +
  ex.abs().to_string()
}

///|
fn engineering_format(x : Value) -> Value raise {
  let xd = to_double(x)
  if xd == 0.0 {
    return format(Nil, "~e", [x])
  }
  if xd < 0.0 {
    raise LispError::SimpleError(
      "engineering-format: the logarithm of a negative number is complex",
    )
  }
  // log10: (floor (log x 10.0)), with 10.0 a single float; adjust n when
  // rounding errors made it too small.
  let log10 = fn(x : Double) -> Int {
    let ln10 = Float::from_double(@math.ln(10.0)).to_double()
    let mut integer_log = (@math.ln(x) / ln10).floor().to_int()
    if !(@math.pow(10.0, integer_log.to_double()) <= x &&
      x < @math.pow(10.0, (integer_log + 1).to_double())) {
      integer_log += 1
    }
    integer_log
  }
  let integer_log = log10(xd)
  let scale = 1 + (integer_log % 3 + 3) % 3
  let fpprintprec = symval(q_d_fpprintprec)
  let effective_fpprintprec = if num_eq(fpprintprec, Fix(0L)) {
    16
  } else {
    to_int(fpprintprec)
  }
  let digits = effective_fpprintprec - 1
  let mut result = share_engineering_format__format_e(xd, digits, scale)
  let debug = symval(q_ear_debug_eng_format).truthy()
  // Check that the printed result does what we want. This accounts for
  // some roundoff in lisp's format function.
  let maybe_fix_up_result = fn() raise {
    let dot_posn = match result.find(".") {
      Some(i) => i
      None => 0
    }
    let epos = match result.find("e") {
      Some(i) => i
      None => result.length() - 1
    }
    let es = result.substring(start=epos + 1)
    let expo = match parse_integer(es) {
      Some(v) => to_int(v)
      None => raise LispError::SimpleError("parse-integer: junk in string \{es}")
    }
    if !(dot_posn < 4 && expo % 3 == 0) {
      if debug {
        format(t, "Expo ~A posn ~A: Result is wrong:  ~A~%", [
          int(expo),
          int(dot_posn),
          Str(result),
        ])
        |> ignore
      }
      result = share_engineering_format__format_e(xd, digits, scale - 1)
      if debug {
        format(t, "New result: ~A~%", [Str(result)]) |> ignore
      }
    }
  }
  if debug {
    format(t, "X = ~A log = ~A scale = ~A digits ~A result ~A~%", [
      x,
      int(integer_log),
      int(scale),
      int(digits),
      Str(result),
    ])
    |> ignore
  }
  maybe_fix_up_result()
  Str(result)
}

///|
fn init_share_engineering_format() -> Unit raise {
  // (let ((foo (symbol-function 'exploden))) (defun exploden (x) ...))
  let foo = commac__exploden_cell.val
  commac__exploden_cell.val = x => if floatp(x) &&
    symval(q_d_engineering_format_floats).truthy() &&
    (
      num_lt(num_abs(x), symval(q_d_engineering_format_min)) ||
      num_gt(num_abs(x), symval(q_d_engineering_format_max))
    ) {
    let s = engineering_format(x)
    let s1 = if symval(q_ear_exploden_strip_float_zeros).truthy() {
      let v = strip_float_zeros(s)
      if v.truthy() {
        v
      } else {
        s
      }
    } else {
      s
    }
    foo(s1)
  } else {
    foo(x)
  }
}
