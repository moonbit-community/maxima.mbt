// A subset of CL `format`, sufficient for Maxima's internal uses.
// Maxima's own `~M` directives are handled by MFORMAT in the core package;
// here an optional hook lets callers extend directive handling.

///|
priv struct FmtState {
  ctl : Array[Char]
  mut i : Int
  args : Array[Value]
  mut ai : Int
  out : StringBuilder
  hook : ((Char, Bool, Bool, Array[Value?], Value, StringBuilder) -> Bool raise)?
}

///|
fn FmtState::next_arg(self : FmtState) -> Value raise LispError {
  if self.ai >= self.args.length() {
    raise SimpleError("format: not enough arguments")
  }
  let v = self.args[self.ai]
  self.ai += 1
  v
}

///|
/// `(format nil ctl args...)`
pub fn format_to_string(
  ctl : String,
  args : Array[Value],
  hook? : (Char, Bool, Bool, Array[Value?], Value, StringBuilder) -> Bool raise,
) -> String raise {
  let st = {
    ctl: string_chars(ctl),
    i: 0,
    args,
    ai: 0,
    out: StringBuilder::new(),
    hook,
  }
  fmt_run(st, st.ctl.length()) |> ignore
  st.out.to_string()
}

///|
/// `(format dest ctl args...)`; dest nil returns a string, otherwise writes
/// to the stream (t = standard output) and returns nil.
pub fn format(dest : Value, ctl : String, args : Array[Value]) -> Value raise {
  let s = format_to_string(ctl, args)
  match dest {
    Nil => Str(s)
    Sym(_) => {
      write_string(s)
      Nil
    }
    Vec(_) => {
      for c in s {
        vector_push_extend(Char(c), dest) |> ignore
      }
      Nil
    }
    _ => {
      write_string(s, stream=dest)
      Nil
    }
  }
}

///|
/// Find the matching close directive (`~}` / `~]` / `~>`) at nesting level 0
/// starting at index i. Returns the index of the `~` of the closer and the
/// list of `~;` separator positions.
fn fmt_find_close(
  ctl : Array[Char],
  start : Int,
  close : Char,
) -> (Int, Array[(Int, Bool)]) raise LispError {
  let seps = []
  let mut depth = 0
  let mut i = start
  while i < ctl.length() {
    if ctl[i] == '~' {
      let mut j = i + 1
      let mut colon = false
      // skip params and modifiers
      while j < ctl.length() &&
            (ctl[j].is_ascii_digit() || ctl[j] == ',' || ctl[j] == '\'' ||
            ctl[j] == ':' || ctl[j] == '@' || ctl[j] == 'v' || ctl[j] == 'V' ||
            ctl[j] == '#' || ctl[j] == '-' || ctl[j] == '+') {
        if ctl[j] == '\'' {
          j += 1
        }
        if ctl[j] == ':' {
          colon = true
        }
        j += 1
      }
      if j >= ctl.length() {
        break
      }
      let d = ctl[j]
      if d == '{' || d == '[' || d == '<' || d == '(' {
        depth += 1
      } else if d == '}' || d == ']' || d == '>' || d == ')' {
        if depth == 0 && d == close {
          return (i, seps)
        }
        depth -= 1
      } else if d == ';' && depth == 0 {
        seps.push((i, colon))
      }
      i = j + 1
    } else {
      i += 1
    }
  }
  raise SimpleError("format: unmatched directive")
}

///|
/// Skip past a directive starting at `~` index i; returns index after it.
fn fmt_directive_end(ctl : Array[Char], i : Int) -> Int {
  let mut j = i + 1
  while j < ctl.length() &&
        (ctl[j].is_ascii_digit() || ctl[j] == ',' || ctl[j] == '\'' ||
        ctl[j] == ':' || ctl[j] == '@' || ctl[j] == 'v' || ctl[j] == 'V' ||
        ctl[j] == '#' || ctl[j] == '-' || ctl[j] == '+') {
    if ctl[j] == '\'' {
      j += 1
    }
    j += 1
  }
  j + 1
}

///|
priv suberror FmtEscape {
  FmtUpAndOut
}

///|
/// Run directives from st.i up to `end`. Returns false if `~^` escaped.
fn fmt_run(st : FmtState, end : Int) -> Bool raise {
  while st.i < end {
    let c = st.ctl[st.i]
    if c != '~' {
      st.out.write_char(c)
      st.i += 1
      continue
    }
    st.i += 1
    // parameters
    let params : Array[Value?] = []
    let mut colon = false
    let mut at = false
    while st.i < end {
      let ch = st.ctl[st.i]
      if ch.is_ascii_digit() || ch == '-' || ch == '+' {
        let sb = StringBuilder::new()
        sb.write_char(ch)
        st.i += 1
        while st.i < end && st.ctl[st.i].is_ascii_digit() {
          sb.write_char(st.ctl[st.i])
          st.i += 1
        }
        params.push(parse_integer(sb.to_string()))
      } else if ch == '\'' {
        params.push(Some(Char(st.ctl[st.i + 1])))
        st.i += 2
      } else if ch == 'v' || ch == 'V' {
        let a = st.next_arg()
        params.push(if a is Nil { None } else { Some(a) })
        st.i += 1
      } else if ch == '#' {
        params.push(Some(int(st.args.length() - st.ai)))
        st.i += 1
      } else if ch == ',' {
        if params.length() == 0 || st.ctl[st.i - 1] == ',' {
          params.push(None)
        }
        st.i += 1
        continue
      } else if ch == ':' {
        colon = true
        st.i += 1
      } else if ch == '@' {
        at = true
        st.i += 1
      } else {
        break
      }
    }
    let d = st.ctl[st.i]
    st.i += 1
    let dl = char_downcase(d)
    // custom hook (e.g. Maxima's ~M)
    match st.hook {
      Some(h) =>
        if dl == 'm' {
          let arg = st.next_arg()
          if h(d, colon, at, params, arg, st.out) {
            continue
          }
        }
      None => ()
    }
    let p0 = params.get(0).unwrap_or(None)
    match dl {
      'a' | 's' => {
        let arg = st.next_arg()
        let s = if dl == 'a' {
          if colon && arg is Nil {
            "()"
          } else {
            princ_to_string(arg)
          }
        } else {
          prin1_to_string(arg)
        }
        let w = match p0 {
          Some(Fix(n)) => n.to_int()
          _ => 0
        }
        if at {
          st.out.write_string(" ".repeat((w - string_length(s)).max(0)))
        }
        st.out.write_string(s)
        if !at {
          st.out.write_string(" ".repeat((w - string_length(s)).max(0)))
        }
      }
      'd' | 'b' | 'o' | 'x' => {
        let arg = st.next_arg()
        let radix = match dl {
          'b' => 2
          'o' => 8
          'x' => 16
          _ => 10
        }
        let s = if integerp(arg) {
          let b = to_big(arg)
          let mut s = b.to_string(radix~)
          if colon {
            s = group_digits(s)
          }
          if at && !(b < 0N) {
            "+" + s
          } else {
            s
          }
        } else {
          // As SBCL: a non-integer argument is printed as by ~A, unpadded.
          st.out.write_string(princ_to_string(arg))
          continue
        }
        let w = match p0 {
          Some(Fix(n)) => n.to_int()
          _ => 0
        }
        let pad = match params.get(1).unwrap_or(None) {
          Some(Char(pc)) => pc.to_string()
          _ => " "
        }
        st.out.write_string(pad.repeat((w - s.length()).max(0)))
        st.out.write_string(s)
      }
      'r' => {
        let arg = st.next_arg()
        match p0 {
          Some(Fix(radix)) =>
            st.out.write_string(to_big(arg).to_string(radix=radix.to_int()))
          _ =>
            if at {
              st.out.write_string(roman(to_int(arg)))
            } else if colon {
              st.out.write_string(ordinal_english(to_int(arg)))
            } else {
              st.out.write_string(cardinal_english(to_big(arg)))
            }
        }
      }
      'c' => {
        let arg = st.next_arg()
        match arg {
          Char(ch) => st.out.write_char(ch)
          _ => st.out.write_string(princ_to_string(arg))
        }
      }
      'f' => {
        let arg = st.next_arg()
        let w = match p0 {
          Some(Fix(n)) => Some(n.to_int())
          _ => None
        }
        let dd = match params.get(1).unwrap_or(None) {
          Some(Fix(n)) => Some(n.to_int())
          _ => None
        }
        let s = if realp(arg) {
          format_fixed(to_double(arg), w, dd, at)
        } else {
          princ_to_string(arg)
        }
        match w {
          Some(wn) => st.out.write_string(" ".repeat((wn - s.length()).max(0)))
          None => ()
        }
        st.out.write_string(s)
      }
      'e' | 'g' => {
        let arg = st.next_arg()
        let dd = match params.get(1).unwrap_or(None) {
          Some(Fix(n)) => Some(n.to_int())
          _ => None
        }
        let s = if realp(arg) {
          format_exp(to_double(arg), dd)
        } else {
          princ_to_string(arg)
        }
        let w = match p0 {
          Some(Fix(n)) => n.to_int()
          _ => 0
        }
        st.out.write_string(" ".repeat((w - s.length()).max(0)))
        st.out.write_string(s)
      }
      '$' => {
        let arg = st.next_arg()
        let dd = match p0 {
          Some(Fix(n)) => Some(n.to_int())
          _ => Some(2)
        }
        st.out.write_string(format_fixed(to_double(arg), None, dd, at))
      }
      '%' => {
        let n = match p0 {
          Some(Fix(n)) => n.to_int()
          _ => 1
        }
        for _ in 0..<n {
          st.out.write_char('\n')
        }
      }
      '&' => {
        let s = st.out.to_string()
        if s.length() > 0 && !s.has_suffix("\n") {
          st.out.write_char('\n')
        }
      }
      '~' => st.out.write_char('~')
      '|' => st.out.write_char('\u{0C}')
      't' => {
        let n = match p0 {
          Some(Fix(n)) => n.to_int()
          _ => 1
        }
        st.out.write_string(" ".repeat(n.max(1)))
      }
      '\n' => {
        // skip following whitespace
        while st.i < end && (st.ctl[st.i] == ' ' || st.ctl[st.i] == '\t') {
          st.i += 1
        }
      }
      'p' => {
        let arg = if colon { st.args[st.ai - 1] } else { st.next_arg() }
        let plural = !(arg is Fix(1L))
        if at {
          st.out.write_string(if plural { "ies" } else { "y" })
        } else if plural {
          st.out.write_char('s')
        }
      }
      '*' => {
        let n = match p0 {
          Some(Fix(n)) => n.to_int()
          _ => 1
        }
        if colon {
          st.ai = (st.ai - n).max(0)
        } else if at {
          st.ai = n
        } else {
          st.ai += n
        }
      }
      '?' => {
        let sub = lstring(st.next_arg())
        if at {
          let st2 = {
            ctl: string_chars(sub),
            i: 0,
            args: st.args,
            ai: st.ai,
            out: st.out,
            hook: st.hook,
          }
          fmt_run(st2, st2.ctl.length()) |> ignore
          st.ai = st2.ai
        } else {
          let subargs = list_to_array(st.next_arg())
          st.out.write_string(format_to_string(sub, subargs, hook?=st.hook))
        }
      }
      '^' =>
        if st.ai >= st.args.length() {
          raise FmtUpAndOut
        }
      '(' => {
        let (close, _) = fmt_find_close(st.ctl, st.i, ')')
        let sub = StringBuilder::new()
        let st2 = {
          ctl: st.ctl,
          i: st.i,
          args: st.args,
          ai: st.ai,
          out: sub,
          hook: st.hook,
        }
        fmt_run(st2, close) |> ignore
        st.ai = st2.ai
        let s = sub.to_string()
        let r = if colon && at {
          string_upcase(s)
        } else if colon {
          capitalize_words(s)
        } else if at {
          let low = string_downcase(s)
          if low.length() > 0 {
            string_upcase(low.substring(end=1)) + low.substring(start=1)
          } else {
            low
          }
        } else {
          string_downcase(s)
        }
        st.out.write_string(r)
        st.i = fmt_directive_end(st.ctl, close)
      }
      '[' => {
        let (close, seps) = fmt_find_close(st.ctl, st.i, ']')
        // clause boundaries
        let starts = [st.i]
        let ends = []
        let mut default_clause = -1
        for k, sp in seps {
          ends.push(sp.0)
          starts.push(fmt_directive_end(st.ctl, sp.0))
          if sp.1 {
            default_clause = k + 1
          }
        }
        ends.push(close)
        let after = fmt_directive_end(st.ctl, close)
        let chosen = if colon {
          let arg = st.next_arg()
          if arg is Nil {
            0
          } else {
            1
          }
        } else if at {
          let arg = st.args[st.ai]
          if arg is Nil {
            st.ai += 1
            -1
          } else {
            0
          }
        } else {
          let n = match p0 {
            Some(Fix(n)) => n.to_int()
            _ => to_int(st.next_arg())
          }
          if n >= 0 && n < starts.length() &&
            !(default_clause >= 0 && n >= default_clause) {
            n
          } else if default_clause >= 0 {
            default_clause
          } else {
            -1
          }
        }
        if chosen >= 0 && chosen < starts.length() {
          st.i = starts[chosen]
          fmt_run(st, ends[chosen]) |> ignore
        }
        st.i = after
      }
      '{' => {
        let (close, _) = fmt_find_close(st.ctl, st.i, '}')
        let body_start = st.i
        let after = fmt_directive_end(st.ctl, close)
        let close_colon = {
          // ~:} forces at least one iteration
          let mut j = close + 1
          let mut cc = false
          while j < st.ctl.length() && st.ctl[j] != '}' {
            if st.ctl[j] == ':' {
              cc = true
            }
            j += 1
          }
          cc
        }
        let body_empty = close == body_start
        let body_ctl = if body_empty {
          string_chars(lstring(st.next_arg()))
        } else {
          st.ctl
        }
        let (bs, be) = if body_empty {
          (0, body_ctl.length())
        } else {
          (body_start, close)
        }
        let max_iter = match p0 {
          Some(Fix(n)) => n.to_int()
          _ => 1000000
        }
        if at {
          // iterate over remaining args
          let mut count = 0
          while (st.ai < st.args.length() || (close_colon && count == 0)) &&
                count < max_iter {
            let st2 = {
              ctl: body_ctl,
              i: bs,
              args: st.args,
              ai: st.ai,
              out: st.out,
              hook: st.hook,
            }
            let ok = fmt_run(st2, be) catch {
              FmtUpAndOut => false
              e => raise e
            }
            st.ai = st2.ai
            count += 1
            if !ok {
              break
            }
          }
        } else {
          let arg = st.next_arg()
          let items = list_to_array(arg)
          if colon {
            // each element is an argument list
            for k, item in items {
              if k >= max_iter {
                break
              }
              let st2 = {
                ctl: body_ctl,
                i: bs,
                args: list_to_array(item),
                ai: 0,
                out: st.out,
                hook: st.hook,
              }
              let ok = fmt_run(st2, be) catch {
                FmtUpAndOut => false
                e => raise e
              }
              if !ok && k == items.length() - 1 {
                break
              }
            }
          } else {
            let st2 = {
              ctl: body_ctl,
              i: bs,
              args: items,
              ai: 0,
              out: st.out,
              hook: st.hook,
            }
            let mut count = 0
            while (st2.ai < items.length() || (close_colon && count == 0)) &&
                  count < max_iter {
              st2.i = bs
              let ok = fmt_run(st2, be) catch {
                FmtUpAndOut => false
                e => raise e
              }
              count += 1
              if !ok {
                break
              }
            }
          }
        }
        st.i = after
      }
      '<' => {
        // justification: just output the segments concatenated
        let (close, _) = fmt_find_close(st.ctl, st.i, '>')
        let sub = StringBuilder::new()
        let st2 = {
          ctl: st.ctl,
          i: st.i,
          args: st.args,
          ai: st.ai,
          out: sub,
          hook: st.hook,
        }
        fmt_run(st2, close) |> ignore
        st.ai = st2.ai
        let s = sub.to_string()
        let w = match p0 {
          Some(Fix(n)) => n.to_int()
          _ => 0
        }
        st.out.write_string(" ".repeat((w - s.length()).max(0)))
        st.out.write_string(s)
        st.i = fmt_directive_end(st.ctl, close)
      }
      ';' => ()
      _ => {
        // unknown: echo it
        st.out.write_char('~')
        st.out.write_char(d)
      }
    }
  }
  true
}

///|
fn group_digits(s : String) -> String {
  let neg = s.has_prefix("-")
  let digits = if neg { s.substring(start=1) } else { s }
  let sb = StringBuilder::new()
  let n = digits.length()
  for i in 0..<n {
    if i > 0 && (n - i) % 3 == 0 {
      sb.write_char(',')
    }
    sb.write_char(digits[i].to_int().unsafe_to_char())
  }
  (if neg { "-" } else { "" }) + sb.to_string()
}

///|
fn capitalize_words(s : String) -> String {
  let sb = StringBuilder::new()
  let mut start = true
  for c in s {
    if alphanumericp(c) {
      sb.write_char(if start { char_upcase(c) } else { char_downcase(c) })
      start = false
    } else {
      sb.write_char(c)
      start = true
    }
  }
  sb.to_string()
}

///|
/// Fixed-point float formatting (`~w,dF`).
pub fn format_fixed(x : Double, w : Int?, d : Int?, plus : Bool) -> String {
  let sign = if x < 0.0 || dsignbit(x) && x == 0.0 {
    "-"
  } else if plus {
    "+"
  } else {
    ""
  }
  let a = x.abs()
  match d {
    Some(dn) => {
      // round to dn decimals using exact rational arithmetic
      let digits = (fn() -> String raise {
        let r = double_to_rational(a)
        let scale = BigInt::from_int(10).pow(BigInt::from_int(dn))
        let scaled = num_round(num_mul(r, from_big(scale))).0
        to_big(scaled).to_string()
      })() catch {
        _ => "0"
      }
      let padded = if digits.length() <= dn {
        "0".repeat(dn - digits.length() + 1) + digits
      } else {
        digits
      }
      let ip = padded.substring(end=padded.length() - dn)
      let fp = padded.substring(start=padded.length() - dn)
      sign + ip + "." + fp
    }
    None => {
      let s = float_to_string(a)
      if s.contains("e") {
        // expand exponent form into fixed
        let (digits, e) = float_digits(a)
        let body = if e <= 0 {
          "0." + "0".repeat(-e) + digits
        } else if e >= digits.length() {
          digits + "0".repeat(e - digits.length()) + ".0"
        } else {
          digits.substring(end=e) + "." + digits.substring(start=e)
        }
        ignore(w)
        sign + body
      } else {
        sign + s
      }
    }
  }
}

///|
/// Exponential float formatting (`~,dE`).
pub fn format_exp(x : Double, d : Int?) -> String {
  if x == 0.0 {
    return "0.0e+0"
  }
  let sign = if x < 0.0 { "-" } else { "" }
  let (digits, e) = float_digits(x.abs())
  let mant = match d {
    Some(dn) => {
      let ds = if digits.length() > dn + 1 {
        digits.substring(end=dn + 1)
      } else {
        digits + "0".repeat(dn + 1 - digits.length())
      }
      ds.substring(end=1) + "." + ds.substring(start=1)
    }
    None =>
      digits.substring(end=1) +
      "." +
      (if digits.length() > 1 { digits.substring(start=1) } else { "0" })
  }
  let ex = e - 1
  sign + mant + "e" + (if ex >= 0 { "+" } else { "-" }) + ex.abs().to_string()
}

///|
fn roman(n : Int) -> String {
  let vals = [1000, 900, 500, 400, 100, 90, 50, 40, 10, 9, 5, 4, 1]
  let syms = ["M", "CM", "D", "CD", "C", "XC", "L", "XL", "X", "IX", "V", "IV", "I"]
  let sb = StringBuilder::new()
  let mut m = n
  for i, v in vals {
    while m >= v {
      sb.write_string(syms[i])
      m -= v
    }
  }
  sb.to_string()
}

///|
let small_names : Array[String] = [
  "zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
  "ten", "eleven", "twelve", "thirteen", "fourteen", "fifteen", "sixteen", "seventeen",
  "eighteen", "nineteen",
]

///|
let tens_names : Array[String] = [
  "", "", "twenty", "thirty", "forty", "fifty", "sixty", "seventy", "eighty", "ninety",
]

///|
fn cardinal_small(n : Int) -> String {
  if n < 20 {
    small_names[n]
  } else if n < 100 {
    let t = tens_names[n / 10]
    if n % 10 == 0 {
      t
    } else {
      t + "-" + small_names[n % 10]
    }
  } else {
    let h = small_names[n / 100] + " hundred"
    if n % 100 == 0 {
      h
    } else {
      h + " " + cardinal_small(n % 100)
    }
  }
}

///|
fn cardinal_english(n : BigInt) -> String {
  if n < 0N {
    return "negative " + cardinal_english(-n)
  }
  if n.is_zero() {
    return "zero"
  }
  let scales = [
    "", " thousand", " million", " billion", " trillion", " quadrillion", " quintillion",
    " sextillion", " septillion", " octillion", " nonillion", " decillion",
  ]
  let parts = []
  let mut m = n
  let mut k = 0
  let thousand = BigInt::from_int(1000)
  while !m.is_zero() {
    let chunk = (m % thousand).to_int()
    if chunk != 0 {
      let sc = if k < scales.length() { scales[k] } else { "" }
      parts.push(cardinal_small(chunk) + sc)
    }
    m = m / thousand
    k += 1
  }
  parts.rev_in_place()
  parts.join(" ")
}

///|
fn ordinal_english(n : Int) -> String {
  let c = cardinal_english(BigInt::from_int(n))
  if c.has_suffix("one") {
    c.substring(end=c.length() - 3) + "first"
  } else if c.has_suffix("two") {
    c.substring(end=c.length() - 3) + "second"
  } else if c.has_suffix("three") {
    c.substring(end=c.length() - 5) + "third"
  } else if c.has_suffix("five") {
    c.substring(end=c.length() - 4) + "fifth"
  } else if c.has_suffix("eight") {
    c + "h"
  } else if c.has_suffix("nine") {
    c.substring(end=c.length() - 1) + "th"
  } else if c.has_suffix("twelve") {
    c.substring(end=c.length() - 2) + "fth"
  } else if c.has_suffix("y") {
    c.substring(end=c.length() - 1) + "ieth"
  } else {
    c + "th"
  }
}
