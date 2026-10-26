// Port of src/pregexp.lisp: portable regular expressions for Common Lisp
// (Dorai Sitaram).
//
// Parse trees are Lisp data as in the original: keywords, characters and
// lists such as (:sub (:or (:seq #\a (:between nil 0 nil :any)))).
//
// The declared functions take Lisp strings and fixnum positions.  The
// reader and the matcher work internally on the string's characters
// (`Array[Char]`, code-point indexed like a Lisp string) and MoonBit
// integers; the declared entry points convert.  The continuation-passing
// matcher of PREGEXP-MATCH-POSITIONS-AUX keeps its structure: success
// continuations take the new position, failure continuations take nothing,
// and both return a Lisp value (NIL meaning failure).

///|
let pregexp__k_or : Value = kw("or")

///|
let pregexp__k_seq : Value = kw("seq")

///|
let pregexp__k_bos : Value = kw("bos")

///|
let pregexp__k_eos : Value = kw("eos")

///|
let pregexp__k_any : Value = kw("any")

///|
let pregexp__k_super_any : Value = kw("super-any")

///|
let pregexp__k_neg_char : Value = kw("neg-char")

///|
let pregexp__k_backref : Value = kw("backref")

///|
let pregexp__k_empty : Value = kw("empty")

///|
let pregexp__k_wbdry : Value = kw("wbdry")

///|
let pregexp__k_not_wbdry : Value = kw("not-wbdry")

///|
let pregexp__k_digit : Value = kw("digit")

///|
let pregexp__k_space : Value = kw("space")

///|
let pregexp__k_word : Value = kw("word")

///|
let pregexp__k_lookahead : Value = kw("lookahead")

///|
let pregexp__k_neg_lookahead : Value = kw("neg-lookahead")

///|
let pregexp__k_no_backtrack : Value = kw("no-backtrack")

///|
let pregexp__k_lookbehind : Value = kw("lookbehind")

///|
let pregexp__k_neg_lookbehind : Value = kw("neg-lookbehind")

///|
let pregexp__k_case_sensitive : Value = kw("case-sensitive")

///|
let pregexp__k_case_insensitive : Value = kw("case-insensitive")

///|
let pregexp__k_sub : Value = kw("sub")

///|
let pregexp__k_between : Value = kw("between")

///|
let pregexp__k_char_range : Value = kw("char-range")

///|
let pregexp__k_one_of_chars : Value = kw("one-of-chars")

///|
fn pregexp__error(msg : String) -> LispError {
  LispError::SimpleError(msg)
}

///|
/// The characters of a Lisp string designator.
fn pregexp__chars(v : Value) -> Array[Char] raise {
  match v {
    Str(s) => string_chars(s)
    _ =>
      raise pregexp__error(
        "The value " + prin1_to_string(v) + " is not of type STRING",
      )
  }
}

///|
fn pregexp__int(v : Value) -> Int raise {
  match v {
    Fix(n) => n.to_int()
    _ =>
      raise pregexp__error(
        "The value " + prin1_to_string(v) + " is not of type FIXNUM",
      )
  }
}

///|
fn pregexp__lchar(v : Value) -> Char raise {
  match v {
    Char(c) => c
    _ =>
      raise pregexp__error(
        "The value " + prin1_to_string(v) + " is not of type CHARACTER",
      )
  }
}

///|
/// (char s i)
fn pregexp__char(s : Array[Char], i : Int) -> Char raise {
  if i < 0 || i >= s.length() {
    raise pregexp__error(
      "Invalid index \{i} for (SIMPLE-ARRAY CHARACTER (\{s.length()})), should be a non-negative integer below \{s.length()}.",
    )
  }
  s[i]
}

///|
fn pregexp__space_sensitive_p() -> Bool {
  symval(q_ear_pregexp_space_sensitive_p).truthy()
}

///|
fn pregexp__set_space_sensitive_p(b : Bool) -> Unit {
  set(q_ear_pregexp_space_sensitive_p, lbool(b)) |> ignore
}

///|
fn pregexp__comment_char() -> Char {
  match symval(q_ear_pregexp_comment_char) {
    Char(c) => c
    _ => ';'
  }
}

///|
/// GRAPHIC-CHAR-P as in SBCL.
fn pregexp__graphic_char_p(c : Char) -> Bool {
  let n = c.to_int()
  (n > 31 && n < 127) || n > 159
}

///|
fn pregexp__whitespace(c : Char) -> Bool {
  c == ' ' || c == '\t' || !pregexp__graphic_char_p(c)
}

///|
fn pregexp__digit(c : Char) -> Bool {
  digit_char_p(c) is Some(_)
}

///|
/// READ-FROM-STRING of a string of decimal digits.
fn pregexp__digits_value(r : Array[Char]) -> Value {
  parse_integer(chars_to_string(r)).unwrap_or(Nil)
}

// ---------------------------------------------------------------------------
// Reading a pattern into a parse tree

///|
fn pregexp__read_pattern(s : Array[Char], i : Int, n : Int) -> (Value, Int) raise {
  if i >= n {
    return (list2(pregexp__k_or, list1(pregexp__k_seq)), i)
  }
  let mut i = i
  let mut branches : Value = Nil
  while true {
    if i >= n || pregexp__char(s, i) == ')' {
      return (cons(pregexp__k_or, nreverse(branches)), i)
    }
    let (branch1, i1) = pregexp__read_branch(
      s,
      if pregexp__char(s, i) == '|' {
        i + 1
      } else {
        i
      },
      n,
    )
    branches = cons(branch1, branches)
    i = i1
  }
  (Nil, i)
}

///|
fn pregexp__read_branch(s : Array[Char], i : Int, n : Int) -> (Value, Int) raise {
  let mut i = i
  let mut pieces : Value = Nil
  while true {
    if i >= n || pregexp__char(s, i) == '|' || pregexp__char(s, i) == ')' {
      return (cons(pregexp__k_seq, nreverse(pieces)), i)
    }
    let (pc, i_new) = pregexp__read_piece(s, i, n)
    pieces = cons(pc, pieces)
    i = i_new
  }
  (Nil, i)
}

///|
fn pregexp__read_piece(s : Array[Char], i : Int, n : Int) -> (Value, Int) raise {
  let c = pregexp__char(s, i)
  let mut i = i + 1
  match c {
    '^' => (pregexp__k_bos, i)
    '$' => (pregexp__k_eos, i)
    '.' => pregexp__wrap_quantifier_if_any(pregexp__k_any, s, i, n)
    '[' => {
      let mut negp = false
      if i < n && pregexp__char(s, i) == '^' {
        i += 1
        negp = true
      }
      if i < n {
        let (chars, i1) = pregexp__read_char_list(s, i, n)
        pregexp__wrap_quantifier_if_any(
          if negp {
            list2(pregexp__k_neg_char, chars)
          } else {
            chars
          },
          s,
          i1,
          n,
        )
      } else {
        // (when (< i n) ...) returns NIL (one value).
        (Nil, -1)
      }
    }
    '(' => {
      let (re, i1) = pregexp__read_subpattern(s, i, n)
      pregexp__wrap_quantifier_if_any(re, s, i1, n)
    }
    '\\' =>
      match pregexp__read_escaped_number(s, i, n) {
        Some((m, i1)) =>
          pregexp__wrap_quantifier_if_any(
            list2(pregexp__k_backref, m),
            s,
            i1,
            n,
          )
        None => {
          let (c, i1) = pregexp__read_escaped_char(s, i)
          if c.truthy() {
            pregexp__wrap_quantifier_if_any(c, s, i1, n)
          } else {
            raise pregexp__error("pregexp-read-piece: backslash")
          }
        }
      }
    _ =>
      if pregexp__space_sensitive_p() ||
        (!pregexp__whitespace(c) && c != pregexp__comment_char()) {
        pregexp__wrap_quantifier_if_any(Char(c), s, i, n)
      } else {
        let mut in_comment_p = false
        let mut c = c
        while true {
          if in_comment_p {
            if c == '\n' {
              in_comment_p = false
            }
          } else if pregexp__whitespace(c) {
            ()
          } else if c == pregexp__comment_char() {
            in_comment_p = true
          } else {
            i -= 1
            return (pregexp__k_empty, i)
          }
          if i >= n {
            return (pregexp__k_empty, i)
          }
          c = pregexp__char(s, i)
          i += 1
        }
        (Nil, i)
      }
  }
}

///|
fn pregexp__read_escaped_number(
  s : Array[Char],
  i : Int,
  n : Int,
) -> (Value, Int)? raise {
  let mut i = i
  let r : Array[Char] = []
  while i < n && pregexp__digit(pregexp__char(s, i)) {
    r.push(s[i])
    i += 1
  }
  if r.is_empty() {
    None
  } else {
    Some((pregexp__digits_value(r), i))
  }
}

///|
fn pregexp__read_escaped_char(s : Array[Char], i : Int) -> (Value, Int) raise {
  let c = pregexp__char(s, i)
  let v = match c {
    'b' => pregexp__k_wbdry
    'B' => pregexp__k_not_wbdry
    'd' => pregexp__k_digit
    'D' => list2(pregexp__k_neg_char, pregexp__k_digit)
    'n' => Char('\n')
    'r' => Char('\r')
    's' => pregexp__k_space
    'S' => list2(pregexp__k_neg_char, pregexp__k_space)
    't' => Char('\t')
    'w' => pregexp__k_word
    'W' => list2(pregexp__k_neg_char, pregexp__k_word)
    _ => Char(c)
  }
  (v, i + 1)
}

///|
fn pregexp__read_posix_char_class(
  s : Array[Char],
  i : Int,
  n : Int,
) -> (Value, Int) raise {
  let mut i = i
  let r : Array[Char] = []
  let mut negp = false
  while true {
    if i >= n {
      raise pregexp__error("pregexp-read-posix-char-class")
    }
    let c = pregexp__char(s, i)
    i += 1
    if c == '^' {
      negp = true
    } else if alpha_char_p(c) {
      r.push(c)
    } else if c == ':' {
      if i >= n || pregexp__char(s, i) != ']' {
        raise pregexp__error("pregexp-read-posix-char-class")
      }
      i += 1
      break
    } else {
      raise pregexp__error("pregexp-read-posix-char-class")
    }
  }
  // (intern (string-upcase name) :keyword), as a port name.
  let posix_class = kw(invert_case(string_upcase(chars_to_string(r))))
  (
    if negp {
      list2(pregexp__k_neg_char, posix_class)
    } else {
      posix_class
    },
    i,
  )
}

///|
fn pregexp__read_cluster_type(s : Array[Char], i : Int) -> (Value, Int) raise {
  let mut c = pregexp__char(s, i)
  let mut i = i + 1
  if c != '?' {
    i -= 1
    return (list1(pregexp__k_sub), i)
  }
  c = pregexp__char(s, i)
  i += 1
  match c {
    ':' => (Nil, i)
    '=' => (list1(pregexp__k_lookahead), i)
    '!' => (list1(pregexp__k_neg_lookahead), i)
    '>' => (list1(pregexp__k_no_backtrack), i)
    '<' => {
      c = pregexp__char(s, i)
      i += 1
      match c {
        '=' => (list1(pregexp__k_lookbehind), i)
        '!' => (list1(pregexp__k_neg_lookbehind), i)
        _ => raise pregexp__error("pregexp-read-cluster-type")
      }
    }
    _ => {
      let mut r : Value = Nil
      let mut invp = false
      while true {
        match c {
          '-' => invp = true
          'i' => {
            r = cons(
              if invp {
                pregexp__k_case_sensitive
              } else {
                pregexp__k_case_insensitive
              },
              r,
            )
            invp = false
          }
          'x' => {
            pregexp__set_space_sensitive_p(invp)
            invp = false
          }
          ':' => return (nreverse(r), i)
          _ => raise pregexp__error("pregexp-read-cluster-type")
        }
        c = pregexp__char(s, i)
        i += 1
      }
      (Nil, i)
    }
  }
}

///|
fn pregexp__read_subpattern(s : Array[Char], i : Int, n : Int) -> (Value, Int) raise {
  let remember_space_sensitive_p = symval(q_ear_pregexp_space_sensitive_p)
  let (ctyp, i1) = pregexp__read_cluster_type(s, i)
  let (re0, i2) = pregexp__read_pattern(s, i1, n)
  set(q_ear_pregexp_space_sensitive_p, remember_space_sensitive_p) |> ignore
  if i2 < n && pregexp__char(s, i2) == ')' {
    let mut re = re0
    for ct in ctyp.iter() {
      re = list2(ct, re)
    }
    (re, i2 + 1)
  } else {
    raise pregexp__error("pregexp-read-subpattern")
  }
}

///|
fn pregexp__wrap_quantifier_if_any(
  re : Value,
  s : Array[Char],
  i : Int,
  n : Int,
) -> (Value, Int) raise {
  let mut i = i
  while true {
    if i >= n {
      return (re, i)
    }
    let c = pregexp__char(s, i)
    i += 1
    if pregexp__whitespace(c) && !pregexp__space_sensitive_p() {
      continue
    }
    match c {
      '*' | '+' | '?' | '{' => {
        // (:between non-greedy at-least at-most re)
        let mut non_greedy : Value = Nil
        let (p, q) = match c {
          '*' => (Value::Fix(0L), Value::Nil)
          '+' => (Value::Fix(1L), Value::Nil)
          '?' => (Value::Fix(0L), Value::Fix(1L))
          _ => {
            let (p, q, i1) = pregexp__read_nums(s, i, n)
            i = i1
            (p, q)
          }
        }
        while true {
          if i >= n {
            break
          }
          let c = pregexp__char(s, i)
          i += 1
          if pregexp__whitespace(c) && !pregexp__space_sensitive_p() {
            continue
          } else if c == '?' {
            non_greedy = t
            break
          } else {
            i -= 1
            break
          }
        }
        return (list([pregexp__k_between, non_greedy, p, q, re]), i)
      }
      _ => {
        i -= 1
        return (re, i)
      }
    }
  }
  (re, i)
}

///|
fn pregexp__read_nums(s : Array[Char], i : Int, n : Int) -> (Value, Value, Int) raise {
  let mut i = i
  let p : Array[Char] = []
  let q : Array[Char] = []
  let mut reading = 1
  while true {
    if i >= n {
      raise pregexp__error("pregexp-read-nums: unmatched left brace")
    }
    let c = pregexp__char(s, i)
    if pregexp__digit(c) {
      if reading == 1 {
        p.push(c)
      } else {
        q.push(c)
      }
      i += 1
    } else if pregexp__whitespace(c) && !pregexp__space_sensitive_p() {
      i += 1
    } else if c == ',' && reading == 1 {
      i += 1
      reading += 1
    } else if c == '}' {
      i += 1
      let pv = pregexp__digits_value(p)
      let qv = pregexp__digits_value(q)
      return if pv is Nil && reading == 1 {
        (Fix(0L), Nil, i)
      } else if reading == 1 {
        (pv, pv, i)
      } else {
        (pv, qv, i)
      }
    } else {
      raise pregexp__error(
        "pregexp-read-nums: left brace must be followed by number",
      )
    }
  }
  (Nil, Nil, i)
}

///|
fn pregexp__read_char_list(s : Array[Char], i : Int, n : Int) -> (Value, Int) raise {
  let mut i = i
  let mut r : Value = Nil
  while true {
    if i >= n {
      raise pregexp__error("pregexp-read-char-list: char class ended too soon")
    }
    let c = pregexp__char(s, i)
    i += 1
    match c {
      ']' =>
        if r is Nil {
          r = cons(Char(c), r)
          i += 1
        } else {
          break
        }
      '\\' => {
        let (c2, i2) = pregexp__read_escaped_char(s, i)
        if c2 is Nil {
          raise pregexp__error("pregexp-read-char-list: backslash")
        }
        r = cons(c2, r)
        i = i2
      }
      '-' =>
        if r is Nil || (i < n && pregexp__char(s, i) == ']') {
          r = cons(Char('-'), r)
        } else {
          let c_1 = car(r)
          if characterp(c_1) {
            r = cdr(r)
            r = cons(
              list3(pregexp__k_char_range, c_1, Char(pregexp__char(s, i))),
              r,
            )
            i += 1
          } else {
            r = cons(Char('-'), r)
          }
        }
      '[' =>
        if pregexp__char(s, i) == ':' {
          let (c, i1) = pregexp__read_posix_char_class(s, i + 1, n)
          r = cons(c, r)
          i = i1
        } else {
          r = cons(Char('['), r)
        }
      _ => r = cons(Char(c), r)
    }
  }
  (cons(pregexp__k_one_of_chars, nreverse(r)), i)
}

// ---------------------------------------------------------------------------
// Matching

///|
fn pregexp__string_match(
  s1 : Array[Char],
  s : Array[Char],
  i : Int,
  n : Int,
  sk : (Int) -> Value raise,
  fk : () -> Value raise,
) -> Value raise {
  let n1 = s1.length()
  if n1 > n {
    return fk()
  }
  let mut j = 0
  let mut k = i
  let mut failp = false
  while true {
    if j >= n1 {
      break
    } else if k >= n {
      failp = true
      break
    } else if s1[j] == pregexp__char(s, k) {
      j += 1
      k += 1
    } else {
      failp = true
      break
    }
  }
  if failp {
    fk()
  } else {
    sk(k)
  }
}

///|
fn pregexp__at_word_boundary_p(s : Array[Char], i : Int, n : Int) -> Bool raise {
  i == 0 ||
  i >= n || {
    let c_i = pregexp__char(s, i)
    let c_i_minus_1 = pregexp__char(s, i - 1)
    let c_i_is_word_p = pregexp__in_char_class_p(c_i, pregexp__k_word)
    let c_i_minus_1_is_word_p = pregexp__in_char_class_p(
      c_i_minus_1,
      pregexp__k_word,
    )
    (c_i_is_word_p && !c_i_minus_1_is_word_p) ||
    (!c_i_is_word_p && c_i_minus_1_is_word_p)
  }
}

///|
/// PREGEXP-CHECK-IF-IN-CHAR-CLASS-P
fn pregexp__in_char_class_p(c : Char, char_class : Value) -> Bool raise {
  let name = match char_class {
    Sym(s) => s.name
    _ => ""
  }
  match name {
    ":any" => c != '\n'
    ":super-any" => true
    ":alnum" => alpha_char_p(c) || pregexp__digit(c)
    ":alpha" => alpha_char_p(c)
    ":ascii" => c.to_int() < 128
    ":blank" => c == ' ' || c == '\t'
    ":cntrl" => c.to_int() < 32
    ":digit" => pregexp__digit(c)
    ":graph" =>
      pregexp__in_char_class_p(c, kw("print")) && !pregexp__whitespace(c)
    ":lower" => lower_case_p(c)
    ":print" => c.to_int() >= 32
    ":punct" =>
      pregexp__in_char_class_p(c, kw("print")) &&
      !(pregexp__whitespace(c) || alpha_char_p(c) || pregexp__digit(c))
    ":space" => pregexp__whitespace(c)
    ":upper" => upper_case_p(c)
    ":word" => alpha_char_p(c) || pregexp__digit(c) || c == '_'
    ":xdigit" =>
      pregexp__digit(c) || ['a', 'b', 'c', 'd', 'e', 'f'].contains(char_downcase(c))
    _ => raise pregexp__error("pregexp-check-if-in-char-class-p")
  }
}

///|
/// CHAR-EQUAL
fn pregexp__char_equal(a : Char, b : Char) -> Bool {
  a == b || char_downcase(a) == char_downcase(b)
}

///|
priv struct PregexpCtx {
  chars : Array[Char]
  mut n : Int
  start : Int
  mut case_sensitive_p : Bool
  // The alist of PREGEXP-MAKE-BACKREF-LIST: (sub-re . (start . end)).
  backref_alist : Value
}

///|
fn pregexp__char_eq1(ctx : PregexpCtx, c1 : Char, c2 : Char) -> Bool {
  if ctx.case_sensitive_p {
    c1 == c2
  } else {
    pregexp__char_equal(c1, c2)
  }
}

///|
fn pregexp__char_le1(ctx : PregexpCtx, c1 : Char, c2 : Char, c3 : Char) -> Bool {
  if ctx.case_sensitive_p {
    c1 <= c2 && c2 <= c3
  } else {
    let a = char_downcase(c1)
    let b = char_downcase(c2)
    let c = char_downcase(c3)
    a <= b && b <= c
  }
}

///|
/// MATCH-LOOP of PREGEXP-MATCH-POSITIONS-AUX (continuation passing).
fn pregexp__match_loop(
  ctx : PregexpCtx,
  re : Value,
  i : Int,
  sk : (Int) -> Value raise,
  fk : () -> Value raise,
) -> Value raise {
  let s = ctx.chars
  if eq(re, pregexp__k_bos) {
    return if i == ctx.start { sk(i) } else { fk() }
  }
  if eq(re, pregexp__k_eos) {
    return if i >= ctx.n { sk(i) } else { fk() }
  }
  if eq(re, pregexp__k_empty) {
    return sk(i)
  }
  if eq(re, pregexp__k_wbdry) {
    return if pregexp__at_word_boundary_p(s, i, ctx.n) { sk(i) } else { fk() }
  }
  if eq(re, pregexp__k_not_wbdry) {
    return if pregexp__at_word_boundary_p(s, i, ctx.n) { fk() } else { sk(i) }
  }
  match re {
    Char(c) if i < ctx.n =>
      return if pregexp__char_eq1(ctx, pregexp__char(s, i), c) {
        sk(i + 1)
      } else {
        fk()
      }
    Cons(_) => ()
    _ =>
      if i < ctx.n {
        return if pregexp__in_char_class_p(pregexp__char(s, i), re) {
          sk(i + 1)
        } else {
          fk()
        }
      } else {
        return fk()
      }
  }
  let op = car(re)
  if eq(op, pregexp__k_char_range) {
    if i >= ctx.n {
      fk()
    } else if pregexp__char_le1(
        ctx,
        pregexp__lchar(cadr(re)),
        pregexp__char(s, i),
        pregexp__lchar(caddr(re)),
      ) {
      sk(i + 1)
    } else {
      fk()
    }
  } else if eq(op, pregexp__k_one_of_chars) {
    if i >= ctx.n {
      fk()
    } else {
      fn one_of_chars_loop(chars : Value) -> Value raise {
        if chars is Nil {
          fk()
        } else {
          pregexp__match_loop(ctx, car(chars), i, sk, () => one_of_chars_loop(
            cdr(chars),
          ))
        }
      }
      one_of_chars_loop(cdr(re))
    }
  } else if eq(op, pregexp__k_neg_char) {
    if i >= ctx.n {
      fk()
    } else {
      pregexp__match_loop(ctx, cadr(re), i, _i1 => fk(), () => sk(i + 1))
    }
  } else if eq(op, pregexp__k_seq) {
    fn seq_loop(res : Value, i : Int) -> Value raise {
      if res is Nil {
        sk(i)
      } else {
        pregexp__match_loop(ctx, car(res), i, i1 => seq_loop(cdr(res), i1), fk)
      }
    }
    seq_loop(cdr(re), i)
  } else if eq(op, pregexp__k_or) {
    fn or_loop(res : Value) -> Value raise {
      if res is Nil {
        fk()
      } else {
        pregexp__match_loop(
          ctx,
          car(res),
          i,
          i1 => {
            let v = sk(i1)
            if v.truthy() {
              v
            } else {
              or_loop(cdr(res))
            }
          },
          () => or_loop(cdr(res)),
        )
      }
    }
    or_loop(cdr(re))
  } else if eq(op, pregexp__k_backref) {
    let cell = nth(pregexp__int(cadr(re)), ctx.backref_alist)
    let backref = if cell.truthy() {
      cdr(cell)
    } else {
      raise pregexp__error(
        "pregexp-match-positions-aux: non-existent backref " +
        prin1_to_string(re),
      )
    }
    if backref.truthy() {
      let a = pregexp__int(car(backref))
      let b = pregexp__int(cdr(backref))
      pregexp__string_match(s[a:b].to_array(), s, i, ctx.n, sk, fk)
    } else {
      sk(i)
    }
  } else if eq(op, pregexp__k_sub) {
    pregexp__match_loop(
      ctx,
      cadr(re),
      i,
      i1 => {
        // (setf (cdr (assoc re backrefs)) (cons i i1))
        rplacd(assoc(re, ctx.backref_alist), cons(int(i), int(i1))) |> ignore
        sk(i1)
      },
      fk,
    )
  } else if eq(op, pregexp__k_lookahead) || eq(op, pregexp__k_neg_lookahead) {
    let found_it_p = pregexp__match_loop(ctx, cadr(re), i, i1 => int(i1), () => Nil)
    let pos = eq(op, pregexp__k_lookahead)
    if found_it_p.truthy() == pos {
      sk(i)
    } else {
      fk()
    }
  } else if eq(op, pregexp__k_lookbehind) || eq(op, pregexp__k_neg_lookbehind) {
    let n_actual = ctx.n
    ctx.n = i
    let found_it_p = pregexp__match_loop(
      ctx,
      list([
        pregexp__k_seq,
        list([pregexp__k_between, Nil, Fix(0L), Nil, pregexp__k_super_any]),
        cadr(re),
        pregexp__k_eos,
      ]),
      ctx.start,
      i1 => int(i1),
      () => Nil,
    )
    ctx.n = n_actual
    let pos = eq(op, pregexp__k_lookbehind)
    if found_it_p.truthy() == pos {
      sk(i)
    } else {
      fk()
    }
  } else if eq(op, pregexp__k_no_backtrack) {
    let found_it_p = pregexp__match_loop(ctx, cadr(re), i, i1 => int(i1), () => Nil)
    if found_it_p.truthy() {
      sk(pregexp__int(found_it_p))
    } else {
      fk()
    }
  } else if eq(op, pregexp__k_case_sensitive) ||
    eq(op, pregexp__k_case_insensitive) {
    let old_case_sensitive_p = ctx.case_sensitive_p
    ctx.case_sensitive_p = eq(op, pregexp__k_case_sensitive)
    pregexp__match_loop(
      ctx,
      cadr(re),
      i,
      i1 => {
        ctx.case_sensitive_p = old_case_sensitive_p
        sk(i1)
      },
      () => {
        ctx.case_sensitive_p = old_case_sensitive_p
        fk()
      },
    )
  } else if eq(op, pregexp__k_between) {
    let non_greedy_p = nth(1, re).truthy()
    let p = pregexp__int(nth(2, re))
    let q0 = nth(3, re)
    let re = nth(4, re)
    let could_loop_infinitely_p = !non_greedy_p && q0 is Nil
    let q : Int? = if q0 is Nil { None } else { Some(pregexp__int(q0) - p) }
    fn q_loop(k : Int, i : Int) -> Value raise {
      let fk = () => sk(i)
      match q {
        Some(qn) if k >= qn => return fk()
        _ => ()
      }
      if !non_greedy_p {
        pregexp__match_loop(
          ctx,
          re,
          i,
          i1 => {
            if could_loop_infinitely_p && i1 == i {
              raise pregexp__error(
                "pregexp-match-positions-aux greedy quantifier operand could be empty",
              )
            }
            let v = q_loop(k + 1, i1)
            if v.truthy() {
              v
            } else {
              fk()
            }
          },
          fk,
        )
      } else {
        let v = fk()
        if v.truthy() {
          v
        } else {
          pregexp__match_loop(ctx, re, i, i1 => q_loop(k + 1, i1), fk)
        }
      }
    }
    fn p_loop(k : Int, i : Int) -> Value raise {
      if k < p {
        pregexp__match_loop(
          ctx,
          re,
          i,
          i1 => if could_loop_infinitely_p && i1 == i {
            raise pregexp__error(
              "pregexp-match-positions-aux: greedy quantifier operand could be empty",
            )
          } else {
            p_loop(k + 1, i1)
          },
          fk,
        )
      } else {
        q_loop(0, i)
      }
    }
    p_loop(0, i)
  } else {
    raise pregexp__error("pregexp-match-positions-aux")
  }
}

///|
fn pregexp__match_positions_aux(
  re : Value,
  s : Array[Char],
  start : Int,
  n : Int,
  i : Int,
) -> Value raise {
  let ctx : PregexpCtx = {
    chars: s,
    n,
    start,
    case_sensitive_p: true,
    backref_alist: rx_pregexp_make_backref_list(re),
  }
  pregexp__match_loop(ctx, re, i, i1 => int(i1), () => Nil) |> ignore
  let backrefs = mapcar(x => cdr(x), ctx.backref_alist)
  if car(backrefs).truthy() {
    backrefs
  } else {
    Nil
  }
}

///|
fn pregexp__match_positions(
  pat : Value,
  s : Array[Char],
  start : Value,
  end : Value,
) -> Value raise {
  let pat = if stringp(pat) { rx_pregexp(pat) } else { pat }
  if !consp(pat) {
    raise pregexp__error(
      "pregexp-match-positions: pattern " +
      prin1_to_string(pat) +
      " must be compiled or string regexp",
    )
  }
  let str_len = s.length()
  let start = if start is Nil { 0 } else { pregexp__int(start) }
  let end = if end is Nil || pregexp__int(end) > str_len {
    str_len
  } else {
    pregexp__int(end)
  }
  let mut i = start
  while i <= end {
    let res = pregexp__match_positions_aux(pat, s, start, end, i)
    if res.truthy() {
      return res
    }
    i += 1
  }
  Nil
}

///|
fn pregexp__subseq(s : Array[Char], a : Int, b : Int) -> String raise {
  if a < 0 || b > s.length() || a > b {
    raise pregexp__error(
      "The bounding indices \{a} and \{b} are bad for a sequence of length \{s.length()}.",
    )
  }
  chars_to_string(s[a:b].to_array())
}

///|
fn pregexp__replace_aux(
  str : Array[Char],
  ins : Array[Char],
  n : Int,
  backrefs : Value,
) -> String raise {
  let sb = StringBuilder::new()
  let mut i = 0
  while true {
    if i >= n {
      return sb.to_string()
    }
    let c = pregexp__char(ins, i)
    i += 1
    if c == '\\' {
      let mut mi = pregexp__read_escaped_number(ins, i, n)
      if mi is None && pregexp__char(str, i) == '&' {
        mi = Some((Fix(0L), i + 1))
      }
      match mi {
        Some((m, i1)) => {
          let backref = nth(pregexp__int(m), backrefs)
          if backref.truthy() {
            sb.write_string(
              pregexp__subseq(
                str,
                pregexp__int(car(backref)),
                pregexp__int(cdr(backref)),
              ),
            )
          }
          i = i1
        }
        None => {
          let c2 = pregexp__char(ins, i)
          i += 1
          if c2 != '$' {
            sb.write_char(c2)
          }
        }
      }
    } else {
      sb.write_char(c)
    }
  }
  ""
}

// ---------------------------------------------------------------------------
// The declared functions

///|
fn rx_pregexp_read_pattern(s : Value, i : Value, n : Value) -> (Value, Value) raise {
  let (v, j) = pregexp__read_pattern(
    pregexp__chars(s),
    pregexp__int(i),
    pregexp__int(n),
  )
  (v, int(j))
}

///|
fn rx_pregexp_read_branch(s : Value, i : Value, n : Value) -> (Value, Value) raise {
  let (v, j) = pregexp__read_branch(
    pregexp__chars(s),
    pregexp__int(i),
    pregexp__int(n),
  )
  (v, int(j))
}

///|
fn rx_pregexp_read_piece(s : Value, i : Value, n : Value) -> (Value, Value) raise {
  let (v, j) = pregexp__read_piece(
    pregexp__chars(s),
    pregexp__int(i),
    pregexp__int(n),
  )
  (v, if j < 0 { Nil } else { int(j) })
}

///|
fn rx_pregexp_read_escaped_number(
  s : Value,
  i : Value,
  n : Value,
) -> (Value, Value) raise {
  match
    pregexp__read_escaped_number(
      pregexp__chars(s),
      pregexp__int(i),
      pregexp__int(n),
    ) {
    Some((m, j)) => (m, int(j))
    None => (Nil, Nil)
  }
}

///|
fn rx_pregexp_read_escaped_char(s : Value, i : Value) -> (Value, Value) raise {
  let (v, j) = pregexp__read_escaped_char(pregexp__chars(s), pregexp__int(i))
  (v, int(j))
}

///|
fn rx_pregexp_read_posix_char_class(
  s : Value,
  i : Value,
  n : Value,
) -> (Value, Value) raise {
  let (v, j) = pregexp__read_posix_char_class(
    pregexp__chars(s),
    pregexp__int(i),
    pregexp__int(n),
  )
  (v, int(j))
}

///|
fn rx_pregexp_read_cluster_type(s : Value, i : Value) -> (Value, Value) raise {
  let (v, j) = pregexp__read_cluster_type(pregexp__chars(s), pregexp__int(i))
  (v, int(j))
}

///|
fn rx_pregexp_read_subpattern(
  s : Value,
  i : Value,
  n : Value,
) -> (Value, Value) raise {
  let (v, j) = pregexp__read_subpattern(
    pregexp__chars(s),
    pregexp__int(i),
    pregexp__int(n),
  )
  (v, int(j))
}

///|
fn rx_pregexp_wrap_quantifier_if_any(
  re : Value,
  s : Value,
  i : Value,
  n : Value,
) -> (Value, Value) raise {
  let (v, j) = pregexp__wrap_quantifier_if_any(
    re,
    pregexp__chars(s),
    pregexp__int(i),
    pregexp__int(n),
  )
  (v, int(j))
}

///|
fn rx_pregexp_whitespacep(c : Value) -> Value raise {
  lbool(pregexp__whitespace(pregexp__lchar(c)))
}

///|
fn rx_pregexp_read_nums(s : Value, i : Value, n : Value) -> (Value, Value, Value) raise {
  let (p, q, j) = pregexp__read_nums(
    pregexp__chars(s),
    pregexp__int(i),
    pregexp__int(n),
  )
  (p, q, int(j))
}

///|
fn rx_pregexp_read_char_list(
  s : Value,
  i : Value,
  n : Value,
) -> (Value, Value) raise {
  let (v, j) = pregexp__read_char_list(
    pregexp__chars(s),
    pregexp__int(i),
    pregexp__int(n),
  )
  (v, int(j))
}

///|
fn rx_pregexp_string_match(
  s1 : Value,
  s : Value,
  i : Value,
  n : Value,
  sk : Value,
  fk : Value,
) -> Value raise {
  pregexp__string_match(
    pregexp__chars(s1),
    pregexp__chars(s),
    pregexp__int(i),
    pregexp__int(n),
    k => funcall(sk, [int(k)]),
    () => funcall(fk, []),
  )
}

///|
fn rx_pregexp_char_word_q(c : Value) -> Value raise {
  let c = pregexp__lchar(c)
  lbool(alpha_char_p(c) || pregexp__digit(c) || c == '_')
}

///|
fn rx_pregexp_at_word_boundary_p(s : Value, i : Value, n : Value) -> Value raise {
  lbool(
    pregexp__at_word_boundary_p(
      pregexp__chars(s),
      pregexp__int(i),
      pregexp__int(n),
    ),
  )
}

///|
fn rx_pregexp_check_if_in_char_class_p(c : Value, char_class : Value) -> Value raise {
  lbool(pregexp__in_char_class_p(pregexp__lchar(c), char_class))
}

///|
fn rx_pregexp_make_backref_list(re : Value) -> Value raise {
  if consp(re) {
    let re1 = car(re)
    let rest_backrefs = rx_pregexp_make_backref_list(cdr(re))
    if eq(re1, pregexp__k_sub) {
      cons(cons(re, Nil), rest_backrefs)
    } else {
      append(rx_pregexp_make_backref_list(re1), rest_backrefs)
    }
  } else {
    Nil
  }
}

///|
fn rx_pregexp_match_positions_aux(
  re : Value,
  s : Value,
  sn : Value,
  start : Value,
  n : Value,
  i : Value,
) -> Value raise {
  ignore(sn)
  pregexp__match_positions_aux(
    re,
    pregexp__chars(s),
    pregexp__int(start),
    pregexp__int(n),
    pregexp__int(i),
  )
}

///|
fn rx_pregexp_replace_aux(
  str : Value,
  ins : Value,
  n : Value,
  backrefs : Value,
) -> Value raise {
  Str(
    pregexp__replace_aux(
      pregexp__chars(str),
      pregexp__chars(ins),
      pregexp__int(n),
      backrefs,
    ),
  )
}

///|
fn rx_pregexp(s : Value) -> Value raise {
  // in case it got corrupted
  pregexp__set_space_sensitive_p(true)
  let cs = pregexp__chars(s)
  list2(pregexp__k_sub, pregexp__read_pattern(cs, 0, cs.length()).0)
}

///|
fn rx_pregexp_match_positions(
  pat : Value,
  str : Value,
  start? : Value = Nil,
  end? : Value = Nil,
) -> Value raise {
  pregexp__match_positions(pat, pregexp__chars(str), start, end)
}

///|
fn rx_pregexp_match(
  pat : Value,
  str : Value,
  start? : Value = Nil,
  end? : Value = Nil,
) -> Value raise {
  let s = pregexp__chars(str)
  let index_pairs = pregexp__match_positions(pat, s, start, end)
  if index_pairs is Nil {
    return Nil
  }
  let r = Collector::new()
  for index_pair in index_pairs.iter() {
    r.add(
      if index_pair.truthy() {
        Str(
          pregexp__subseq(
            s,
            pregexp__int(car(index_pair)),
            pregexp__int(cdr(index_pair)),
          ),
        )
      } else {
        Nil
      },
    )
  }
  r.result()
}

///|
fn rx_pregexp_split(pat : Value, str : Value) -> Value raise {
  // split str into substrings, using pat as delim
  let s = pregexp__chars(str)
  let mut r : Value = Nil
  let n = s.length()
  let mut i = 0
  let mut picked_up_one_undelimited_char_p = false
  while true {
    if i >= n {
      return nreverse(r)
    }
    let it = car(pregexp__match_positions(pat, s, int(i), int(n)))
    if it.truthy() {
      let j = pregexp__int(car(it))
      let k = pregexp__int(cdr(it))
      if j == k {
        r = cons(Str(pregexp__subseq(s, i, j + 1)), r)
        i = k + 1
        picked_up_one_undelimited_char_p = true
      } else if j == i && picked_up_one_undelimited_char_p {
        i = k
        picked_up_one_undelimited_char_p = false
      } else {
        r = cons(Str(pregexp__subseq(s, i, j)), r)
        i = k
        picked_up_one_undelimited_char_p = false
      }
    } else {
      r = cons(Str(pregexp__subseq(s, i, n)), r)
      i = n
    }
  }
  Nil
}

///|
fn rx_pregexp_replace(pat : Value, str : Value, ins : Value) -> Value raise {
  let s = pregexp__chars(str)
  let n = s.length()
  let pp = pregexp__match_positions(pat, s, Fix(0L), int(n))
  if pp is Nil {
    return str
  }
  let insc = pregexp__chars(ins)
  let m_i = pregexp__int(caar(pp))
  let m_n = pregexp__int(cdar(pp))
  Str(
    pregexp__subseq(s, 0, m_i) +
    pregexp__replace_aux(s, insc, insc.length(), pp) +
    pregexp__subseq(s, m_n, n),
  )
}

///|
fn rx_pregexp_replace_star(pat : Value, str : Value, ins : Value) -> Value raise {
  // return str with every occurrence of pat replaced by ins
  let pat = if stringp(pat) { rx_pregexp(pat) } else { pat }
  let s = pregexp__chars(str)
  let n = s.length()
  let insc = pregexp__chars(ins)
  let ins_len = insc.length()
  let mut i = 0
  let r = StringBuilder::new()
  while true {
    // i = index in str to start replacing from
    // r = already calculated prefix of answer
    if i >= n {
      return Str(r.to_string())
    }
    let pp = pregexp__match_positions(pat, s, int(i), int(n))
    if pp is Nil {
      return if i == 0 {
        // this implies pat didn't match str at all, so let's return
        // original str
        str
      } else {
        Str(r.to_string() + pregexp__subseq(s, i, n))
      }
    }
    r.write_string(pregexp__subseq(s, i, pregexp__int(caar(pp))))
    r.write_string(pregexp__replace_aux(s, insc, ins_len, pp))
    i = pregexp__int(cdar(pp))
  }
  Nil
}

///|
fn rx_pregexp_quote(s : Value) -> Value raise {
  let cs = pregexp__chars(s)
  let sb = StringBuilder::new()
  for c in cs {
    if [
        '\\', '.', '?', '*', '+', '|', '^', '$', '[', ']', '{', '}', '(', ')',
      ].contains(c) {
      sb.write_char('\\')
    }
    sb.write_char(c)
  }
  Str(sb.to_string())
}

///|
/// The macro PREGEXP-RECUR, called as a function on its (unevaluated)
/// arguments: evaluate its expansion
/// (labels ((name vars . body)) (name . vals)).
fn rx_pregexp_recur(name : Value, varvals : Value, body : Value) -> Value raise {
  let vars = mapcar(x => car(x), varvals)
  let vals = mapcar(x => cadr(x), varvals)
  lisp_eval_form(
    list3(
      sym("labels"),
      list1(cons(name, cons(vars, body))),
      cons(name, vals),
    ),
  )
}

///|
fn init_pregexp() -> Unit raise {
  ()
}
