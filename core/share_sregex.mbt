// Port of share/stringproc/sregex.lisp: Maxima interface to pregexp.lisp
// (a portable regex parser by Dorai Sitaram).
//
// src/pregexp.lisp is not part of the port (it is excluded from the
// generated contract), so its functions are translated here as private
// helpers (share_sregex__pregexp_*). Parse trees are Lisp data as in the
// original: keywords, characters and lists.
//
// Like in stringproc.lisp positions are 1-indexed at Maxima level.

// ---------------------------------------------------------------------------
// pregexp

///|
let share_sregex__space_sensitive_p : Ref[Bool] = Ref(true)

///|
let share_sregex__k_or : Value = kw("or")

///|
let share_sregex__k_seq : Value = kw("seq")

///|
let share_sregex__k_bos : Value = kw("bos")

///|
let share_sregex__k_eos : Value = kw("eos")

///|
let share_sregex__k_any : Value = kw("any")

///|
let share_sregex__k_super_any : Value = kw("super-any")

///|
let share_sregex__k_neg_char : Value = kw("neg-char")

///|
let share_sregex__k_backref : Value = kw("backref")

///|
let share_sregex__k_empty : Value = kw("empty")

///|
let share_sregex__k_wbdry : Value = kw("wbdry")

///|
let share_sregex__k_not_wbdry : Value = kw("not-wbdry")

///|
let share_sregex__k_digit : Value = kw("digit")

///|
let share_sregex__k_space : Value = kw("space")

///|
let share_sregex__k_word : Value = kw("word")

///|
let share_sregex__k_lookahead : Value = kw("lookahead")

///|
let share_sregex__k_neg_lookahead : Value = kw("neg-lookahead")

///|
let share_sregex__k_no_backtrack : Value = kw("no-backtrack")

///|
let share_sregex__k_lookbehind : Value = kw("lookbehind")

///|
let share_sregex__k_neg_lookbehind : Value = kw("neg-lookbehind")

///|
let share_sregex__k_case_sensitive : Value = kw("case-sensitive")

///|
let share_sregex__k_case_insensitive : Value = kw("case-insensitive")

///|
let share_sregex__k_sub : Value = kw("sub")

///|
let share_sregex__k_between : Value = kw("between")

///|
let share_sregex__k_char_range : Value = kw("char-range")

///|
let share_sregex__k_one_of_chars : Value = kw("one-of-chars")

///|
fn share_sregex__error(msg : String) -> LispError {
  LispError::SimpleError(msg)
}

///|
/// (char s i)
fn share_sregex__char(s : Array[Char], i : Int) -> Char raise {
  if i < 0 || i >= s.length() {
    raise share_sregex__error(
      "Invalid index \{i} for (SIMPLE-ARRAY CHARACTER (\{s.length()})), should be a non-negative integer below \{s.length()}.",
    )
  }
  s[i]
}

///|
fn share_sregex__ascii_digit_p(c : Char) -> Bool {
  c >= '0' && c <= '9'
}

///|
fn share_sregex__whitespacep(c : Char) -> Bool {
  c == ' ' || c == '\t' || !share_stringproc__graphic_char_p(c)
}

///|
fn share_sregex__read_pattern(s : Array[Char], i : Int, n : Int) -> (Value, Int) raise {
  if i >= n {
    return (list2(share_sregex__k_or, list1(share_sregex__k_seq)), i)
  }
  let mut i = i
  let mut branches : Value = Nil
  while true {
    if i >= n || share_sregex__char(s, i) == ')' {
      return (cons(share_sregex__k_or, nreverse(branches)), i)
    }
    let (branch1, i1) = share_sregex__read_branch(
      s,
      if share_sregex__char(s, i) == '|' {
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
fn share_sregex__read_branch(s : Array[Char], i : Int, n : Int) -> (Value, Int) raise {
  let mut i = i
  let mut pieces : Value = Nil
  while true {
    if i >= n || share_sregex__char(s, i) == '|' || share_sregex__char(s, i) == ')' {
      return (cons(share_sregex__k_seq, nreverse(pieces)), i)
    }
    let (pc, i_new) = share_sregex__read_piece(s, i, n)
    pieces = cons(pc, pieces)
    i = i_new
  }
  (Nil, i)
}

///|
fn share_sregex__read_piece(s : Array[Char], i : Int, n : Int) -> (Value, Int) raise {
  let c = share_sregex__char(s, i)
  let mut i = i + 1
  match c {
    '^' => (share_sregex__k_bos, i)
    '$' => (share_sregex__k_eos, i)
    '.' => share_sregex__wrap_quantifier_if_any(share_sregex__k_any, s, i, n)
    '[' => {
      let mut negp = false
      if i < n && share_sregex__char(s, i) == '^' {
        i += 1
        negp = true
      }
      if i < n {
        let (chars, i1) = share_sregex__read_char_list(s, i, n)
        share_sregex__wrap_quantifier_if_any(
          if negp {
            list2(share_sregex__k_neg_char, chars)
          } else {
            chars
          },
          s,
          i1,
          n,
        )
      } else {
        raise share_sregex__error("pregexp-read-piece: char class ended too soon")
      }
    }
    '(' => {
      let (re, i1) = share_sregex__read_subpattern(s, i, n)
      share_sregex__wrap_quantifier_if_any(re, s, i1, n)
    }
    '\\' =>
      match share_sregex__read_escaped_number(s, i, n) {
        Some((m, i1)) =>
          share_sregex__wrap_quantifier_if_any(
            list2(share_sregex__k_backref, m),
            s,
            i1,
            n,
          )
        None => {
          let (c, i1) = share_sregex__read_escaped_char(s, i)
          share_sregex__wrap_quantifier_if_any(c, s, i1, n)
        }
      }
    _ =>
      if share_sregex__space_sensitive_p.val ||
        (!share_sregex__whitespacep(c) && c != ';') {
        share_sregex__wrap_quantifier_if_any(Char(c), s, i, n)
      } else {
        let mut in_comment_p = false
        let mut c = c
        while true {
          if in_comment_p {
            if c == '\n' {
              in_comment_p = false
            }
          } else if share_sregex__whitespacep(c) {
            ()
          } else if c == ';' {
            in_comment_p = true
          } else {
            i -= 1
            return (share_sregex__k_empty, i)
          }
          if i >= n {
            return (share_sregex__k_empty, i)
          }
          c = share_sregex__char(s, i)
          i += 1
        }
        (Nil, i)
      }
  }
}

///|
fn share_sregex__read_escaped_number(
  s : Array[Char],
  i : Int,
  n : Int,
) -> (Value, Int)? raise {
  let mut i = i
  let sb = StringBuilder::new()
  while i < n && share_sregex__ascii_digit_p(share_sregex__char(s, i)) {
    sb.write_char(s[i])
    i += 1
  }
  let r = sb.to_string()
  if r == "" {
    None
  } else {
    match parse_integer(r) {
      Some(v) => Some((v, i))
      None => None
    }
  }
}

///|
fn share_sregex__read_escaped_char(s : Array[Char], i : Int) -> (Value, Int) raise {
  let c = share_sregex__char(s, i)
  let v = match c {
    'b' => share_sregex__k_wbdry
    'B' => share_sregex__k_not_wbdry
    'd' => share_sregex__k_digit
    'D' => list2(share_sregex__k_neg_char, share_sregex__k_digit)
    'n' => Char('\n')
    'r' => Char('\r')
    's' => share_sregex__k_space
    'S' => list2(share_sregex__k_neg_char, share_sregex__k_space)
    't' => Char('\t')
    'w' => share_sregex__k_word
    'W' => list2(share_sregex__k_neg_char, share_sregex__k_word)
    _ => Char(c)
  }
  (v, i + 1)
}

///|
fn share_sregex__read_posix_char_class(
  s : Array[Char],
  i : Int,
  n : Int,
) -> (Value, Int) raise {
  let mut i = i
  let r = StringBuilder::new()
  let mut negp = false
  while true {
    if i >= n {
      raise share_sregex__error("pregexp-read-posix-char-class")
    }
    let c = share_sregex__char(s, i)
    i += 1
    if c == '^' {
      negp = true
    } else if alpha_char_p(c) {
      r.write_char(c)
    } else if c == ':' {
      if i >= n || share_sregex__char(s, i) != ']' {
        raise share_sregex__error("pregexp-read-posix-char-class")
      }
      i += 1
      break
    } else {
      raise share_sregex__error("pregexp-read-posix-char-class")
    }
  }
  // (intern (string-upcase name) :keyword)
  let posix_class = sym(":" + invert_case(string_upcase(r.to_string())))
  (
    if negp {
      list2(share_sregex__k_neg_char, posix_class)
    } else {
      posix_class
    },
    i,
  )
}

///|
fn share_sregex__read_cluster_type(s : Array[Char], i : Int) -> (Value, Int) raise {
  let mut c = share_sregex__char(s, i)
  let mut i = i + 1
  if c != '?' {
    i -= 1
    return (list1(share_sregex__k_sub), i)
  }
  c = share_sregex__char(s, i)
  i += 1
  match c {
    ':' => (Nil, i)
    '=' => (list1(share_sregex__k_lookahead), i)
    '!' => (list1(share_sregex__k_neg_lookahead), i)
    '>' => (list1(share_sregex__k_no_backtrack), i)
    '<' => {
      c = share_sregex__char(s, i)
      i += 1
      match c {
        '=' => (list1(share_sregex__k_lookbehind), i)
        '!' => (list1(share_sregex__k_neg_lookbehind), i)
        _ => raise share_sregex__error("pregexp-read-cluster-type")
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
                share_sregex__k_case_sensitive
              } else {
                share_sregex__k_case_insensitive
              },
              r,
            )
            invp = false
          }
          'x' => {
            share_sregex__space_sensitive_p.val = invp
            invp = false
          }
          ':' => return (nreverse(r), i)
          _ => raise share_sregex__error("pregexp-read-cluster-type")
        }
        c = share_sregex__char(s, i)
        i += 1
      }
      (Nil, i)
    }
  }
}

///|
fn share_sregex__read_subpattern(s : Array[Char], i : Int, n : Int) -> (Value, Int) raise {
  let remember_space_sensitive_p = share_sregex__space_sensitive_p.val
  let (ctyp, i1) = share_sregex__read_cluster_type(s, i)
  let (re0, i2) = share_sregex__read_pattern(s, i1, n)
  share_sregex__space_sensitive_p.val = remember_space_sensitive_p
  if i2 < n && share_sregex__char(s, i2) == ')' {
    let mut re = re0
    for ct in ctyp.iter() {
      re = list2(ct, re)
    }
    (re, i2 + 1)
  } else {
    raise share_sregex__error("pregexp-read-subpattern")
  }
}

///|
fn share_sregex__wrap_quantifier_if_any(
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
    let c = share_sregex__char(s, i)
    i += 1
    if share_sregex__whitespacep(c) && !share_sregex__space_sensitive_p.val {
      continue
    }
    match c {
      '*' | '+' | '?' | '{' => {
        // (:between non-greedy at-least at-most re)
        let mut non_greedy : Value = Nil
        let (p, q) = match c {
          '*' => (int(0), Value::Nil)
          '+' => (int(1), Value::Nil)
          '?' => (int(0), int(1))
          _ => {
            let (p, q, i1) = share_sregex__read_nums(s, i, n)
            i = i1
            (p, q)
          }
        }
        while true {
          if i >= n {
            break
          }
          let c = share_sregex__char(s, i)
          i += 1
          if share_sregex__whitespacep(c) && !share_sregex__space_sensitive_p.val {
            continue
          } else if c == '?' {
            non_greedy = t
            break
          } else {
            i -= 1
            break
          }
        }
        return (list([share_sregex__k_between, non_greedy, p, q, re]), i)
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
fn share_sregex__read_nums(s : Array[Char], i : Int, n : Int) -> (Value, Value, Int) raise {
  let mut i = i
  let p = StringBuilder::new()
  let q = StringBuilder::new()
  let mut reading = 1
  while true {
    if i >= n {
      raise share_sregex__error("pregexp-read-nums: unmatched left brace")
    }
    let c = share_sregex__char(s, i)
    if share_sregex__ascii_digit_p(c) {
      if reading == 1 {
        p.write_char(c)
      } else {
        q.write_char(c)
      }
      i += 1
    } else if share_sregex__whitespacep(c) && !share_sregex__space_sensitive_p.val {
      i += 1
    } else if c == ',' && reading == 1 {
      i += 1
      reading += 1
    } else if c == '}' {
      i += 1
      let pv = parse_integer(p.to_string()).unwrap_or(Value::Nil)
      let qv = parse_integer(q.to_string()).unwrap_or(Value::Nil)
      return if pv is Nil && reading == 1 {
        (int(0), Nil, i)
      } else if reading == 1 {
        (pv, pv, i)
      } else {
        (pv, qv, i)
      }
    } else {
      raise share_sregex__error(
        "pregexp-read-nums: left brace must be followed by number",
      )
    }
  }
  (Nil, Nil, i)
}

///|
fn share_sregex__read_char_list(s : Array[Char], i : Int, n : Int) -> (Value, Int) raise {
  let mut i = i
  let mut r : Value = Nil
  while true {
    if i >= n {
      raise share_sregex__error(
        "pregexp-read-char-list: char class ended too soon",
      )
    }
    let c = share_sregex__char(s, i)
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
        let (c2, i2) = share_sregex__read_escaped_char(s, i)
        r = cons(c2, r)
        i = i2
      }
      '-' =>
        if r is Nil || (i < n && share_sregex__char(s, i) == ']') {
          r = cons(Char('-'), r)
        } else {
          let c_1 = car(r)
          if characterp(c_1) {
            r = cdr(r)
            r = cons(
              list3(share_sregex__k_char_range, c_1, Char(share_sregex__char(s, i))),
              r,
            )
            i += 1
          } else {
            r = cons(Char('-'), r)
          }
        }
      '[' =>
        if share_sregex__char(s, i) == ':' {
          let (c, i1) = share_sregex__read_posix_char_class(s, i + 1, n)
          r = cons(c, r)
          i = i1
        } else {
          r = cons(Char('['), r)
        }
      _ => r = cons(Char(c), r)
    }
  }
  (cons(share_sregex__k_one_of_chars, nreverse(r)), i)
}

///|
fn share_sregex__string_match(
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
    } else if s1[j] == share_sregex__char(s, k) {
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
fn share_sregex__at_word_boundary_p(s : Array[Char], i : Int, n : Int) -> Bool raise {
  i == 0 ||
  i >= n || {
    let c_i = share_sregex__char(s, i)
    let c_i_minus_1 = share_sregex__char(s, i - 1)
    let c_i_is_word_p = share_sregex__in_char_class_p(c_i, share_sregex__k_word)
    let c_i_minus_1_is_word_p = share_sregex__in_char_class_p(
      c_i_minus_1,
      share_sregex__k_word,
    )
    (c_i_is_word_p && !c_i_minus_1_is_word_p) ||
    (!c_i_is_word_p && c_i_minus_1_is_word_p)
  }
}

///|
fn share_sregex__in_char_class_p(c : Char, char_class : Value) -> Bool raise {
  let name = match char_class {
    Sym(s) => s.name
    _ => ""
  }
  let digit = share_stringproc__digit_weight(c) is Some(_)
  match name {
    ":any" => c != '\n'
    ":super-any" => true
    ":alnum" => alpha_char_p(c) || digit
    ":alpha" => alpha_char_p(c)
    ":ascii" => c.to_int() < 128
    ":blank" => c == ' ' || c == '\t'
    ":cntrl" => c.to_int() < 32
    ":digit" => digit
    ":graph" => c.to_int() >= 32 && !share_sregex__whitespacep(c)
    ":lower" => share_stringproc__lower_case_p(c)
    ":print" => c.to_int() >= 32
    ":punct" =>
      c.to_int() >= 32 && !(share_sregex__whitespacep(c) || alpha_char_p(c) || digit)
    ":space" => share_sregex__whitespacep(c)
    ":upper" => share_stringproc__upper_case_p(c)
    ":word" => alpha_char_p(c) || digit || c == '_'
    ":xdigit" =>
      digit ||
      ['a', 'b', 'c', 'd', 'e', 'f'].contains(share_stringproc__char_downcase(c))
    _ => raise share_sregex__error("pregexp-check-if-in-char-class-p")
  }
}

///|
fn share_sregex__make_backref_list(re : Value) -> Array[(Value, Ref[Value])] {
  match re {
    Cons(_) => {
      let re1 = car(re)
      let rest_backrefs = share_sregex__make_backref_list(cdr(re))
      if physical_equal_value(re1, share_sregex__k_sub) || eq(re1, share_sregex__k_sub) {
        let r : Array[(Value, Ref[Value])] = [(re, Ref(Nil))]
        for x in rest_backrefs {
          r.push(x)
        }
        r
      } else {
        let r = share_sregex__make_backref_list(re1)
        for x in rest_backrefs {
          r.push(x)
        }
        r
      }
    }
    _ => []
  }
}

///|
priv struct ShareSregexCtx {
  s : Array[Char]
  mut n : Int
  start : Int
  mut case_sensitive_p : Bool
  backrefs : Array[(Value, Ref[Value])]
}

///|
fn share_sregex__char_eq1(ctx : ShareSregexCtx, c1 : Char, c2 : Char) -> Bool {
  if ctx.case_sensitive_p {
    c1 == c2
  } else {
    share_stringproc__equal_code(c1) == share_stringproc__equal_code(c2)
  }
}

///|
fn share_sregex__char_le1(ctx : ShareSregexCtx, c1 : Char, c2 : Char, c3 : Char) -> Bool {
  if ctx.case_sensitive_p {
    c1 <= c2 && c2 <= c3
  } else {
    let a = share_stringproc__equal_code(c1)
    let b = share_stringproc__equal_code(c2)
    let c = share_stringproc__equal_code(c3)
    a <= b && b <= c
  }
}

///|
fn share_sregex__op_is(re : Value, k : Value) -> Bool {
  eq(car(re), k)
}

///|
/// MATCH-LOOP of PREGEXP-MATCH-POSITIONS-AUX (continuation passing).
fn share_sregex__match_loop(
  ctx : ShareSregexCtx,
  re : Value,
  i : Int,
  sk : (Int) -> Value raise,
  fk : () -> Value raise,
) -> Value raise {
  let s = ctx.s
  if eq(re, share_sregex__k_bos) {
    return if i == ctx.start { sk(i) } else { fk() }
  }
  if eq(re, share_sregex__k_eos) {
    return if i >= ctx.n { sk(i) } else { fk() }
  }
  if eq(re, share_sregex__k_empty) {
    return sk(i)
  }
  if eq(re, share_sregex__k_wbdry) {
    return if share_sregex__at_word_boundary_p(s, i, ctx.n) { sk(i) } else { fk() }
  }
  if eq(re, share_sregex__k_not_wbdry) {
    return if share_sregex__at_word_boundary_p(s, i, ctx.n) { fk() } else { sk(i) }
  }
  match re {
    Char(c) if i < ctx.n =>
      return if share_sregex__char_eq1(ctx, share_sregex__char(s, i), c) {
        sk(i + 1)
      } else {
        fk()
      }
    Cons(_) => ()
    _ =>
      if i < ctx.n {
        return if share_sregex__in_char_class_p(share_sregex__char(s, i), re) {
          sk(i + 1)
        } else {
          fk()
        }
      } else {
        return fk()
      }
  }
  let op = car(re)
  if eq(op, share_sregex__k_char_range) {
    if i >= ctx.n {
      fk()
    } else if share_sregex__char_le1(
        ctx,
        share_stringproc__lchar(cadr(re)),
        share_sregex__char(s, i),
        share_stringproc__lchar(caddr(re)),
      ) {
      sk(i + 1)
    } else {
      fk()
    }
  } else if eq(op, share_sregex__k_one_of_chars) {
    if i >= ctx.n {
      fk()
    } else {
      fn one_of_chars_loop(chars : Value) -> Value raise {
        if chars is Nil {
          fk()
        } else {
          share_sregex__match_loop(ctx, car(chars), i, sk, () => one_of_chars_loop(
            cdr(chars),
          ))
        }
      }
      one_of_chars_loop(cdr(re))
    }
  } else if eq(op, share_sregex__k_neg_char) {
    if i >= ctx.n {
      fk()
    } else {
      share_sregex__match_loop(ctx, cadr(re), i, _i1 => fk(), () => sk(i + 1))
    }
  } else if eq(op, share_sregex__k_seq) {
    fn seq_loop(res : Value, i : Int) -> Value raise {
      if res is Nil {
        sk(i)
      } else {
        share_sregex__match_loop(ctx, car(res), i, i1 => seq_loop(cdr(res), i1), fk)
      }
    }
    seq_loop(cdr(re), i)
  } else if eq(op, share_sregex__k_or) {
    fn or_loop(res : Value) -> Value raise {
      if res is Nil {
        fk()
      } else {
        share_sregex__match_loop(
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
  } else if eq(op, share_sregex__k_backref) {
    let k = to_int(cadr(re))
    if k < 0 || k >= ctx.backrefs.length() {
      raise share_sregex__error(
        "pregexp-match-positions-aux: non-existent backref " + prin1_to_string(re),
      )
    }
    let backref = ctx.backrefs[k].1.val
    if backref.truthy() {
      let a = to_int(car(backref))
      let b = to_int(cdr(backref))
      share_sregex__string_match(s[a:b].to_array(), s, i, ctx.n, sk, fk)
    } else {
      sk(i)
    }
  } else if eq(op, share_sregex__k_sub) {
    share_sregex__match_loop(
      ctx,
      cadr(re),
      i,
      i1 => {
        for e in ctx.backrefs {
          if physical_equal_value(e.0, re) {
            e.1.val = cons(int(i), int(i1))
            break
          }
        }
        sk(i1)
      },
      fk,
    )
  } else if eq(op, share_sregex__k_lookahead) || eq(op, share_sregex__k_neg_lookahead) {
    let found_it_p = share_sregex__match_loop(ctx, cadr(re), i, i1 => int(i1), () => Nil)
    let pos = eq(op, share_sregex__k_lookahead)
    if found_it_p.truthy() == pos {
      sk(i)
    } else {
      fk()
    }
  } else if eq(op, share_sregex__k_lookbehind) || eq(op, share_sregex__k_neg_lookbehind) {
    let n_actual = ctx.n
    ctx.n = i
    let found_it_p = share_sregex__match_loop(
      ctx,
      list([
        share_sregex__k_seq,
        list([share_sregex__k_between, Nil, int(0), Nil, share_sregex__k_super_any]),
        cadr(re),
        share_sregex__k_eos,
      ]),
      ctx.start,
      i1 => int(i1),
      () => Nil,
    )
    ctx.n = n_actual
    let pos = eq(op, share_sregex__k_lookbehind)
    if found_it_p.truthy() == pos {
      sk(i)
    } else {
      fk()
    }
  } else if eq(op, share_sregex__k_no_backtrack) {
    let found_it_p = share_sregex__match_loop(ctx, cadr(re), i, i1 => int(i1), () => Nil)
    if found_it_p.truthy() {
      sk(to_int(found_it_p))
    } else {
      fk()
    }
  } else if eq(op, share_sregex__k_case_sensitive) ||
    eq(op, share_sregex__k_case_insensitive) {
    let old_case_sensitive_p = ctx.case_sensitive_p
    ctx.case_sensitive_p = eq(op, share_sregex__k_case_sensitive)
    share_sregex__match_loop(
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
  } else if eq(op, share_sregex__k_between) {
    let non_greedy_p = nth(1, re).truthy()
    let p = to_int(nth(2, re))
    let q0 = nth(3, re)
    let re = nth(4, re)
    let could_loop_infinitely_p = !non_greedy_p && q0 is Nil
    let q : Int? = if q0 is Nil { None } else { Some(to_int(q0) - p) }
    fn q_loop(k : Int, i : Int) -> Value raise {
      let fk = () => sk(i)
      match q {
        Some(qn) if k >= qn => return fk()
        _ => ()
      }
      if !non_greedy_p {
        share_sregex__match_loop(
          ctx,
          re,
          i,
          i1 => {
            if could_loop_infinitely_p && i1 == i {
              raise share_sregex__error(
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
          share_sregex__match_loop(ctx, re, i, i1 => q_loop(k + 1, i1), fk)
        }
      }
    }
    fn p_loop(k : Int, i : Int) -> Value raise {
      if k < p {
        share_sregex__match_loop(
          ctx,
          re,
          i,
          i1 => if could_loop_infinitely_p && i1 == i {
            raise share_sregex__error(
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
    raise share_sregex__error("pregexp-match-positions-aux")
  }
}

///|
fn share_sregex__match_positions_aux(
  re : Value,
  s : Array[Char],
  start : Int,
  n : Int,
  i : Int,
) -> Value raise {
  let ctx = {
    s,
    n,
    start,
    case_sensitive_p: true,
    backrefs: share_sregex__make_backref_list(re),
  }
  share_sregex__match_loop(ctx, re, i, i1 => int(i1), () => Nil) |> ignore
  let c = Collector::new()
  for e in ctx.backrefs {
    c.add(e.1.val)
  }
  let backrefs = c.result()
  if car(backrefs).truthy() {
    backrefs
  } else {
    Nil
  }
}

///|
fn share_sregex__pregexp(s : Value) -> Value raise {
  // in case it got corrupted
  share_sregex__space_sensitive_p.val = true
  let cs = share_stringproc__chars(s)
  list2(share_sregex__k_sub, share_sregex__read_pattern(cs, 0, cs.length()).0)
}

///|
fn share_sregex__match_positions(
  pat : Value,
  str : Value,
  start : Value,
  end : Value,
) -> Value raise {
  let pat = if stringp(pat) { share_sregex__pregexp(pat) } else { pat }
  if !consp(pat) {
    raise share_sregex__error(
      "pregexp-match-positions: pattern " + prin1_to_string(pat) +
      " must be compiled or string regexp",
    )
  }
  let s = share_stringproc__chars(str)
  let str_len = s.length()
  let start = if start is Nil { 0 } else { to_int(start) }
  let end = if end is Nil || to_int(end) > str_len { str_len } else { to_int(end) }
  let mut i = start
  while i <= end {
    let res = share_sregex__match_positions_aux(pat, s, start, end, i)
    if res.truthy() {
      return res
    }
    i += 1
  }
  Nil
}

///|
fn share_sregex__pregexp_match(
  pat : Value,
  str : Value,
  start : Value,
  end : Value,
) -> Value raise {
  let index_pairs = share_sregex__match_positions(pat, str, start, end)
  if index_pairs is Nil {
    return Nil
  }
  mapcar(
    index_pair => if index_pair.truthy() {
      share_stringproc__subseq(str, car(index_pair), cdr(index_pair))
    } else {
      Nil
    },
    index_pairs,
  )
}

///|
fn share_sregex__pregexp_split(pat : Value, str : Value) -> Value raise {
  let mut r : Value = Nil
  let n = string_length(lstring(str))
  let mut i = 0
  let mut picked_up_one_undelimited_char_p = false
  while true {
    if i >= n {
      return nreverse(r)
    }
    let it = car(share_sregex__match_positions(pat, str, int(i), int(n)))
    if it.truthy() {
      let j = to_int(car(it))
      let k = to_int(cdr(it))
      if j == k {
        r = cons(share_stringproc__subseq(str, int(i), int(j + 1)), r)
        i = k + 1
        picked_up_one_undelimited_char_p = true
      } else if j == i && picked_up_one_undelimited_char_p {
        i = k
        picked_up_one_undelimited_char_p = false
      } else {
        r = cons(share_stringproc__subseq(str, int(i), int(j)), r)
        i = k
        picked_up_one_undelimited_char_p = false
      }
    } else {
      r = cons(share_stringproc__subseq(str, int(i), int(n)), r)
      i = n
    }
  }
  Nil
}

///|
fn share_sregex__replace_aux(
  str : Value,
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
    let c = share_sregex__char(ins, i)
    i += 1
    if c == '\\' {
      let mut mi = share_sregex__read_escaped_number(ins, i, n)
      if mi is None && share_sregex__char(share_stringproc__chars(str), i) == '&' {
        mi = Some((int(0), i + 1))
      }
      match mi {
        Some((m, i1)) => {
          let backref = nth(to_int(m), backrefs)
          if backref.truthy() {
            sb.write_string(lstring(share_stringproc__subseq(str, car(backref), cdr(backref))))
          }
          i = i1
        }
        None => {
          let c2 = share_sregex__char(ins, i)
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

///|
fn share_sregex__pregexp_replace(pat : Value, str : Value, ins : Value) -> Value raise {
  let n = string_length(lstring(str))
  let pp = share_sregex__match_positions(pat, str, int(0), int(n))
  if pp is Nil {
    return str
  }
  let insc = share_stringproc__chars(ins)
  let m_i = caar(pp)
  let m_n = cdar(pp)
  Str(
    lstring(share_stringproc__subseq(str, int(0), m_i)) +
    share_sregex__replace_aux(str, insc, insc.length(), pp) +
    lstring(share_stringproc__subseq(str, m_n, int(n))),
  )
}

///|
fn share_sregex__pregexp_replace_star(
  pat : Value,
  str : Value,
  ins : Value,
) -> Value raise {
  let pat = if stringp(pat) { share_sregex__pregexp(pat) } else { pat }
  let n = string_length(lstring(str))
  let insc = share_stringproc__chars(ins)
  let mut i = 0
  let r = StringBuilder::new()
  while true {
    if i >= n {
      return Str(r.to_string())
    }
    let pp = share_sregex__match_positions(pat, str, int(i), int(n))
    if pp is Nil {
      return if i == 0 {
        // pat didn't match str at all: return original str
        str
      } else {
        Str(r.to_string() + lstring(share_stringproc__subseq(str, int(i), int(n))))
      }
    }
    r.write_string(lstring(share_stringproc__subseq(str, int(i), caar(pp))))
    r.write_string(share_sregex__replace_aux(str, insc, insc.length(), pp))
    i = to_int(cdar(pp))
  }
  Nil
}

///|
fn share_sregex__pregexp_quote(s : Value) -> Value raise {
  let cs = share_stringproc__chars(s)
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

// ---------------------------------------------------------------------------
// sregex

///|
/// (defstruct compiled-regex parse-tree pattern)
fn share_sregex__compiled_regex_p(x : Value) -> Bool {
  struct_typep(x, "compiled-regex")
}

///|
/// Include the pattern so the printed object is more meaningful.
fn compiled_regex_print(struct_ : Value, stream : Value, i : Value) -> Value raise {
  ignore(i)
  format(stream, "Structure [COMPILED-REGEX for ~S]", [struct_ref(struct_, 1)])
}

///|
fn d_regex_compile(regex : Value) -> Value raise {
  make_struct("compiled-regex", [share_sregex__pregexp(regex), regex])
}

///|
fn regex_check_and_maybe_coerce(name : Value, regex : Value, args : Value) -> Value raise {
  let mut regex = regex
  if share_sregex__compiled_regex_p(regex) {
    regex = struct_ref(regex, 0)
  } else if !stringp(regex) {
    gf_merror(
      Str("`~m': first arg must be a compiled regex or a string."),
      list([name]),
    )
    |> ignore
  }
  for a in args.iter() {
    if !stringp(a) {
      gf_merror(Str("Unsuitable arguments to `~m'."), list([name])) |> ignore
    }
  }
  regex
}

///|
fn regex_index_error(name : Value) -> Value raise {
  gf_merror(Str("`~m': improper start or end index."), list([name]))
}

///|
/// When the external format is not utf-8 (unicode) positions are counted
/// in octets; the decrement we need to find the character position.
fn regex_utf_8_pos_dec(ov : Value, off : Value, pos : Value) -> Value raise {
  let mut n = 0
  for i in to_int(off)..<to_int(pos) {
    if to_int(logand(aref1(ov, i), int(192))) == 128 {
      n += 1
    }
  }
  int(n)
}

///|
/// 1-based indexing!
fn d_regex_match_pos(
  regex : Value,
  str : Value,
  start? : Value = Fix(1L),
  end? : Value = Nil,
) -> Value raise {
  let regex = regex_check_and_maybe_coerce(
    Str("regex_match_pos"),
    regex,
    list1(str),
  )
  let mut start = num_sub(start, int(1))
  let mut end = if end.truthy() { num_sub(end, int(1)) } else { end }
  let mut ov : Value = Nil
  let r = errset(() => {
    if symval(q_ear_parse_utf_8_input).truthy() {
      ov = string_to_raw_bytes(str)
      let args = utf_8_fix_start_end(ov, list([Nil, start, end]))
      start = cadr(args)
      end = caddr(args)
    }
    let pos_list = share_sregex__match_positions(regex, str, start, end)
    if pos_list.truthy() {
      let c = Collector::new()
      for pos in pos_list.iter() {
        if symval(q_ear_parse_utf_8_input).truthy() {
          let dec = regex_utf_8_pos_dec(ov, int(0), car(pos))
          rplacd(
            pos,
            num_sub(cdr(pos), num_add(dec, regex_utf_8_pos_dec(ov, car(pos), cdr(pos)))),
          )
          |> ignore
          rplaca(pos, num_sub(car(pos), dec)) |> ignore
        }
        c.add(
          list3(
            list2(q_mlist, q_simp),
            num_add(car(pos), int(1)),
            num_add(cdr(pos), int(1)),
          ),
        )
      }
      cons(list2(q_mlist, q_simp), c.result())
    } else {
      // (return-from $regex_match_pos nil)
      Str("")
    }
  })
  match r {
    Some(Str("")) => Nil
    Some(v) if v.truthy() => v
    _ => regex_index_error(Str("regex_match_pos"))
  }
}

///|
fn d_regex_match(
  regex : Value,
  str : Value,
  start? : Value = Fix(1L),
  end? : Value = Nil,
) -> Value raise {
  let regex = regex_check_and_maybe_coerce(Str("regex_match"), regex, list1(str))
  let mut start = start
  let mut end = end
  let r = errset(() => {
    if symval(q_ear_parse_utf_8_input).truthy() {
      let ov = string_to_raw_bytes(str)
      let args = utf_8_fix_start_end(ov, list([Nil, start, end]))
      start = cadr(args)
      end = caddr(args)
    }
    let m = share_sregex__pregexp_match(
      regex,
      str,
      num_sub(start, int(1)),
      if end.truthy() {
        num_sub(end, int(1))
      } else {
        Nil
      },
    )
    if m.truthy() {
      cons(list2(q_mlist, q_simp), m)
    } else {
      // (return-from $regex_match nil)
      Str("")
    }
  })
  match r {
    Some(Str("")) => Nil
    Some(v) if v.truthy() => v
    _ => regex_index_error(Str("regex_match"))
  }
}

///|
fn d_regex_split(regex : Value, str : Value) -> Value raise {
  let regex = regex_check_and_maybe_coerce(Str("regex_split"), regex, list1(str))
  cons(list2(q_mlist, q_simp), share_sregex__pregexp_split(regex, str))
}

///|
fn d_regex_subst_first(replacement : Value, regex : Value, str : Value) -> Value raise {
  let regex = regex_check_and_maybe_coerce(
    Str("regex_subst_first"),
    regex,
    list2(str, replacement),
  )
  share_sregex__pregexp_replace(regex, str, replacement)
}

///|
/// Argument order different to the order of pregexp-replace: new, old,
/// str as in $ssubst.
fn d_regex_subst(replacement : Value, regex : Value, str : Value) -> Value raise {
  let regex = regex_check_and_maybe_coerce(
    Str("regex_subst"),
    regex,
    list2(str, replacement),
  )
  share_sregex__pregexp_replace_star(regex, str, replacement)
}

///|
fn d_string_to_regex(str : Value) -> Value raise {
  if !stringp(str) {
    gf_merror(Str("`string_to_regex': Argument must be a string."), Nil) |> ignore
  }
  share_sregex__pregexp_quote(str)
}
