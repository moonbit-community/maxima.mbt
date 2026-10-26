// Port of share/stringproc/printf.lisp: formatted printing to character
// streams.
//
// `$printf' is an interface to the Lisp function `format'. `$printf'
// provides a directive ~w,d,e,x,o,p@h to process bigfloat numbers.
// Arguments which are passed to d,f,e,g or h-directives are converted to
// that type. Before passing to `format' ctrls and args are both visited
// and modified: `prepare-ctrls' replaces the directive ~w,d,e,x,o,p@h by
// ~@a and `prepare-args' replaces the corresponding bigfloat argument by a
// string.
//
// The runtime `format' implements only a subset of CL FORMAT, so this file
// contains a private implementation of CL FORMAT following SBCL
// (src/code/target-format.lisp, and the float printing of
// src/code/print.lisp: FLONUM-TO-DIGITS, FLONUM-TO-STRING,
// FLONUM-EXPONENT), used by $printf. Pretty-printer directives (~<...~:>
// logical blocks, ~_, ~I, ~:T) are treated as their non-pretty
// equivalents; ~/name/ is not supported.

///|
/// This is an implementation of the formerly src/plot.lisp/$sprint as a
/// simple wrapper for printf(true,"~@{~a ~}",x,y,z,...) keeping the
/// original return value: the first argument resp. false.
fn d_sprint(args : Value) -> Value raise {
  for v in args.iter() {
    d_printf(t, Str("~a "), list1(v)) |> ignore
  }
  car(args)
}

///|
fn reconstitute_tilde_m(param : Value) -> Value raise {
  d_sconcat(list([Str("~"), param, Str("m")]))
}

///|
fn generate_tilde_m_placeholder() -> Value raise {
  let sb = StringBuilder::new()
  for _ in 1..=6 {
    let code = if eq(d_random(int(2)), int(0)) {
      num_add(d_random(int(92 - 33)), int(33))
    } else {
      num_add(d_random(int(126 - 93)), int(93))
    }
    sb.write_char(to_int(code).unsafe_to_char())
  }
  Str(sb.to_string())
}

///|
fn d_printf(stream : Value, ctrls : Value, args : Value) -> Value raise {
  if !(eq(stream, t) || stream is Nil) && !streamp(stream) {
    gf_merror(
      Str("`printf': first argument must be `true', `false' or a stream."),
      Nil,
    )
    |> ignore
  } else if !stringp(ctrls) {
    gf_merror(Str("`printf': second argument must be a string."), Nil) |> ignore
  }
  with_specials(
    [
      (q_ear_tilde_m_args, Nil),
      (q_ear_tilde_m_params, Nil),
      (q_ear_tilde_m_placeholders, Nil),
    ],
    () => {
      let args = prepare_args(ctrls, args, Nil)
      let body = list_to_array(args)
      let ctrls = prepare_ctrls(ctrls)
      if symval(q_ear_tilde_m_args).truthy() {
        // Capture output from FORMAT, and then call AFORMAT to handle ~M
        // directives.
        let first_pass = share_printf__format(Nil, lstring(ctrls), body)
        let second_pass = ssubst(Str("~~"), Str("~"), first_pass)
        let mut third_pass = second_pass
        // Substitute ~m directives back in.
        let mut ps = symval(q_ear_tilde_m_params)
        let mut hs = symval(q_ear_tilde_m_placeholders)
        while consp(ps) && consp(hs) {
          third_pass = ssubst(reconstitute_tilde_m(car(ps)), car(hs), third_pass)
          ps = cdr(ps)
          hs = cdr(hs)
        }
        aformat(stream, third_pass, reverse(symval(q_ear_tilde_m_args)))
      } else {
        // No ~m directives present, punt directly to FORMAT.
        share_printf__format(stream, lstring(ctrls), body)
      }
    },
  )
}

// -- string helpers on code points ----------------------------------------

///|
fn share_printf__len(s : Value) -> Int {
  string_length(lstring(s))
}

///|
/// (subseq s a b)
fn share_printf__sub(s : Value, a : Int, b? : Int) -> Value raise {
  share_stringproc__subseq(s, int(a), match b {
    Some(b) => int(b)
    None => Nil
  })
}

///|
/// (search needle hay :start2 start); with CI the test is char-equal.
fn share_printf__search(
  needle : Value,
  hay : Value,
  start? : Int = 0,
  ci? : Bool = false,
) -> Int? raise {
  let r = share_stringproc__search(
    share_stringproc__chars(needle),
    share_stringproc__chars(hay),
    if ci {
      q_d_sequalignore
    } else {
      q_d_sequal
    },
    int(start),
    Nil,
  )
  match r {
    Fix(n) => Some(n.to_int())
    _ => None
  }
}

///|
fn share_printf__in(spec : Value, set_ : String, ci? : Bool = false) -> Bool raise {
  share_printf__search(spec, Str(set_), ci~) is Some(_)
}

///|
/// (cdr x) of a list; a type error for other objects.
fn share_printf__cdr(x : Value) -> Value raise {
  if !listp(x) {
    raise LispError::SimpleError(
      "The value " + prin1_to_string(x) + " is not of type LIST",
    )
  }
  cdr(x)
}

///|
fn share_printf__parse_integer(s : Value) -> Value raise {
  let str = string_trim(" \t\n", lstring(s))
  match parse_integer(str) {
    Some(v) => v
    None =>
      raise LispError::SimpleError(
        "junk in string " + prin1_to_string(s),
      )
  }
}

///|
fn share_printf__digitcharp(s : Value) -> Bool raise {
  d_digitcharp(s).truthy()
}

///|
fn prepare_args(
  ctrls : Value,
  todo_ : Value,
  done : Value,
  loop_? : Value = Nil,
) -> Value raise {
  let mut ctrls = ctrls
  let mut todo = todo_
  let mut done = done
  let mut start = 0
  let mut pos1 : Int? = None
  let mut pos2 = 0
  let mut pos1a = 0
  let mut params : Value = Str("")
  let mut spec : Value = Str("")
  let mut subctrls : Value = Nil
  let mut skip = 0
  let mut loops : Value = Nil
  let mut index = 0
  let mut arg = car(todo)
  let tilde : Value = Str("~")
  while true {
    if todo is Nil {
      pos1 = share_printf__search(tilde, ctrls, start~)
      match pos1 {
        Some(p) => {
          pos2 = to_int(spec_position(ctrls, int(p)))
          spec = share_printf__sub(ctrls, pos2 - 1, b=pos2)
        }
        None => ()
      }
      // newline possible spec
      if skip == 0 &&
        (pos1 is None || share_printf__in(spec, "^{}[]<>%;&~tpTP\n")) {
        return reverse(done)
      } else {
        return gf_merror(Str("`printf': arguments exhausted."), Nil)
      }
    }
    // (prog () tag1 ... tag2 ... tag3 ... tag4)
    let mut lbl = 1
    while lbl != 0 {
      match lbl {
        1 => {
          // recognize the directive:
          pos1 = share_printf__search(tilde, ctrls, start~)
          if pos1 is None {
            if loop_.truthy() {
              start = 0
              pos1 = share_printf__search(tilde, ctrls, start~)
            } else {
              done = cons(arg, done)
              lbl = 3
              continue
            }
          }
          let p1 = match pos1 {
            Some(p) => p
            None =>
              raise LispError::SimpleError(
                "The value NIL is not of type (MOD 4611686018427387901)",
              )
          }
          pos2 = to_int(spec_position(ctrls, int(p1)))
          pos1a = pos2
          spec = share_printf__sub(ctrls, pos2 - 1, b=pos2)
          if share_printf__in(spec, "}]>;%&t~") {
            start = pos2
            lbl = 1
            continue
          }
          params = share_printf__sub(ctrls, p1 + 1, b=pos2 - 1)
          // pre-test for ~nr, ~vr, ~#r : check if radix is legal
          if string_equal(lstring(spec), "r") && lstring(params) != "" {
            let mut ch = share_printf__sub(params, 0, b=1)
            let mut n = ""
            let len = share_printf__len(params)
            if share_printf__digitcharp(ch) || share_printf__in(ch, "v#V") {
              let mut p = 1
              while !(p == len || share_printf__in(ch, ",@:v#V")) {
                n = n + lstring(ch)
                ch = share_printf__sub(params, p, b=p + 1)
                p += 1
              }
              let radix = if lstring(ch) == "," {
                int(10)
              } else if string_equal(lstring(ch), "v") {
                arg
              } else if lstring(ch) == "#" {
                int(length(todo))
              } else if lstring(ch) == "@" || lstring(ch) == ":" {
                share_printf__parse_integer(Str(n))
              } else {
                share_printf__parse_integer(Str(n + lstring(ch)))
              }
              if num_lt(radix, int(2)) || num_gt(radix, int(36)) {
                gf_merror(
                  Str("`printf': illegal radix in r-directive: ~m"),
                  list([radix]),
                )
                |> ignore
              }
            }
          }
          // handle some special directives:
          let mut handled = false
          if share_printf__in(spec, "abdefgorstx<~&%$", ci=true) {
            // ~v,v,v<spec>, spec=ABDEFGORSTX<~&%$
            skip = to_int(count_v(params))
            if skip > 0 {
              while skip != 0 {
                done = cons(
                  if stringp(arg) {
                    share_stringproc__chars(arg)[0] |> Value::Char
                  } else {
                    arg
                  },
                  done,
                )
                todo = cdr(todo)
                arg = car(todo)
                index += 1
                skip -= 1
              }
              done = cons(prepare_arg(params, spec, arg), done)
              lbl = 2
              continue
            }
          } else if string_equal(lstring(spec), "h") {
            // ~v,#,vH
            if check_v_hash(params).truthy() {
              let prms = split_at_comma(params)
              let mut new_params = ""
              for p in prms.iter() {
                let prm = if string_equal("v", lstring(p)) {
                  let r = d_sconcat(list1(arg))
                  todo = cdr(todo)
                  arg = car(todo)
                  index += 1
                  r
                } else if lstring(p) == "#" {
                  d_sconcat(list1(int(length(todo))))
                } else {
                  p
                }
                new_params = new_params + lstring(prm) + ","
              }
              done = cons(prepare_arg(Str(new_params), spec, arg), done)
              lbl = 2
              continue
            }
          } else if lstring(spec) == "[" {
            // ~@[, ~#[, ~n[
            let ps = lstring(params)
            if ps == "" {
              // don't check another condition
              ()
            } else if (ps == "@" && arg.truthy()) || ps == "#" {
              // if arg is not nil, arg is not consumed
              start = pos2
              lbl = 1
              continue
            } else if ps == "v" || string_chars(ps).iter().all(c => c >= '0' && c <= '9') {
              // 0- vs. 1-based indexing
              gf_merror(Str("`printf': not supported directive ~~~m["), list([params]))
              |> ignore
            }
          } else if lstring(spec) == "?" {
            // ~?
            let ps = lstring(params)
            if ps == "" {
              // arg is a string
              let ind_ctrls = arg
              done = cons(arg, done)
              todo = cdr(todo)
              arg = car(todo)
              done = cons(prepare_args(ind_ctrls, share_printf__cdr(arg), Nil, loop_=Nil), done)
              index += 1
              lbl = 2
              continue
            } else if ps == "@" {
              ctrls = Str(
                lstring(share_printf__sub(ctrls, 0, b=p1)) +
                lstring(arg) +
                lstring(share_printf__sub(ctrls, pos2)),
              )
              done = cons(arg, done)
              lbl = 3
              continue
            } else {
              gf_merror(Str("`printf': illegal directive ~~~m?"), list([params]))
              |> ignore
            }
          } else if lstring(spec) == "^" {
            // ~^
            if share_printf__search(Str("@"), params) is Some(_) {
              gf_merror(Str("`printf': illegal directive ~~~m^"), list([params]))
              |> ignore
            }
            skip = to_int(count_v(params))
            if skip > 0 {
              while skip != 0 {
                done = cons(
                  if stringp(arg) {
                    share_stringproc__chars(arg)[0] |> Value::Char
                  } else {
                    arg
                  },
                  done,
                )
                todo = cdr(todo)
                arg = car(todo)
                index += 1
                skip -= 1
              }
              done = cons(prepare_arg(params, spec, arg), done)
            }
            start = pos2
            lbl = 1
            continue
          } else if string_equal("p", lstring(spec)) &&
            share_printf__search(Str(":"), params) is Some(_) {
            // ~:P and ~:@P (':' backs up)
            start = pos2
            lbl = 1
            continue
          }
          ignore(handled)
          handled = true
          // default part: loop ...
          if lstring(spec) == "{" {
            // ~n{ and ~v{ etc. , set number of loops
            let ps = lstring(params)
            if ps != "" && ps != ":" && ps != "@" && ps != ":@" {
              let mut ch = share_printf__sub(params, 0, b=1)
              let mut n = ""
              let len = share_printf__len(params)
              let mut p = 1
              while true {
                if p == len || share_printf__in(ch, "@:v#V") {
                  params = if lstring(ch) == "@" || lstring(ch) == ":" {
                    share_printf__sub(params, p - 1)
                  } else {
                    share_printf__sub(params, p)
                  }
                  break
                }
                n = n + lstring(ch)
                ch = share_printf__sub(params, p, b=p + 1)
                p += 1
              }
              if loops is Nil {
                if string_equal(lstring(ch), "v") {
                  done = cons(arg, done)
                  index += 1
                  loops = arg
                  todo = cdr(todo)
                  arg = car(todo)
                } else if lstring(ch) == "#" {
                  loops = int(length(todo))
                } else if lstring(ch) == "@" || lstring(ch) == ":" {
                  loops = share_printf__parse_integer(Str(n))
                } else {
                  loops = share_printf__parse_integer(Str(n + lstring(ch)))
                }
              }
            }
            // ~{ and ~:{ and ~@{ and  ~:@{
            let ps = lstring(params)
            if ps == "" {
              pos2 = to_int(cadr(iter_positions(ctrls, int(p1))))
              subctrls = share_printf__sub(ctrls, pos1a, b=pos2 - 2)
              loops = Nil
              done = cons(prepare_args(subctrls, share_printf__cdr(arg), Nil, loop_=t), done)
            } else if ps == ":" {
              pos2 = to_int(cadr(iter_positions(ctrls, int(p1))))
              subctrls = Str("~{" + lstring(share_printf__sub(ctrls, pos1a, b=pos2)))
              loops = Nil
              done = cons(prepare_args(subctrls, share_printf__cdr(arg), Nil, loop_=t), done)
            } else if ps == "@" || ps == ":@" {
              pos2 = to_int(cadr(iter_positions(ctrls, int(p1))))
              subctrls = if ps == "@" {
                Str("~{" + lstring(share_printf__sub(ctrls, pos1a, b=pos2)))
              } else {
                Str(
                  "~" +
                  (if loops.truthy() {
                    lstring(d_sconcat(list1(loops)))
                  } else {
                    ""
                  }) +
                  ":{" +
                  lstring(share_printf__sub(ctrls, pos1a, b=pos2)),
                )
              }
              let items = if loops.truthy() {
                butlast(todo, n=(length(todo) - to_int(loops)).max(0))
              } else {
                todo
              }
              let prepared = car(
                prepare_args(subctrls, list1(cons(list1(q_mlist), items)), Nil, loop_=Nil),
              )
              done = append(reverse(prepared), done)
              todo = if loops.truthy() { nthcdr(to_int(loops), todo) } else { Nil }
              arg = car(todo)
              start = pos2
              if loops.truthy() {
                index += to_int(loops)
                loops = Nil
              }
              lbl = 0
              continue
            }
          } else {
            // ... or don't loop ...
            done = cons(prepare_arg(params, spec, arg), done)
          }
          lbl = 2
        }
        2 => {
          // ... set the position in ctrls ...
          start = pos2
          lbl = 3
        }
        _ => {
          // ... and take the next argument
          todo = cdr(todo)
          arg = car(todo)
          index += 1
          lbl = 0
        }
      }
    }
  }
  Nil
}

///|
fn prepare_ctrls(ctrls : Value) -> Value raise {
  let mut start = 0
  let mut pos2 = 0
  let mut new_ctrls = ""
  let tilde : Value = Str("~")
  // ~w,d,e,x,o,p@H
  let mut pos1 = share_printf__search(tilde, ctrls, start~)
  while true {
    let p1 = match pos1 {
      Some(p) => p
      None => return Str(new_ctrls + lstring(share_printf__sub(ctrls, pos2)))
    }
    pos2 = to_int(spec_position(ctrls, int(p1)))
    let spec = share_printf__sub(ctrls, pos2 - 1, b=pos2)
    new_ctrls = if string_equal(lstring(spec), "h") {
      new_ctrls + lstring(share_printf__sub(ctrls, start, b=p1)) + "~@a"
    } else if string_equal(lstring(spec), "m") {
      new_ctrls + lstring(share_printf__sub(ctrls, start, b=p1)) + "~a"
    } else {
      new_ctrls + lstring(share_printf__sub(ctrls, start, b=pos2))
    }
    start = pos2
    pos1 = share_printf__search(tilde, ctrls, start~)
  }
  Nil
}

///|
fn spec_position(ctrls : Value, pos1 : Value) -> Value raise {
  let mut p = to_int(pos1) + 1
  while true {
    if share_printf__in(
        share_printf__sub(ctrls, p, b=p + 1),
        "abcdefghmoprstx%{}^&$[]?~<>;ABCDEFGHMOPRSTX\n",
      ) &&
      lstring(share_printf__sub(ctrls, p - 1, b=p)) != "'" {
      return int(p + 1)
    }
    p += 1
  }
  Nil
}

///|
/// helper for ~v,v,v<spec>
fn count_v(params : Value) -> Value raise {
  if lstring(params) == "" {
    return int(0)
  }
  let len = share_printf__len(params)
  let mut n = 0
  for p in 0..<len {
    if string_equal("v", lstring(share_printf__sub(params, p, b=p + 1))) &&
      (p == 0 || lstring(share_printf__sub(params, p - 1, b=p)) != "'") {
      n += 1
    }
  }
  int(n)
}

///|
/// helper for ~v,#,vH
fn check_v_hash(params : Value) -> Value raise {
  if lstring(params) == "" {
    return Nil
  }
  let len = share_printf__len(params)
  for p in 0..<len {
    if share_printf__in(share_printf__sub(params, p, b=p + 1), "vV#") &&
      (p == 0 || lstring(share_printf__sub(params, p - 1, b=p)) != "'") {
      return t
    }
  }
  Nil
}

///|
/// find positions of matching braces
fn iter_positions(ctrls : Value, start : Value) -> Value raise {
  let mut end = to_int(start) + 2
  let mut n = 1
  while n != 0 {
    let pos1 = match share_printf__search(Str("~"), ctrls, start=end) {
      Some(p) => p
      None =>
        raise LispError::SimpleError(
          "The value NIL is not of type (MOD 4611686018427387901)",
        )
    }
    let pos2 = to_int(spec_position(ctrls, int(pos1)))
    let spec = share_printf__sub(ctrls, pos2 - 1, b=pos2)
    if lstring(spec) == "{" {
      n += 1
    }
    if lstring(spec) == "}" {
      n -= 1
    }
    end = pos2
  }
  list2(start, int(end))
}

///|
fn split_at_comma(params : Value) -> Value raise {
  let len = share_printf__len(params)
  let mut prms : Value = Nil
  let mut prm = ""
  for p in 0..<len {
    let c = lstring(share_printf__sub(params, p, b=p + 1))
    let prev_quote = p != 0 &&
      lstring(share_printf__sub(params, p - 1, b=p)) == "'"
    if (c == "," || c == "@") && !prev_quote {
      prms = cons(Str(prm), prms)
      prm = ""
    } else if c == "," && prev_quote {
      prms = cons(Str(","), prms)
      prm = ""
    } else if c == "'" {
      ()
    } else {
      prm = prm + c
    }
  }
  reverse(cons(Str(prm), prms))
}

///|
fn prepare_arg(params : Value, spec : Value, arg : Value) -> Value raise {
  let mut arg = arg
  let sp = lstring(spec)
  if string_equal("h", sp) {
    // ~w,d,e,x,o,p@H
    if !bigfloatp(arg).truthy() {
      if d_numberp(arg).truthy() {
        // Maxima rational, float
        arg = d_bfloat(arg)
      } else if d_constantp(arg).truthy() &&
        d_freeof(list2(q_d__pcti, arg)).truthy() &&
        !(eq(arg, t) || arg is Nil) &&
        !d_listp(arg).truthy() {
        // %pi, sqrt(2), ...
        arg = d_bfloat(arg)
      } else {
        gf_merror(
          Str("`printf': argument can't be supplied to h-directive: ~m"),
          list([arg]),
        )
        |> ignore
      }
    }
    let prms = split_at_comma(params)
    let wd = nth(0, prms)
    let dd = nth(1, prms)
    let ed = nth(2, prms)
    let xp = nth(3, prms)
    let ov = nth(4, prms)
    let pc = nth(5, prms)
    let smarap = string_chars(lstring(params))
    smarap.rev_in_place()
    let at = if smarap.length() > 0 &&
      smarap[0] == '@' &&
      (smarap.length() == 1 || smarap[1] != '\'') {
      t
    } else {
      Nil
    }
    let num = fn(x : Value) raise {
      if x.truthy() && lstring(x) != "" {
        share_printf__parse_integer(x)
      } else {
        Nil
      }
    }
    arg = bprintf(arg, num(wd), num(dd), num(ed), num(xp), ov, pc, at)
  } else if share_printf__in(spec, "efg", ci=true) {
    // ~E, ~F, ~G
    if !floatp(arg) {
      if d_numberp(arg).truthy() {
        // Maxima rational, bigfloat
        arg = d_float(arg)
      } else if d_constantp(arg).truthy() &&
        !(eq(arg, t) || arg is Nil) &&
        !d_listp(arg).truthy() &&
        {
          let would_be_arg = d_float(arg)
          if d_numberp(would_be_arg).truthy() {
            arg = would_be_arg
            true
          } else {
            false
          }
        } {
        ()
      } else {
        gf_merror(
          Str("`printf': argument can't be supplied to ~m-directive: ~m"),
          list([spec, arg]),
        )
        |> ignore
      }
    }
  } else if string_equal("d", sp) {
    // ~D
    if !integerp(arg) {
      if d_numberp(arg).truthy() {
        // Maxima rational, (big)float
        arg = ftake(q_p_truncate, [arg])
      } else if d_constantp(arg).truthy() &&
        d_freeof(list2(q_d__pcti, arg)).truthy() &&
        !(eq(arg, t) || arg is Nil) &&
        !d_listp(arg).truthy() {
        // %pi, sqrt(2), ...
        arg = ftake(q_p_truncate, [arg])
      } else {
        gf_merror(
          Str("`printf': argument can't be supplied to d-directive: ~m"),
          list([arg]),
        )
        |> ignore
      }
    }
  } else if share_printf__in(spec, "as", ci=true) {
    // ~A, ~S
    arg = d_sconcat(list1(arg))
  } else if string_equal("c", sp) {
    // ~C: conversion to Lisp char
    arg = match arg {
      Char(_) => arg
      Str(_) =>
        match share_stringproc__chars(arg) {
          [c] => Char(c)
          _ =>
            raise LispError::SimpleError(
              "The value " + prin1_to_string(arg) + " is not of type CHARACTER",
            )
        }
      Sym(_) =>
        match string_chars(invert_case(symbol_name(arg))) {
          [c] => Char(c)
          _ =>
            raise LispError::SimpleError(
              "The value " + prin1_to_string(arg) + " is not of type CHARACTER",
            )
        }
      _ =>
        raise LispError::SimpleError(
          "The value " + prin1_to_string(arg) + " is not of type CHARACTER",
        )
    }
  } else if string_equal("m", sp) {
    // ~M
    set(q_ear_tilde_m_args, cons(arg, symval(q_ear_tilde_m_args))) |> ignore
    set(q_ear_tilde_m_params, cons(params, symval(q_ear_tilde_m_params)))
    |> ignore
    let placeholder = generate_tilde_m_placeholder()
    set(
      q_ear_tilde_m_placeholders,
      cons(placeholder, symval(q_ear_tilde_m_placeholders)),
    )
    |> ignore
    arg = placeholder
  } else if sp == "[" {
    // ~[ : 1-based indexing!
    if !(lstring(params) == "@" || lstring(params) == ":") {
      if integerp(arg) {
        arg = num_sub(arg, int(1))
      }
    }
  }
  arg
}

///|
/// bf: bigfloat; wd: nil or width; dd: nil or decimal digits behind
/// floating point; ed: nil or minimal exponent digits; xp: nil or
/// preferred exponent; ov: nil or overflow character; pc: nil or padding
/// character; at: nil or true; sets "+" if true.  ~w,d,e,x,o,p@H
fn bprintf(
  bf : Value,
  wd : Value,
  dd : Value,
  ed : Value,
  xp : Value,
  ov : Value,
  pc : Value,
  at : Value,
) -> Value raise {
  let ms = fn(len : Int, c : Char) { c.to_string().repeat(len.max(0)) }
  let mut bf = bf
  let mut xp = xp
  // keep old fpprec in case it differs to current fpprec
  with_special(q_fpprec, caddr(car(bf)), () => {
    if xp.truthy() && !zerop(xp) {
      bf = bcons(
        if minusp(xp) {
          fptimes_star(cdr(bf), intofp(expt(int(10), num_neg(xp))))
        } else {
          fpquotient(cdr(bf), intofp(expt(int(10), xp)))
        },
      )
    }
    if dd.truthy() {
      let m = intofp(expt(int(10), dd))
      let b1 = fptimes_star(cdr(bf), m)
      let b2 = meval(list2(list1(q_p_round), bcons(b1)))
      bf = bcons(fpquotient(intofp(b2), m))
    }
    Value::Nil
  })
  |> ignore
  let s0 = string_left_trim("-", lstring(d_sconcat(list1(bf))))
  let sgn = to_int(signum(cadr(bf)))
  let sc = string_chars(s0)
  let part1 = chars_to_string(sc[0:1].to_array())
  let pos = {
    let mut r = -1
    for i, c in sc {
      if c == 'b' {
        r = i
        break
      }
    }
    r
  }
  let part2 = string_right_trim("0", chars_to_string(sc[2:pos].to_array()))
  let mut len = string_length(part2)
  let mut pow = to_int(
    share_printf__parse_integer(Str(chars_to_string(sc[pos + 1:].to_array()))),
  )
  let dd_ = if dd.truthy() { Some(to_int(dd)) } else { None }
  let mut s = ""
  let p2c = string_chars(part2)
  if pow > 0 && len > pow {
    s = part1 +
      chars_to_string(p2c[0:pow].to_array()) +
      "." +
      chars_to_string(p2c[pow:].to_array())
    match dd_ {
      Some(d) if d + pow > len => s = s + ms(d + pow - len, '0')
      _ => ()
    }
  } else if pow > 0 {
    s = part1 + part2 + ms(pow - len, '0') + ".0"
    match dd_ {
      Some(d) if d > 0 => s = s + ms(d - 1, '0')
      _ => ()
    }
  } else if pow == 0 {
    s = part1 + (if len == 0 { ".0" } else { "." }) + part2
    if len == 0 {
      len += 1
    }
    match dd_ {
      Some(d) if d > len => s = s + ms(d - len, '0')
      _ => ()
    }
  } else {
    pow = -pow
    s = "0." + ms(pow - 1, '0') + part1 + part2
    match dd_ {
      Some(d) if d > len + pow => s = s + ms(d - pow - len, '0')
      _ => ()
    }
  }
  match dd_ {
    Some(0) => s = string_right_trim("0", s)
    _ => ()
  }
  if sgn < 0 {
    s = "-" + s
  } else if at.truthy() {
    s = "+" + s
  }
  if ed.truthy() || xp.truthy() {
    if xp is Nil {
      xp = int(0)
    }
    let mut xps = lstring(mfuncall(q_d_string, list1(xp)))
    if minusp(xp) {
      xps = xps.substring(start=1)
    }
    let xpl = string_length(xps)
    if ed.truthy() && to_int(ed) > xpl {
      xps = ms(to_int(ed) - xpl, '0') + xps
    }
    s = s + "b" + (if minusp(xp) { "-" } else { "+" }) + xps
  }
  let len = string_length(s)
  if wd.truthy() && ov.truthy() && share_printf__len(ov) == 1 && len > to_int(wd) {
    s = ms(to_int(wd), share_stringproc__chars(ov)[0])
  }
  if wd.truthy() && to_int(wd) > len {
    let pcc = if pc.truthy() { share_stringproc__chars(pc)[0] } else { ' ' }
    s = ms(to_int(wd) - len, pcc) + s
  }
  Str(s)
}

// ===========================================================================
// CL FORMAT (SBCL semantics)

///|
priv suberror SharePrintfEscape {
  /// ~^ : throw 'up-and-out
  UpAndOut
  /// ~:^ : throw 'up-up-and-out
  UpUpAndOut
}

///|
priv enum SharePrintfRaw {
  RNone
  RInt(Int)
  RChar(Char)
  RArg
  RRemaining
}

///|
priv struct SharePrintfDir {
  next : Int
  params : Array[SharePrintfRaw]
  colon : Bool
  at : Bool
  /// the directive character (lower case)
  ch : Char
}

///|
/// Output with column tracking (SBCL charpos).
priv struct SharePrintfOut {
  sb : StringBuilder
  mut col : Int
}

///|
fn SharePrintfOut::put(self : SharePrintfOut, s : String) -> Unit {
  for c in s {
    if c == '\n' {
      self.col = 0
    } else {
      self.col += 1
    }
  }
  self.sb.write_string(s)
}

///|
fn SharePrintfOut::putc(self : SharePrintfOut, c : Char) -> Unit {
  if c == '\n' {
    self.col = 0
  } else {
    self.col += 1
  }
  self.sb.write_char(c)
}

///|
fn SharePrintfOut::putn(self : SharePrintfOut, n : Int, c : Char) -> Unit {
  for _ in 0..<n {
    self.putc(c)
  }
}

///|
/// The state of one argument list.
priv struct SharePrintfArgs {
  all : Array[Value]
  mut i : Int
  /// inside ~:{ : are the outside args (remaining sublists) empty?
  outside_empty : Bool?
}

///|
fn SharePrintfArgs::next(self : SharePrintfArgs) -> Value raise {
  if self.i >= self.all.length() {
    raise LispError::SimpleError("format error: No more arguments")
  }
  let v = self.all[self.i]
  self.i += 1
  v
}

///|
fn SharePrintfArgs::remaining(self : SharePrintfArgs) -> Int {
  self.all.length() - self.i
}

///|
fn share_printf__error(msg : String) -> LispError {
  LispError::SimpleError("format error: " + msg)
}

///|
/// Parse the directive starting at the ~ at index i.
fn share_printf__parse_dir(ctl : Array[Char], i : Int) -> SharePrintfDir raise {
  let n = ctl.length()
  let mut j = i + 1
  let params : Array[SharePrintfRaw] = []
  while true {
    if j >= n {
      raise share_printf__error("String ended before directive was found")
    }
    let c = ctl[j]
    let mut p : SharePrintfRaw? = None
    if (c >= '0' && c <= '9') ||
      ((c == '+' || c == '-') && j + 1 < n && ctl[j + 1] >= '0' && ctl[j + 1] <= '9') {
      let sb = StringBuilder::new()
      sb.write_char(c)
      j += 1
      while j < n && ctl[j] >= '0' && ctl[j] <= '9' {
        sb.write_char(ctl[j])
        j += 1
      }
      let s = sb.to_string()
      let v = parse_integer(if s.has_prefix("+") { s.substring(start=1) } else { s })
      p = Some(
        match v {
          Some(Fix(k)) => RInt(k.to_int())
          _ => raise share_printf__error("parameter too large")
        },
      )
    } else if c == '\'' {
      if j + 1 >= n {
        raise share_printf__error("String ended before directive was found")
      }
      p = Some(RChar(ctl[j + 1]))
      j += 2
    } else if c == 'v' || c == 'V' {
      p = Some(RArg)
      j += 1
    } else if c == '#' {
      p = Some(RRemaining)
      j += 1
    }
    if j < n && ctl[j] == ',' {
      params.push(p.unwrap_or(RNone))
      j += 1
      continue
    }
    match p {
      Some(x) => params.push(x)
      None => ()
    }
    break
  }
  let mut colon = false
  let mut at = false
  while j < n && (ctl[j] == ':' || ctl[j] == '@') {
    if ctl[j] == ':' {
      colon = true
    } else {
      at = true
    }
    j += 1
  }
  if j >= n {
    raise share_printf__error("String ended before directive was found")
  }
  let ch = ctl[j]
  let ch = if ch.to_int() < 128 { char_downcase(ch) } else { ch }
  { next: j + 1, params, colon, at, ch }
}

///|
/// Find the directive closing the construct opened before index FROM.
/// Returns the separators ~; (with their start index) and the closing
/// directive with its start index.
fn share_printf__find_close(
  ctl : Array[Char],
  from : Int,
  close : Char,
) -> (Array[(Int, SharePrintfDir)], Int, SharePrintfDir) raise {
  let seps : Array[(Int, SharePrintfDir)] = []
  let mut i = from
  while i < ctl.length() {
    if ctl[i] != '~' {
      i += 1
      continue
    }
    let d = share_printf__parse_dir(ctl, i)
    match d.ch {
      '(' | '[' | '{' | '<' => {
        let c = match d.ch {
          '(' => ')'
          '[' => ']'
          '{' => '}'
          _ => '>'
        }
        let (_, _, cd) = share_printf__find_close(ctl, d.next, c)
        i = cd.next
        continue
      }
      ')' | ']' | '}' | '>' =>
        if d.ch == close {
          return (seps, i, d)
        } else {
          raise share_printf__error("No matching closing directive")
        }
      ';' => seps.push((i, d))
      _ => ()
    }
    i = d.next
  }
  raise share_printf__error(
    "No corresponding close directive " + close.to_string(),
  )
}

///|
/// Resolve the parameters of a directive (v consumes an argument, #
/// counts the remaining ones).
fn share_printf__params(d : SharePrintfDir, a : SharePrintfArgs) -> Array[Value?] raise {
  let r : Array[Value?] = []
  for p in d.params {
    r.push(
      match p {
        RNone => None
        RInt(n) => Some(int(n))
        RChar(c) => Some(Char(c))
        RArg => {
          let v = a.next()
          if v is Nil {
            None
          } else {
            Some(v)
          }
        }
        RRemaining => Some(int(a.remaining()))
      },
    )
  }
  r
}

///|
fn share_printf__pint(p : Array[Value?], i : Int, default : Int?) -> Int? raise {
  match p.get(i) {
    Some(Some(Fix(n))) => Some(n.to_int())
    Some(Some(v)) =>
      raise share_printf__error(
        "The value " + prin1_to_string(v) + " is not of type INTEGER",
      )
    _ => default
  }
}

///|
fn share_printf__pchar(p : Array[Value?], i : Int, default : Char?) -> Char? raise {
  match p.get(i) {
    Some(Some(Char(c))) => Some(c)
    Some(Some(v)) =>
      raise share_printf__error(
        "The value " + prin1_to_string(v) + " is not of type CHARACTER",
      )
    _ => default
  }
}

///|
fn share_printf__max_params(p : Array[Value?], n : Int) -> Unit raise {
  if p.length() > n {
    raise share_printf__error(
      "Too many parameters, expected no more than \{n}",
    )
  }
}

// -- printing objects ------------------------------------------------------

///|
fn share_printf__princ(v : Value, base? : Int = 10) -> String {
  match v {
    Str(s) => s
    Char(c) => c.to_string()
    Fix(_) | Big(_) =>
      string_upcase(
        (try to_big(v) catch { _ => 0N }).to_string(radix=base),
      )
    Flo(d) => float_to_string(d)
    Nil => "NIL"
    Sym(s) =>
      if s.name == "t" {
        "T"
      } else {
        invert_case(s.name)
      }
    Cons(_) => {
      let sb = StringBuilder::new()
      sb.write_char('(')
      let mut l = v
      let mut first = true
      while true {
        match l {
          Cons(c) => {
            if !first {
              sb.write_char(' ')
            }
            first = false
            sb.write_string(share_printf__princ(c.car, base~))
            l = c.cdr
          }
          Nil => break
          _ => {
            sb.write_string(" . ")
            sb.write_string(share_printf__princ(l, base~))
            break
          }
        }
      }
      sb.write_char(')')
      sb.to_string()
    }
    _ => princ_to_string(v)
  }
}

///|
/// SBCL names of the non-graphic characters below 160.
fn share_printf__char_name(c : Char) -> String? {
  let n = c.to_int()
  let names = [
    "Nul", "Soh", "Stx", "Etx", "Eot", "Enq", "Ack", "Bel", "Backspace", "Tab", "Newline",
    "Vt", "Page", "Return", "So", "Si", "Dle", "Dc1", "Dc2", "Dc3", "Dc4", "Nak", "Syn",
    "Etb", "Can", "Em", "Sub", "Esc", "Fs", "Gs", "Rs", "Us",
  ]
  if n < 32 {
    Some(names[n])
  } else if n == 32 {
    Some("Space")
  } else if n == 127 {
    Some("Rubout")
  } else if n >= 128 && n < 160 {
    Some("U+" + string_upcase(n.to_string(radix=16)))
  } else {
    None
  }
}

///|
fn share_printf__prin1(v : Value) -> String {
  match v {
    Str(s) => {
      let sb = StringBuilder::new()
      sb.write_char('"')
      for c in s {
        if c == '"' || c == '\\' {
          sb.write_char('\\')
        }
        sb.write_char(c)
      }
      sb.write_char('"')
      sb.to_string()
    }
    Char(c) =>
      "#\\" +
      (match share_printf__char_name(c) {
        Some(nm) => nm
        None => c.to_string()
      })
    Cons(_) => {
      let sb = StringBuilder::new()
      sb.write_char('(')
      let mut l = v
      let mut first = true
      while true {
        match l {
          Cons(c) => {
            if !first {
              sb.write_char(' ')
            }
            first = false
            sb.write_string(share_printf__prin1(c.car))
            l = c.cdr
          }
          Nil => break
          _ => {
            sb.write_string(" . ")
            sb.write_string(share_printf__prin1(l))
            break
          }
        }
      }
      sb.write_char(')')
      sb.to_string()
    }
    _ => share_printf__princ(v)
  }
}

///|
fn share_printf__write_field(
  out : SharePrintfOut,
  s : String,
  mincol : Int,
  colinc : Int,
  minpad : Int,
  padchar : Char,
  padleft : Bool,
) -> Unit raise {
  if colinc <= 0 {
    raise share_printf__error("colinc should be a positive integer")
  }
  if mincol < 0 {
    raise share_printf__error("mincol should be a non-negative integer")
  }
  if !padleft {
    out.put(s)
  }
  out.putn(minpad, padchar)
  let mut chars = string_length(s) + minpad.max(0)
  while chars < mincol {
    out.putn(colinc, padchar)
    chars += colinc
  }
  if padleft {
    out.put(s)
  }
}

///|
fn share_printf__add_commas(s : String, commachar : Char, interval : Int) -> String {
  let cs = string_chars(s)
  let l = cs.length()
  let commas = (l - 1) / interval
  let extra = (l - 1) % interval
  ignore(commas)
  let sb = StringBuilder::new()
  let first = extra + 1
  for i in 0..<first.min(l) {
    sb.write_char(cs[i])
  }
  let mut src = first
  while src < l {
    sb.write_char(commachar)
    for k in src..<(src + interval).min(l) {
      sb.write_char(cs[k])
    }
    src += interval
  }
  sb.to_string()
}

///|
fn share_printf__print_integer(
  out : SharePrintfOut,
  number : Value,
  commas : Bool,
  sign : Bool,
  radix : Int,
  mincol : Int,
  padchar : Char,
  commachar : Char,
  interval : Int,
) -> Unit raise {
  if integerp(number) {
    let text = share_printf__princ(num_abs(number), base=radix)
    let commaed = if commas {
      share_printf__add_commas(text, commachar, interval)
    } else {
      text
    }
    let signed = if minusp(number) {
      "-" + commaed
    } else if sign {
      "+" + commaed
    } else {
      commaed
    }
    share_printf__write_field(out, signed, mincol, 1, 0, padchar, true)
  } else {
    out.put(share_printf__princ(number, base=radix))
  }
}

// -- English and Roman numbers -----------------------------------------------

///|
let share_printf__ones : Array[String] = [
  "", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
]

///|
let share_printf__tens : Array[String] = [
  "", "", "twenty", "thirty", "forty", "fifty", "sixty", "seventy", "eighty", "ninety",
]

///|
let share_printf__teens : Array[String] = [
  "ten", "eleven", "twelve", "thirteen", "fourteen", "fifteen", "sixteen", "seventeen",
  "eighteen", "nineteen",
]

///|
let share_printf__ordinal_ones : Array[String] = [
  "", "first", "second", "third", "fourth", "fifth", "sixth", "seventh", "eighth", "ninth",
]

///|
let share_printf__ordinal_tens : Array[String] = [
  "", "tenth", "twentieth", "thirtieth", "fortieth", "fiftieth", "sixtieth", "seventieth",
  "eightieth", "ninetieth",
]

///|
let share_printf__periods : Array[String] = [
  "", " thousand", " million", " billion", " trillion", " quadrillion", " quintillion",
  " sextillion", " septillion", " octillion", " nonillion", " decillion", " undecillion",
  " duodecillion", " tredecillion", " quattuordecillion", " quindecillion", " sexdecillion",
  " septendecillion", " octodecillion", " novemdecillion", " vigintillion",
]

///|
fn share_printf__small_cardinal(out : SharePrintfOut, n : Int) -> Unit {
  let hundreds = n / 100
  let rem = n % 100
  if hundreds > 0 {
    out.put(share_printf__ones[hundreds])
    out.put(" hundred")
    if rem > 0 {
      out.putc(' ')
    }
  }
  if rem > 0 {
    let tens = rem / 10
    let ones = rem % 10
    if tens > 1 {
      out.put(share_printf__tens[tens])
      if ones > 0 {
        out.putc('-')
        out.put(share_printf__ones[ones])
      }
    } else if tens == 1 {
      out.put(share_printf__teens[ones])
    } else if ones > 0 {
      out.put(share_printf__ones[ones])
    }
  }
}

///|
fn share_printf__cardinal_aux(
  out : SharePrintfOut,
  n : BigInt,
  period : Int,
  err : Value,
) -> Unit raise {
  let thousand = BigInt::from_int(1000)
  let beyond = n / thousand
  let here = (n % thousand).to_int()
  if period > 21 {
    raise share_printf__error(
      "Number too large to print in English: " + share_printf__princ(err),
    )
  }
  if !beyond.is_zero() {
    share_printf__cardinal_aux(out, beyond, period + 1, err)
  }
  if here != 0 {
    if !beyond.is_zero() {
      out.putc(' ')
    }
    share_printf__small_cardinal(out, here)
    out.put(share_printf__periods[period])
  }
}

///|
fn share_printf__cardinal(out : SharePrintfOut, n : Value) -> Unit raise {
  let b = to_big(n)
  if b < 0N {
    out.put("negative ")
    share_printf__cardinal_aux(out, -b, 0, n)
  } else if b.is_zero() {
    out.put("zero")
  } else {
    share_printf__cardinal_aux(out, b, 0, n)
  }
}

///|
fn share_printf__ordinal(out : SharePrintfOut, n : Value) -> Unit raise {
  if minusp(n) {
    out.put("negative ")
  }
  let number = to_big(num_abs(n))
  let hundred = BigInt::from_int(100)
  let top = number / hundred
  let bot = (number % hundred).to_int()
  if !top.is_zero() {
    share_printf__cardinal(out, from_big(number - BigInt::from_int(bot)))
  }
  if top > 0N && bot > 0 {
    out.putc(' ')
  }
  let tens = bot / 10
  let ones = bot % 10
  if bot == 12 {
    out.put("twelfth")
  } else if tens == 1 {
    out.put(share_printf__teens[ones])
    out.put("th")
  } else if tens == 0 && ones > 0 {
    out.put(share_printf__ordinal_ones[ones])
  } else if ones == 0 && tens > 0 {
    out.put(share_printf__ordinal_tens[tens])
  } else if bot > 0 {
    out.put(share_printf__tens[tens])
    out.putc('-')
    out.put(share_printf__ordinal_ones[ones])
  } else if number > 0N {
    out.put("th")
  } else {
    out.put("zeroth")
  }
}

///|
fn share_printf__old_roman(out : SharePrintfOut, n : Value) -> Unit raise {
  if !(num_gt(n, int(0)) && num_lt(n, int(5000))) {
    raise share_printf__error(
      "Number too large to print in old Roman numerals: " + share_printf__princ(n),
    )
  }
  let mut i = to_int(n)
  for p in [('M', 1000), ('D', 500), ('C', 100), ('L', 50), ('X', 10), ('V', 5), ('I', 1)] {
    while i >= p.1 {
      out.putc(p.0)
      i -= p.1
    }
  }
}

///|
fn share_printf__roman(out : SharePrintfOut, n : Value) -> Unit raise {
  if !(num_gt(n, int(0)) && num_lt(n, int(4000))) {
    raise share_printf__error(
      "Number too large to print in Roman numerals: " + share_printf__princ(n),
    )
  }
  let mut i = to_int(n)
  let levels = [
    ('M', 1000, 'C', 100),
    ('D', 500, 'C', 100),
    ('C', 100, 'X', 10),
    ('L', 50, 'X', 10),
    ('X', 10, 'I', 1),
    ('V', 5, 'I', 1),
    ('I', 1, ' ', 0),
  ]
  for lv in levels {
    if i == 0 {
      break
    }
    let (ch, v, sub, subv) = lv
    while i >= v {
      out.putc(ch)
      i -= v
    }
    if subv > 0 && v - subv <= i {
      out.putc(sub)
      out.putc(ch)
      i -= v - subv
    }
  }
}

// -- floats (SBCL FLONUM-TO-DIGITS / FLONUM-TO-STRING) ----------------------

///|
/// (integer-decode-float x) of a double, or of x coerced to single-float.
fn share_printf__decode(x : Double, single : Bool) -> (BigInt, Int) {
  if single {
    let bits = Float::from_double(x).reinterpret_as_uint()
    let ex = ((bits >> 23) & 0xffU).reinterpret_as_int()
    let mant = (bits & 0x7fffffU).reinterpret_as_int()
    if ex == 0 {
      (BigInt::from_int(mant), -149)
    } else {
      (BigInt::from_int(mant | 0x800000), ex - 150)
    }
  } else {
    let bits = x.reinterpret_as_uint64()
    let ex = ((bits >> 52) & 0x7ffUL).to_int()
    let mant = bits & 0xfffffffffffffUL
    if ex == 0 {
      (BigInt::from_uint64(mant), -1074)
    } else {
      (BigInt::from_uint64(mant | 0x10000000000000UL), ex - 1075)
    }
  }
}

///|
fn share_printf__pow(b : Int, n : Int) -> BigInt {
  BigInt::from_int(b).pow(BigInt::from_int(n))
}

///|
fn share_printf__integer_length(f : BigInt) -> Int {
  let mut n = 0
  let mut x = f
  let two = BigInt::from_int(2)
  while x > 0N {
    x = x / two
    n += 1
  }
  n
}

///|
/// The digit generation loop of %FLONUM-TO-DIGITS.
fn share_printf__generate(
  r0 : BigInt,
  s : BigInt,
  mp0 : BigInt,
  mm0 : BigInt,
  high_ok : Bool,
  low_ok : Bool,
) -> String raise {
  let sb = StringBuilder::new()
  let ten = BigInt::from_int(10)
  let mut r = r0
  let mut mp = mp0
  let mut mm = mm0
  while true {
    let r10 = r * ten
    let d = (r10 / s).to_int()
    r = r10 % s
    mp = mp * ten
    mm = mm * ten
    let tc1 = r < mm || (low_ok && r == mm)
    let tc2 = r + mp > s || (high_ok && r + mp == s)
    if !(tc1 || tc2) {
      sb.write_char((48 + d).unsafe_to_char())
      continue
    }
    let d = if !tc1 && tc2 {
      d + 1
    } else if tc1 && !tc2 {
      d
    } else if r * BigInt::from_int(2) < s {
      d
    } else {
      d + 1
    }
    if d > 9 {
      raise LispError::SimpleError("Invalid index 10 for (SIMPLE-STRING 10)")
    }
    sb.write_char((48 + d).unsafe_to_char())
    break
  }
  sb.to_string()
}

///|
/// SBCL FLONUM-TO-DIGITS: (k, digits) with x = 0.digits * 10^k.
fn share_printf__flonum_to_digits(
  x : Double,
  single : Bool,
  position? : Int? = None,
  relativep? : Bool = false,
) -> (Int, String) raise {
  if x == 0.0 {
    return (0, "0")
  }
  let (f, e) = share_printf__decode(x, single)
  let p = if single { 24 } else { 53 }
  let min_e = if single { -148 } else { -1073 }
  let mut high_ok = f % BigInt::from_int(2) == 0N
  let mut low_ok = high_ok
  let hidden = share_printf__pow(2, p - 1)
  let (r0, s0, mp0, mm0) = if e >= 0 {
    let be = share_printf__pow(2, e)
    if f != hidden {
      (f * share_printf__pow(2, e + 1), BigInt::from_int(2), be, be)
    } else {
      (f * share_printf__pow(2, e + 2), BigInt::from_int(4), share_printf__pow(2, e + 1), be)
    }
  } else if e == min_e || f != hidden {
    (f * BigInt::from_int(2), share_printf__pow(2, 1 - e), 1N, 1N)
  } else {
    (f * BigInt::from_int(4), share_printf__pow(2, 2 - e), 2N, 1N)
  }
  let mut r = r0
  let mut s = s0
  let mut mp = mp0
  let mut mm = mm0
  let ten = BigInt::from_int(10)
  match position {
    None => {
      // scale: estimate k with a logarithm, then fixup
      let log10_2 = 0.30102999566398114
      let eps = (1.0e-10 : Float).to_double()
      let est = ((e + share_printf__integer_length(f) - 1).to_double() * log10_2 - eps).ceil().to_int()
      if est >= 0 {
        s = s * share_printf__pow(10, est)
      } else {
        let sc = share_printf__pow(10, -est)
        r = r * sc
        mp = mp * sc
        mm = mm * sc
      }
      let mut k = est
      if (high_ok && r + mp >= s) || (!high_ok && r + mp > s) {
        k += 1
        s = s * ten
      }
      (k, share_printf__generate(r, s, mp, mm, high_ok, low_ok))
    }
    Some(pos0) => {
      let mut position = pos0
      if relativep {
        let mut k = 0
        let mut l = 1N
        while !(s * l >= r + mp) {
          k += 1
          l = l * ten
        }
        // r + s*(10^(k-position)/2) < s*l
        let a = k - position
        let less = if a >= 0 {
          r * BigInt::from_int(2) + s * share_printf__pow(10, a) <
          s * l * BigInt::from_int(2)
        } else {
          let q = share_printf__pow(10, -a)
          r * BigInt::from_int(2) * q + s < s * l * BigInt::from_int(2) * q
        }
        position = if less { k - position } else { k - position - 1 }
      }
      // x = s * 10^position / 2 (scale everything when position < 0)
      let xv = if position >= 0 {
        s * share_printf__pow(10, position) / BigInt::from_int(2)
      } else {
        let half = s / BigInt::from_int(2)
        let sc = share_printf__pow(10, -position)
        r = r * sc
        s = s * sc
        mp = mp * sc
        mm = mm * sc
        half
      }
      if mm < xv {
        mm = xv
      }
      low_ok = true
      if mp < xv {
        mp = xv
      }
      high_ok = true
      let rr0 = r + mp
      let mut k = 0
      while rr0 > s || (high_ok && rr0 == s) {
        k += 1
        s = s * ten
      }
      let mut kk = k
      let mut rr = r
      let mut mpp = mp
      let mut mmm = mm
      while rr > mmm &&
            ((rr + mpp) * ten < s || (!high_ok && (rr + mpp) * ten == s)) {
        kk -= 1
        rr = rr * ten
        mpp = mpp * ten
        mmm = mmm * ten
      }
      (kk, share_printf__generate(rr, s, mpp, mmm, high_ok, low_ok))
    }
  }
}

///|
/// SBCL FLONUM-EXPONENT.
fn share_printf__flonum_exponent(x : Double, single : Bool) -> Int raise {
  if x == 0.0 {
    1
  } else {
    share_printf__flonum_to_digits(x, single).0
  }
}

///|
/// SBCL FLONUM-TO-STRING: (string, length, leading-point, trailing-point,
/// point-position).
fn share_printf__flonum_to_string(
  x : Double,
  single : Bool,
  width? : Int? = None,
  fdigits? : Int? = None,
  scale? : Int? = None,
  fmin? : Int? = None,
  exponent_zero? : Int? = None,
) -> (String, Int, Bool, Bool, Int) raise {
  let sc = scale.unwrap_or(0)
  let fm = fmin.unwrap_or(0)
  let (e0, string) = match fdigits {
    Some(fd) => {
      let pos = (-(fd + sc)).min(-fm) + exponent_zero.unwrap_or(0)
      share_printf__flonum_to_digits(x, single, position=Some(pos))
    }
    None =>
      match width {
        Some(w) if w > 1 => {
          let wl = share_printf__flonum_to_digits(
            x,
            single,
            position=Some(
              (w - 1 + (match scale { Some(s) if s < 0 => s; _ => 0 })).max(1),
            ),
            relativep=true,
          )
          let fl = share_printf__flonum_to_digits(
            x,
            single,
            position=Some(-(fm + sc)),
          )
          if wl.1.length() >= fl.1.length() {
            wl
          } else {
            fl
          }
        }
        _ => share_printf__flonum_to_digits(x, single)
      }
  }
  let mut e = e0
  match exponent_zero {
    Some(ez) => e = if x == 0.0 { 0 } else { e - ez }
    None => ()
  }
  if x != 0.0 {
    e += sc
  }
  let cs = string_chars(string)
  let l = cs.length()
  let sb = StringBuilder::new()
  if (e == 0 && exponent_zero is Some(_)) || e > 0 {
    let m = l.min(e)
    for i in 0..<m {
      sb.write_char(cs[i])
    }
    for _ in 0..<(e - l).max(0) {
      sb.write_char('0')
    }
    sb.write_char('.')
    for i in m..<l {
      sb.write_char(cs[i])
    }
    match fdigits {
      Some(fd) =>
        for _ in 0..<(fd - (l - m)).max(0) {
          sb.write_char('0')
        }
      None => ()
    }
  } else {
    sb.write_char('.')
    for _ in 0..<(-e).max(0) {
      sb.write_char('0')
    }
    let end = match fdigits {
      None => l
      Some(fd) => l.min(fm.max(fd + e))
    }
    for i in 0..<end.max(0) {
      sb.write_char(cs[i])
    }
    match fdigits {
      Some(fd) =>
        for _ in 0..<(fd + e - l).max(0) {
          sb.write_char('0')
        }
      None => ()
    }
  }
  let result = sb.to_string()
  let rc = string_chars(result)
  let mut point = 0
  for i, c in rc {
    if c == '.' {
      point = i
      break
    }
  }
  (result, rc.length(), rc[0] == '.', rc[rc.length() - 1] == '.', point)
}

///|
/// A real argument as a float: (value, single-float?) or None.
fn share_printf__as_float(v : Value) -> (Double, Bool)? raise {
  match v {
    Flo(d) => Some((d, false))
    Fix(_) | Big(_) | Ratio(_, _) => {
      // (coerce number 'single-float)
      let d = to_double(v)
      Some((Float::from_double(d).to_double(), true))
    }
    _ => None
  }
}

///|
fn share_printf__sign_bit(x : Double) -> Bool {
  x < 0.0 || (x == 0.0 && 1.0 / x < 0.0)
}

///|
/// FORMAT-FIXED-AUX; returns true on overflow.
fn share_printf__fixed_aux(
  out : SharePrintfOut,
  x : Double,
  single : Bool,
  w : Int?,
  d : Int?,
  k : Int?,
  ovf : Char?,
  pad : Char,
  atsign : Bool,
) -> Bool raise {
  if x.is_inf() || x.is_nan() {
    out.put(float_to_string(x))
    return false
  }
  let mut spaceleft = w
  if w is Some(_) && (atsign || share_printf__sign_bit(x)) {
    spaceleft = spaceleft.map(n => n - 1)
  }
  let (str, len, lpoint0, tpoint0, _) = share_printf__flonum_to_string(
    x.abs(),
    single,
    width=spaceleft,
    fdigits=d,
    scale=k,
  )
  let mut lpoint = lpoint0
  let mut tpoint = tpoint0
  if d is Some(0) {
    tpoint = false
  }
  match w {
    Some(_) => {
      let mut sl = spaceleft.unwrap_or(0) - len
      if lpoint {
        if sl > 0 || tpoint {
          sl -= 1
        } else {
          lpoint = false
        }
      }
      if tpoint {
        if sl > 0 {
          sl -= 1
        } else {
          tpoint = false
        }
      }
      spaceleft = Some(sl)
    }
    None => ()
  }
  match (w, spaceleft, ovf) {
    (Some(wn), Some(sl), Some(oc)) if sl < 0 => {
      out.putn(wn, oc)
      return true
    }
    _ => ()
  }
  match w {
    Some(_) => out.putn(spaceleft.unwrap_or(0).max(0), pad)
    None => ()
  }
  if share_printf__sign_bit(x) {
    out.putc('-')
  } else if atsign {
    out.putc('+')
  }
  if lpoint {
    out.putc('0')
  }
  out.put(str)
  if tpoint {
    out.putc('0')
  }
  false
}

///|
fn share_printf__exponent_marker(single : Bool) -> Char {
  // *read-default-float-format* is double-float in Maxima
  if single {
    'f'
  } else {
    'e'
  }
}

///|
/// FORMAT-EXP-AUX
fn share_printf__exp_aux(
  out : SharePrintfOut,
  x : Double,
  single : Bool,
  w : Int?,
  d : Int?,
  e : Int?,
  k : Int,
  ovf : Char?,
  pad : Char,
  marker : Char?,
  atsign : Bool,
) -> Unit raise {
  if x.is_inf() || x.is_nan() {
    out.put(float_to_string(x))
    return
  }
  let num = x.abs()
  let num_expt = share_printf__flonum_exponent(num, single)
  let expt = num_expt - k
  let estr = expt.abs().to_string()
  let elen = match e {
    Some(en) => estr.length().max(en)
    None => estr.length()
  }
  let mut spaceleft : Int? = None
  match w {
    Some(wn) => {
      let mut sl = wn - 2 - elen
      if atsign || share_printf__sign_bit(x) {
        sl -= 1
      }
      spaceleft = Some(sl)
    }
    None => ()
  }
  match (w, ovf, e) {
    (Some(wn), Some(oc), Some(en)) if elen > en => {
      out.putn(wn, oc)
      return
    }
    _ => ()
  }
  let fdig = match d {
    Some(dn) => Some(if k > 0 { 1 + (dn - k) } else { dn })
    None => None
  }
  let fmin = if k < 0 { Some(1) } else { fdig }
  let (fstr, flen, lpoint0, tpoint0, _) = share_printf__flonum_to_string(
    num,
    single,
    width=spaceleft,
    fdigits=fdig,
    scale=Some(k),
    fmin~,
    exponent_zero=Some(num_expt),
  )
  let mut lpoint = lpoint0
  let mut tpoint = tpoint0
  if fdig is Some(0) {
    tpoint = false
  }
  match w {
    Some(_) => {
      let mut sl = spaceleft.unwrap_or(0) - flen
      if lpoint {
        if sl > 0 || tpoint {
          sl -= 1
        } else {
          lpoint = false
        }
      }
      if tpoint {
        if sl <= 0 {
          tpoint = false
        } else {
          sl -= 1
        }
      }
      spaceleft = Some(sl)
    }
    None => ()
  }
  match (w, spaceleft, ovf) {
    (Some(wn), Some(sl), Some(oc)) if sl < 0 => {
      out.putn(wn, oc)
      return
    }
    _ => ()
  }
  match w {
    Some(_) => out.putn(spaceleft.unwrap_or(0).max(0), pad)
    None => ()
  }
  if share_printf__sign_bit(x) {
    out.putc('-')
  } else if atsign {
    out.putc('+')
  }
  if lpoint {
    out.putc('0')
  }
  out.put(fstr)
  if tpoint {
    out.putc('0')
  }
  out.putc(marker.unwrap_or(share_printf__exponent_marker(single)))
  out.putc(if expt < 0 { '-' } else { '+' })
  match e {
    Some(en) => out.putn(en - estr.length(), '0')
    None => ()
  }
  out.put(estr)
}

///|
/// FORMAT-GENERAL-AUX
fn share_printf__general_aux(
  out : SharePrintfOut,
  x : Double,
  single : Bool,
  w : Int?,
  d : Int?,
  e : Int?,
  k : Int?,
  ovf : Char?,
  pad : Char,
  marker : Char?,
  atsign : Bool,
) -> Unit raise {
  if x.is_inf() || x.is_nan() {
    out.put(float_to_string(x))
    return
  }
  let a = x.abs()
  let n = share_printf__flonum_exponent(a, single)
  let d = match d {
    Some(dn) => dn
    None => {
      let (_, len, _, _, _) = share_printf__flonum_to_string(a, single)
      let q = if len == 1 { 1 } else { len - 1 }
      q.max(n.min(7))
    }
  }
  let ee = match e {
    Some(en) => en + 2
    None => 4
  }
  let ww = w.map(wn => wn - ee)
  let dd = d - n
  if 0 <= dd && dd <= d {
    let char = if share_printf__fixed_aux(out, x, single, ww, Some(dd), None, ovf, pad, atsign) {
      ovf.unwrap_or(' ')
    } else {
      ' '
    }
    out.putn(ee, char)
  } else {
    share_printf__exp_aux(out, x, single, w, Some(d), e, k.unwrap_or(1), ovf, pad, marker, atsign)
  }
}

///|
/// FORMAT-DOLLARS
fn share_printf__dollars(
  out : SharePrintfOut,
  number : Value,
  d : Int,
  n : Int,
  w : Int,
  pad : Char,
  colon : Bool,
  atsign : Bool,
) -> Unit raise {
  match share_printf__as_float(number) {
    Some((x, single)) => {
      let signstr = if share_printf__sign_bit(x) {
        "-"
      } else if atsign {
        "+"
      } else {
        ""
      }
      let signlen = signstr.length()
      let (str, _, _, _, pointplace) = share_printf__flonum_to_string(
        x.abs(),
        single,
        fdigits=Some(d),
      )
      if colon {
        out.put(signstr)
      }
      out.putn(w - signlen - n.max(pointplace) - 1 - d, pad)
      if !colon {
        out.put(signstr)
      }
      out.putn(n - pointplace, '0')
      out.put(str)
    }
    None =>
      share_printf__write_field(
        out,
        share_printf__princ(number),
        w,
        1,
        0,
        ' ',
        true,
      )
  }
}

// -- the interpreter --------------------------------------------------------

///|
/// Case conversion of ~( ~).
fn share_printf__case(s : String, colon : Bool, at : Bool) -> String {
  let cs = string_chars(s)
  if colon && at {
    return chars_to_string(cs.map(c => share_stringproc__char_upcase(c)))
  }
  if !colon && !at {
    return chars_to_string(cs.map(c => share_stringproc__char_downcase(c)))
  }
  // capitalize (each word) or capitalize-first (first word only)
  let sb = StringBuilder::new()
  let mut in_word = false
  let mut first_done = false
  for c in cs {
    let alnum = alphanumericp(c)
    if alnum {
      if !in_word && (colon || !first_done) {
        sb.write_char(share_stringproc__char_upcase(c))
      } else {
        sb.write_char(share_stringproc__char_downcase(c))
      }
      in_word = true
    } else {
      if in_word {
        first_done = true
      }
      in_word = false
      sb.write_char(c)
    }
  }
  sb.to_string()
}

///|
/// Interpret the directives ctl[from:to] with the arguments A.
fn share_printf__interpret(
  ctl : Array[Char],
  from : Int,
  to : Int,
  a : SharePrintfArgs,
  out : SharePrintfOut,
) -> Unit raise {
  let mut i = from
  while i < to {
    if ctl[i] != '~' {
      out.putc(ctl[i])
      i += 1
      continue
    }
    let d = share_printf__parse_dir(ctl, i)
    i = share_printf__directive(ctl, i, d, a, out)
  }
}

///|
/// Execute directive D (starting at index START); returns the index after
/// it (after the closing directive for compound ones).
fn share_printf__directive(
  ctl : Array[Char],
  start : Int,
  d : SharePrintfDir,
  a : SharePrintfArgs,
  out : SharePrintfOut,
) -> Int raise {
  ignore(start)
  match d.ch {
    'a' | 's' | 'w' => {
      let p = share_printf__params(d, a)
      share_printf__max_params(p, 4)
      let arg = a.next()
      let s = if d.colon && arg is Nil {
        "()"
      } else if d.ch == 'a' {
        share_printf__princ(arg)
      } else {
        share_printf__prin1(arg)
      }
      if p.length() == 0 {
        out.put(s)
      } else {
        share_printf__write_field(
          out,
          s,
          share_printf__pint(p, 0, Some(0)).unwrap_or(0),
          share_printf__pint(p, 1, Some(1)).unwrap_or(1),
          share_printf__pint(p, 2, Some(0)).unwrap_or(0),
          share_printf__pchar(p, 3, Some(' ')).unwrap_or(' '),
          d.at,
        )
      }
      d.next
    }
    'd' | 'b' | 'o' | 'x' => {
      let radix = match d.ch {
        'b' => 2
        'o' => 8
        'x' => 16
        _ => 10
      }
      let p = share_printf__params(d, a)
      share_printf__max_params(p, 4)
      let arg = a.next()
      if p.length() == 0 && !d.colon && !d.at {
        out.put(share_printf__princ(arg, base=radix))
      } else {
        share_printf__print_integer(
          out,
          arg,
          d.colon,
          d.at,
          radix,
          share_printf__pint(p, 0, Some(0)).unwrap_or(0),
          share_printf__pchar(p, 1, Some(' ')).unwrap_or(' '),
          share_printf__pchar(p, 2, Some(',')).unwrap_or(','),
          share_printf__pint(p, 3, Some(3)).unwrap_or(3),
        )
      }
      d.next
    }
    'r' => {
      let p = share_printf__params(d, a)
      share_printf__max_params(p, 5)
      let base = share_printf__pint(p, 0, None)
      let arg = a.next()
      match base {
        Some(b) =>
          share_printf__print_integer(
            out,
            arg,
            d.colon,
            d.at,
            b,
            share_printf__pint(p, 1, Some(0)).unwrap_or(0),
            share_printf__pchar(p, 2, Some(' ')).unwrap_or(' '),
            share_printf__pchar(p, 3, Some(',')).unwrap_or(','),
            share_printf__pint(p, 4, Some(3)).unwrap_or(3),
          )
        None => {
          if !integerp(arg) {
            raise share_printf__error(
              share_printf__prin1(arg) + " is not of type INTEGER.",
            )
          }
          if d.at {
            if d.colon {
              share_printf__old_roman(out, arg)
            } else {
              share_printf__roman(out, arg)
            }
          } else if d.colon {
            share_printf__ordinal(out, arg)
          } else {
            share_printf__cardinal(out, arg)
          }
        }
      }
      d.next
    }
    'c' => {
      let p = share_printf__params(d, a)
      share_printf__max_params(p, 0)
      let arg = a.next()
      let c = match arg {
        Char(c) => c
        _ =>
          raise share_printf__error(
            share_printf__prin1(arg) + " is not of type CHARACTER.",
          )
      }
      if d.colon {
        if c != ' ' && share_stringproc__graphic_char_p(c) {
          out.putc(c)
        } else {
          out.put(share_printf__char_name(c).unwrap_or(c.to_string()))
        }
      } else if d.at {
        out.put(share_printf__prin1(arg))
      } else {
        out.putc(c)
      }
      d.next
    }
    'p' => {
      let p = share_printf__params(d, a)
      share_printf__max_params(p, 0)
      let arg = if d.colon {
        if a.i == 0 {
          raise share_printf__error("No previous argument")
        }
        a.all[a.i - 1]
      } else {
        a.next()
      }
      let one = arg is Fix(1L)
      if d.at {
        out.put(if one { "y" } else { "ies" })
      } else if !one {
        out.putc('s')
      }
      d.next
    }
    'f' => {
      let p = share_printf__params(d, a)
      share_printf__max_params(p, 5)
      let w = share_printf__pint(p, 0, None)
      let dd = share_printf__pint(p, 1, None)
      let k = share_printf__pint(p, 2, None)
      let ovf = share_printf__pchar(p, 3, None)
      let pad = share_printf__pchar(p, 4, Some(' ')).unwrap_or(' ')
      let arg = a.next()
      match share_printf__as_float(arg) {
        Some((x, single)) =>
          share_printf__fixed_aux(out, x, single, w, dd, k, ovf, pad, d.at) |> ignore
        None =>
          share_printf__write_field(
            out,
            share_printf__princ(arg),
            w.unwrap_or(0),
            1,
            0,
            pad,
            true,
          )
      }
      d.next
    }
    'e' | 'g' => {
      let p = share_printf__params(d, a)
      share_printf__max_params(p, 7)
      let w = share_printf__pint(p, 0, None)
      let dd = share_printf__pint(p, 1, None)
      let e = share_printf__pint(p, 2, None)
      let k = share_printf__pint(p, 3, None)
      let ovf = share_printf__pchar(p, 4, None)
      let pad = share_printf__pchar(p, 5, Some(' ')).unwrap_or(' ')
      let mark = share_printf__pchar(p, 6, None)
      let arg = a.next()
      match share_printf__as_float(arg) {
        Some((x, single)) =>
          if d.ch == 'e' {
            share_printf__exp_aux(out, x, single, w, dd, e, k.unwrap_or(1), ovf, pad, mark, d.at)
          } else {
            share_printf__general_aux(out, x, single, w, dd, e, k, ovf, pad, mark, d.at)
          }
        None =>
          share_printf__write_field(
            out,
            share_printf__princ(arg),
            w.unwrap_or(0),
            1,
            0,
            pad,
            true,
          )
      }
      d.next
    }
    '$' => {
      let p = share_printf__params(d, a)
      share_printf__max_params(p, 4)
      let dd = share_printf__pint(p, 0, Some(2)).unwrap_or(2)
      let n = share_printf__pint(p, 1, Some(1)).unwrap_or(1)
      let w = share_printf__pint(p, 2, Some(0)).unwrap_or(0)
      let pad = share_printf__pchar(p, 3, Some(' ')).unwrap_or(' ')
      let arg = a.next()
      share_printf__dollars(out, arg, dd, n, w, pad, d.colon, d.at)
      d.next
    }
    '%' | '&' | '|' | '~' => {
      let p = share_printf__params(d, a)
      share_printf__max_params(p, 1)
      let n = share_printf__pint(p, 0, Some(1)).unwrap_or(1)
      match d.ch {
        '%' => out.putn(n, '\n')
        '&' =>
          if n > 0 {
            if out.col != 0 {
              out.putc('\n')
            }
            out.putn(n - 1, '\n')
          }
        '|' => out.putn(n, '\u{0C}')
        _ => out.putn(n, '~')
      }
      d.next
    }
    't' => {
      let p = share_printf__params(d, a)
      share_printf__max_params(p, 2)
      if d.at {
        let colrel = share_printf__pint(p, 0, Some(1)).unwrap_or(1)
        let colinc = share_printf__pint(p, 1, Some(1)).unwrap_or(1)
        let cur = out.col
        let spaces = if colinc > 0 {
          (cur + colrel + colinc - 1) / colinc * colinc - cur
        } else {
          colrel
        }
        out.putn(spaces, ' ')
      } else {
        let colnum = share_printf__pint(p, 0, Some(1)).unwrap_or(1)
        let colinc = share_printf__pint(p, 1, Some(1)).unwrap_or(1)
        let cur = out.col
        if cur < colnum {
          out.putn(colnum - cur, ' ')
        } else if colinc != 0 {
          out.putn(colinc - (cur - colnum) % colinc, ' ')
        }
      }
      d.next
    }
    '\n' => {
      let mut j = d.next
      if d.at {
        out.putc('\n')
      }
      if !d.colon {
        while j < ctl.length() &&
              (ctl[j] == ' ' || ctl[j] == '\t' || ctl[j] == '\r' || ctl[j] == '\u{0C}') {
          j += 1
        }
      }
      j
    }
    '_' | 'i' => {
      share_printf__params(d, a) |> ignore
      d.next
    }
    '*' => {
      let p = share_printf__params(d, a)
      share_printf__max_params(p, 1)
      if d.at {
        let posn = share_printf__pint(p, 0, Some(0)).unwrap_or(0)
        if posn < 0 || posn > a.all.length() {
          raise share_printf__error(
            "Index \{posn} is out of bounds. It should have been between 0 and \{a.all.length()}.",
          )
        }
        a.i = posn
      } else if d.colon {
        let n = share_printf__pint(p, 0, Some(1)).unwrap_or(1)
        let new = a.i - n
        if new < 0 || new > a.all.length() {
          raise share_printf__error(
            "Index \{new} is out of bounds. It should have been between 0 and \{a.all.length()}.",
          )
        }
        a.i = new
      } else {
        let n = share_printf__pint(p, 0, Some(1)).unwrap_or(1)
        for _ in 0..<n {
          a.next() |> ignore
        }
      }
      d.next
    }
    '?' => {
      let p = share_printf__params(d, a)
      share_printf__max_params(p, 0)
      let sub = a.next()
      let sc = string_chars(lstring(sub))
      if d.at {
        share_printf__interpret(sc, 0, sc.length(), a, out) catch {
          UpAndOut | UpUpAndOut => ()
          e => raise e
        }
      } else {
        let subargs = list_to_array(a.next())
        let a2 = { all: subargs, i: 0, outside_empty: None }
        share_printf__interpret(sc, 0, sc.length(), a2, out) catch {
          UpAndOut | UpUpAndOut => ()
          e => raise e
        }
      }
      d.next
    }
    '^' => {
      let p = share_printf__params(d, a)
      share_printf__max_params(p, 3)
      if d.at {
        raise share_printf__error("@ modifier not allowed")
      }
      if d.colon && a.outside_empty is None {
        raise share_printf__error(
          "Attempt to use ~:^ outside a ~:{...~} construct",
        )
      }
      let pi = fn(i) raise { share_printf__pint(p, i, None).unwrap_or(0) }
      let test_ = match p.length() {
        0 =>
          if d.colon {
            a.outside_empty.unwrap_or(true)
          } else {
            a.remaining() == 0
          }
        1 => pi(0) == 0
        2 => pi(0) == pi(1)
        _ => pi(0) <= pi(1) && pi(1) <= pi(2)
      }
      if test_ {
        raise (if d.colon { UpUpAndOut } else { UpAndOut })
      }
      d.next
    }
    '(' => {
      let p = share_printf__params(d, a)
      share_printf__max_params(p, 0)
      let (_, ci, cd) = share_printf__find_close(ctl, d.next, ')')
      let sub = { sb: StringBuilder::new(), col: out.col }
      let flush = fn() {
        let s = share_printf__case(sub.sb.to_string(), d.colon, d.at)
        out.put(s)
      }
      share_printf__interpret(ctl, d.next, ci, a, sub) catch {
        e => {
          flush()
          raise e
        }
      }
      flush()
      cd.next
    }
    '[' => {
      let (seps, ci, cd) = share_printf__find_close(ctl, d.next, ']')
      // clauses in source order
      let starts = [d.next]
      let ends : Array[Int] = []
      let mut last_semi_colon = false
      for k, sp in seps {
        ends.push(sp.0)
        starts.push(sp.1.next)
        if k == seps.length() - 1 && sp.1.colon {
          last_semi_colon = true
        }
      }
      ends.push(ci)
      let p = share_printf__params(d, a)
      share_printf__max_params(p, 1)
      if d.colon && d.at {
        raise share_printf__error("Cannot specify both colon and at-sign")
      }
      if d.at {
        if starts.length() > 1 {
          raise share_printf__error("Can only specify one section")
        }
        let prev = a.i
        let arg = a.next()
        if arg.truthy() {
          a.i = prev
          share_printf__interpret(ctl, starts[0], ends[0], a, out)
        }
      } else if d.colon {
        if starts.length() != 2 {
          raise share_printf__error("Must specify exactly two sections")
        }
        let arg = a.next()
        let k = if arg.truthy() { 1 } else { 0 }
        share_printf__interpret(ctl, starts[k], ends[k], a, out)
      } else {
        let index = match p.get(0) {
          Some(Some(v)) => v
          _ => a.next()
        }
        let nclauses = if last_semi_colon {
          starts.length() - 1
        } else {
          starts.length()
        }
        let k = match index {
          Fix(n) =>
            if n >= 0L && n < nclauses.to_int64() {
              n.to_int()
            } else if last_semi_colon {
              starts.length() - 1
            } else {
              -1
            }
          Big(_) => if last_semi_colon { starts.length() - 1 } else { -1 }
          _ =>
            raise share_printf__error(
              "The argument to ~[ is not an integer: " + share_printf__princ(index),
            )
        }
        if k >= 0 {
          share_printf__interpret(ctl, starts[k], ends[k], a, out)
        }
      }
      cd.next
    }
    '{' => {
      let (_, ci, cd) = share_printf__find_close(ctl, d.next, '}')
      let p = share_printf__params(d, a)
      share_printf__max_params(p, 1)
      let mut max = share_printf__pint(p, 0, None)
      let cclon = cd.colon
      let empty_body = ci == d.next
      let (body, bs, be) = if empty_body {
        let s = string_chars(lstring(a.next()))
        (s, 0, s.length())
      } else {
        (ctl, d.next, ci)
      }
      // do-guts on argument state ga
      let guts = fn(ga : SharePrintfArgs) raise {
        if empty_body {
          // %format has its own up-and-out catch
          share_printf__interpret(body, bs, be, ga, out) catch {
            UpAndOut => ()
            e => raise e
          }
        } else {
          share_printf__interpret(body, bs, be, ga, out)
        }
      }
      let lp = fn(la : SharePrintfArgs) raise {
        while true {
          if !cclon && la.remaining() == 0 {
            break
          }
          match max {
            Some(m) => {
              max = Some(m - 1)
              if m - 1 < 0 {
                break
              }
            }
            None => ()
          }
          if d.colon {
            let sub = la.next()
            let sa = {
              all: list_to_array(sub),
              i: 0,
              outside_empty: Some(la.remaining() == 0),
            }
            guts(sa) catch {
              UpAndOut => ()
              e => raise e
            }
          } else {
            guts(la)
          }
          if cclon && la.remaining() == 0 {
            break
          }
        }
      }
      let catcher = fn(la : SharePrintfArgs) raise {
        lp(la) catch {
          UpAndOut if !d.colon => ()
          UpUpAndOut if d.colon => ()
          e => raise e
        }
      }
      if d.at {
        catcher(a)
      } else {
        let arg = a.next()
        let la = { all: list_to_array(arg), i: 0, outside_empty: a.outside_empty }
        catcher(la)
      }
      cd.next
    }
    '<' => {
      let (seps, ci, cd) = share_printf__find_close(ctl, d.next, '>')
      let p = share_printf__params(d, a)
      share_printf__max_params(p, 4)
      let mincol = share_printf__pint(p, 0, Some(0)).unwrap_or(0)
      let colinc = share_printf__pint(p, 1, Some(1)).unwrap_or(1)
      let minpad = share_printf__pint(p, 2, Some(0)).unwrap_or(0)
      let padchar = share_printf__pchar(p, 3, Some(' ')).unwrap_or(' ')
      let starts = [d.next]
      let ends : Array[Int] = []
      for sp in seps {
        ends.push(sp.0)
        starts.push(sp.1.next)
      }
      ends.push(ci)
      let strings : Array[String] = []
      let mut newline_string : String? = None
      let mut extra_space = 0
      let mut line_len = 72
      let mut first = 0
      let segment = fn(k : Int) raise {
        let sub = { sb: StringBuilder::new(), col: 0 }
        share_printf__interpret(ctl, starts[k], ends[k], a, sub)
        sub.sb.to_string()
      }
      let collect = fn() raise {
        if seps.length() > 0 && seps[0].1.colon {
          let pp = share_printf__params(seps[0].1, a)
          extra_space = share_printf__pint(pp, 0, Some(0)).unwrap_or(0)
          line_len = share_printf__pint(pp, 1, Some(72)).unwrap_or(72)
          newline_string = Some(segment(0))
          first = 1
        }
        for k in first..<starts.length() {
          strings.push(segment(k))
        }
      }
      collect() catch {
        UpAndOut => ()
        e => raise e
      }
      // format-justification
      let pad_left = d.colon
      let pad_right = d.at
      let mut gaps = strings.length() -
        1 +
        (if pad_left { 1 } else { 0 }) +
        (if pad_right { 1 } else { 0 })
      let mut chars = gaps * minpad
      for s in strings {
        chars += string_length(s)
      }
      let width = if chars > mincol {
        mincol + (chars - mincol + colinc - 1) / colinc * colinc
      } else {
        mincol
      }
      let mut padding = width - chars + gaps * minpad
      match newline_string {
        Some(ns) =>
          if out.col + width + extra_space > line_len {
            out.put(ns)
          }
        None => ()
      }
      let do_padding = fn() {
        let n = if gaps == 0 { padding } else { padding / gaps }
        padding -= n
        gaps -= 1
        out.putn(n, padchar)
      }
      if pad_left || (!pad_right && strings.length() == 1) {
        do_padding()
      }
      if strings.length() > 0 {
        out.put(strings[0])
        for k in 1..<strings.length() {
          do_padding()
          out.put(strings[k])
        }
      }
      if pad_right {
        do_padding()
      }
      cd.next
    }
    ';' | ')' | ']' | '}' | '>' =>
      raise share_printf__error("Unexpected directive ~" + d.ch.to_string())
    _ =>
      raise share_printf__error(
        "Unknown format directive ~" + d.ch.to_string(),
      )
  }
}

///|
/// (format dest ctl args...): DEST nil returns a string, t writes to
/// *standard-output*, otherwise to the stream.
fn share_printf__format(dest : Value, ctl : String, args : Array[Value]) -> Value raise {
  let start_col = match dest {
    Nil => 0
    Stream(_) => stream_column(stream=dest)
    _ => stream_column()
  }
  let out = { sb: StringBuilder::new(), col: start_col }
  let a = { all: args, i: 0, outside_empty: None }
  let cs = string_chars(ctl)
  share_printf__interpret(cs, 0, cs.length(), a, out) catch {
    UpAndOut | UpUpAndOut => ()
    e => raise e
  }
  let s = out.sb.to_string()
  match dest {
    Nil => Str(s)
    Stream(_) => {
      write_string(s, stream=dest)
      Nil
    }
    _ => {
      write_string(s)
      Nil
    }
  }
}

///|
fn init_share_printf() -> Unit raise {
  // Make stdout, stdin and stderr user-accessible
  set(q_d_stderr, symval(error_output)) |> ignore
  set(q_d_stdout, symval(standard_output)) |> ignore
  set(q_d_stdin, symval(standard_input)) |> ignore
}
