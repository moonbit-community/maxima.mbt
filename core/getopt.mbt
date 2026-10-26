// Port of src/getopt.lisp: command line option processing (Kevin
// Rosenberg's GETOPT package).

///|
let getopt__k_short : Value = kw("short")

///|
let getopt__k_long : Value = kw("long")

///|
let getopt__k_arg : Value = kw("arg")

///|
let getopt__k_none : Value = kw("none")

///|
let getopt__k_required : Value = kw("required")

///|
let getopt__k_optional : Value = kw("optional")

///|
/// The characters of a string argument (NIL has none).
fn getopt__chars(arg : Value) -> Array[Char] {
  match arg {
    Str(s) => string_chars(s)
    _ => []
  }
}

///|
fn getopt_is_short_option(arg : Value) -> Value raise {
  let cs = getopt__chars(arg)
  lbool(cs.length() >= 2 && cs[0] == '-' && cs[1] != '-')
}

///|
fn getopt_is_option_terminator(arg : Value) -> Value raise {
  let cs = getopt__chars(arg)
  lbool(cs.length() == 2 && cs[0] == '-' && cs[1] == '-')
}

///|
fn getopt_is_long_option(arg : Value) -> Value raise {
  let cs = getopt__chars(arg)
  lbool(cs.length() > 2 && cs[0] == '-' && cs[1] == '-' && cs[2] != '-')
}

///|
/// Returns base-name,argument
fn getopt_decompose_arg(arg : Value, option_type : Value) -> (Value, Value) raise {
  let start = if eq(option_type, getopt__k_long) {
    2
  } else if eq(option_type, getopt__k_short) {
    1
  } else {
    raise LispError::SimpleError(
      prin1_to_string(option_type) +
      " fell through ECASE expression. Wanted one of (:LONG :SHORT).",
    )
  }
  let cs = getopt__chars(arg)
  let mut name_end : Int? = None
  for i, c in cs {
    if c == '=' {
      name_end = Some(i)
      break
    }
  }
  match name_end {
    Some(e) =>
      (
        Str(chars_to_string(cs[start:e].to_array())),
        Str(chars_to_string(cs[e + 1:].to_array())),
      )
    None => (Str(chars_to_string(cs[start:].to_array())), Nil)
  }
}

///|
/// Analyzes an argument. Returns option-type,base-name,argument
fn getopt_analyze_arg(arg : Value) -> (Value, Value, Value) raise {
  let option_type = if getopt_is_short_option(arg).truthy() {
    getopt__k_short
  } else if getopt_is_long_option(arg).truthy() {
    getopt__k_long
  } else {
    getopt__k_arg
  }
  if eq(option_type, getopt__k_short) || eq(option_type, getopt__k_long) {
    let (base, arg) = getopt_decompose_arg(arg, option_type)
    (option_type, base, arg)
  } else {
    (getopt__k_arg, arg, Nil)
  }
}

///|
/// Find an option in option list. Handles using unique abbreviations
fn getopt_find_option(
  name : Value,
  options : Value,
  allow_exact_match? : Value = Nil,
) -> Value raise {
  let option_names = mapcar(o => car(o), options)
  let pos = getopt_match_unique_abbreviation(
    name,
    option_names,
    allow_exact_match~,
  )
  if pos.truthy() {
    nth(to_int(pos), options)
  } else {
    Nil
  }
}

///|
/// Matches an argument to an option. Returns
/// option-list,option-type,base-name,argument
fn getopt_match_option(
  arg : Value,
  options : Value,
  allow_exact_match? : Value = Nil,
) -> (Value, Value, Value, Value) raise {
  let (option_type, base_name, argument) = getopt_analyze_arg(arg)
  let match_ = getopt_find_option(base_name, options, allow_exact_match~)
  (
    match_,
    option_type,
    if match_.truthy() {
      car(match_)
    } else {
      Nil
    },
    argument,
  )
}

///|
/// Returns position of ABBR in STRINGS. ABBR may be a unique abbreviation.
/// Returns NIL if no match found.
fn getopt_match_unique_abbreviation(
  abbr : Value,
  strings : Value,
  allow_exact_match? : Value = Nil,
) -> Value raise {
  let a = lstring(abbr)
  let len = string_length(a)
  let mut matches : Value = Nil
  let strs = list_to_array(strings)
  for i, sv in strs {
    let s = lstring(sv)
    let l = string_length(s)
    if len == l {
      if a == s {
        if allow_exact_match.truthy() {
          return int(i)
        } else {
          matches = cons(cons(sv, int(i)), matches)
        }
      }
    } else if len < l {
      if a == substring(s, 0, end=len) {
        matches = cons(cons(sv, int(i)), matches)
      }
    }
  }
  if length(matches) == 1 {
    cdr(first(matches))
  } else {
    Nil
  }
}

///|
/// Processes a list of arguments and options. Returns three values:
///  - Non-option arguments
///  - An alist of options consisting of the option name and the value, if
///    any
///  - A list of any option names that were not recognized
///
/// options is a list of option lists. The fields of the list are
///  - NAME name of the long option
///  - HAS-ARG with legal values of :NONE, :REQUIRED, :OPTIONAL
///  - VAL value to return for a option with no arguments
fn getopt_getopt(
  args : Value,
  options : Value,
  allow_exact_match? : Value = Nil,
) -> (Value, Value, Value) raise {
  let mut pos = args
  let mut finished_options = false
  let mut out_opts : Value = Nil
  let mut out_args : Value = Nil
  let mut errors : Value = Nil
  while pos.truthy() {
    if finished_options {
      out_args = cons(car(pos), out_args)
    } else if getopt_is_option_terminator(car(pos)).truthy() {
      finished_options = true
    } else {
      let arg = car(pos)
      let (option_list, option_type, base_name, argument) = getopt_match_option(
        car(pos),
        options,
        allow_exact_match~,
      )
      if option_list.truthy() && !eq(option_type, getopt__k_arg) {
        if argument.truthy() {
          if eq(second(option_list), getopt__k_none) {
            errors = cons(base_name, errors)
          } else {
            out_opts = cons(cons(base_name, argument), out_opts)
          }
        } else if eq(getopt__k_required, second(option_list)) &&
          cdr(pos) is Nil {
          errors = cons(base_name, errors)
        } else {
          let kind = second(option_list)
          if eq(kind, getopt__k_none) {
            out_opts = cons(cons(base_name, third(option_list)), out_opts)
          } else if eq(kind, getopt__k_required) {
            // Next arg is the value.
            out_opts = cons(cons(base_name, second(pos)), out_opts)
            pos = cdr(pos)
          } else if eq(kind, getopt__k_optional) {
            // Optional arg.  If the next arg is an option arg, we use the
            // default value. Otherwise we use the next arg as the value.
            if getopt_is_short_option(second(pos)).truthy() ||
              getopt_is_long_option(second(pos)).truthy() {
              out_opts = cons(cons(base_name, third(option_list)), out_opts)
            } else {
              out_opts = cons(cons(base_name, second(pos)), out_opts)
              pos = cdr(pos)
            }
          }
        }
      } else if eq(getopt__k_long, option_type) {
        errors = cons(getopt_decompose_arg(arg, option_type).0, errors)
      } else if eq(getopt__k_short, option_type) {
        let cs = getopt__chars(car(pos))
        if cs.length() <= 2 {
          // Unrecognized short option (one character)
          errors = cons(getopt_decompose_arg(arg, option_type).0, errors)
        } else {
          // We have option that's not matched, but looks like a short
          // option like "-abc".  Expand this to '("-a" "-b" "-c") and
          // effectively replace "-abc" with the replacement.  We setf the
          // cdr because the do loop will remove "-abc" for us.
          let expanded = list(
            cs[1:].to_array().map(c => Str("-" + c.to_string())),
          )
          setf_cdr(pos, append(expanded, cdr(pos))) |> ignore
        }
      } else {
        out_args = cons(arg, out_args)
      }
    }
    pos = cdr(pos)
  }
  (nreverse(out_args), nreverse(out_opts), errors)
}

///|
fn init_getopt() -> Unit raise {
  ()
}
