// Port of src/prompt-util.lisp: the input-prompt specials, the
// format-prompt machinery, the main-prompt / break-prompt printers, and
// STRIPDOLLAR.

///|
/// If $ALT_FORMAT_PROMPT is NIL, use DEFAULT-FORMAT-PROMPT to print prompt;
/// otherwise MFUNCALL $ALT_FORMAT_PROMPT to print prompt.
fn format_prompt(
  destination : Value,
  control_string : Value,
  arguments : Value,
) -> Value raise {
  if symval(q_d_alt_format_prompt).truthy() {
    alt_format_prompt(destination, control_string, arguments)
  } else {
    default_format_prompt(destination, control_string, arguments)
  }
}

///|
/// MFUNCALL $ALT_FORMAT_PROMPT with a heavy coating of error protection.
fn alt_format_prompt(
  destination : Value,
  control_string : Value,
  arguments : Value,
) -> Value raise {
  let call = () => with_special(q_ear_merror_signals__dolerror_p, t, () => {
    let prompt = mfuncall(
      symval(q_d_alt_format_prompt),
      list([destination, control_string, arguments]),
    )
    if stringp(prompt) {
      prompt
    } else {
      merr("alt_format_prompt returned an object of type ~a, needed a string.", [
        prompt,
      ])
    }
  })
  call() catch {
    LispError::Throw(_, _) as e => raise e
    LispError::ReturnFrom(_, _) as e => raise e
    LispError::Go(_) as e => raise e
    e => {
      set(q_d_alt_format_prompt, Nil) |> ignore
      format(t, "Error in printing prompt; reverting to default.~%~a", [
        Str(prompt_util__error_message(e)),
      ])
      |> ignore
      throw_tag(q_macsyma_quit, q_maxima_error)
    }
  }
}

///|
/// A printable message for a caught error (what PRINC of a Lisp condition
/// shows).
fn prompt_util__error_message(e : Error) -> String {
  match e {
    LispError::SimpleError(msg) => msg
    LispError::Condition(_, msg, _) => msg
    _ => e.to_string()
  }
}

///|
/// Like AFORMAT, but add the prefix and suffix configured for a prompt.
fn default_format_prompt(
  destination : Value,
  control_string : Value,
  arguments : Value,
) -> Value raise {
  with_special(q_ear_print_base, Fix(10L), () => {
    let body = aformat(Nil, control_string, arguments)
    if destination is Nil {
      // return value string is important
      Str(
        lstring(symval(q_ear_prompt_prefix)) +
        lstring(body) +
        lstring(symval(q_ear_prompt_suffix)),
      )
    } else {
      format(destination, "~A~A~A", [
        symval(q_ear_prompt_prefix),
        body,
        symval(q_ear_prompt_suffix),
      ])
    }
  })
}

///|
fn main_prompt() -> Value raise {
  if symval(q_ear_display_labels_p).truthy() &&
    !symval(q_ear_suppress_input_echo).truthy() {
    format_prompt(
      Nil,
      Str("(~A~A) "),
      list([
        Str(princ_to_string(stripdollar(symval(q_d_inchar)))),
        symval(q_d_linenum),
      ]),
    )
  } else {
    Str("")
  }
}

///|
fn break_prompt() -> Value raise {
  format_prompt(
    Nil,
    Str("~A"),
    list1(Str(princ_to_string(stripdollar(symval(q_d_prompt))))),
  )
}

///|
fn stripdollar(x : Value) -> Value raise {
  if !atom(x) {
    if eq(caar(x), q_bigfloat) && !minusp(cadr(x)) {
      return implode(fpformat(x))
    } else {
      return merr("STRIPDOLLAR: argument must be an atom; found: ~M", [x])
    }
  }
  if numberp(x) {
    return x
  }
  if x is Nil {
    return q_false
  }
  if eq(x, t) {
    return q_true
  }
  let name = match x {
    Str(s) => s
    Sym(s) => s.name
    Char(c) => c.to_string()
    _ => return x
  }
  if name.length() > 0 && (name.has_prefix("$") || name.has_prefix("%")) {
    sym(name.substring(start=1))
  } else {
    x
  }
}

///|
fn init_prompt_util() -> Unit raise {
  defvar_init(
    q_d_default_format_prompt,
    lfunc("default-format-prompt", args => default_format_prompt(
      arg(args, 0),
      arg(args, 1),
      arg(args, 2),
    )),
  )
}
