// Port of src/transs.lisp: user-hacking code, file-io, translator toplevel
// ($translate, $compile, $compfile, $translate_file, $compile_file).
//
// Translated code is written to files in Lisp syntax as CL Maxima writes it
// inside WITH-MAXIMA-IO-SYNTAX (readtable case :INVERT, *PRINT-RADIX* T,
// *PRINT-GENSYM* NIL), so that symbol names print as the port's names. The
// port has no Lisp compiler: COMPILE is a no-op (translated functions are
// run by the Lisp evaluator) and COMPILE-FILE "compiles" a translated file
// by copying its Lisp source to the output file, which LOAD then reads.

// ---------------------------------------------------------------------------
// Printing Lisp forms with WITH-MAXIMA-IO-SYNTAX.

///|
let transs__q_print_pretty : Value = sym("*print-pretty*")

///|
/// Does a CL symbol name need |escaping| when printed with the standard
/// readtable (case :UPCASE)?
fn transs__needs_escape(name : String) -> Bool {
  if name.length() == 0 {
    return true
  }
  let mut all_dots = true
  for c in name {
    match c {
      ' ' | '(' | ')' | '"' | ';' | '\'' | '`' | ',' | '|' | '\\' | '\n' | '\t' =>
        return true
      _ => ()
    }
    if c != '.' {
      all_dots = false
    }
    if lower_case_p(c) {
      return true
    }
  }
  if all_dots {
    return true
  }
  // looks like a number?
  parse_number_token(name) is Some(_)
}

///|
/// Print X to SB as PRIN1 does inside WITH-MAXIMA-IO-SYNTAX: standard CL
/// syntax (the port's names are the case-inverted CL names), *PRINT-RADIX*
/// T, *PRINT-GENSYM* NIL; QUOTE and FUNCTION forms are abbreviated only by
/// the pretty printer.
fn transs__print(sb : StringBuilder, x : Value, pretty~ : Bool = false) -> Unit {
  match x {
    Nil => sb.write_string("NIL")
    Sym(s) => {
      let cl = invert_case(s.name)
      if s.name.contains(":") {
        // a package-qualified symbol (e.g. cl:signum, intl:gettext) or a
        // keyword; CL:SIGNUM is shadowed in MAXIMA, so it prints with the
        // package name.
        sb.write_string(
          if cl.has_prefix("CL::") {
            "COMMON-LISP:" + cl.substring(start=4)
          } else {
            cl
          },
        )
      } else if transs__needs_escape(cl) {
        sb.write_char('|')
        for c in cl {
          if c == '|' || c == '\\' {
            sb.write_char('\\')
          }
          sb.write_char(c)
        }
        sb.write_char('|')
      } else {
        sb.write_string(cl)
      }
    }
    // *PRINT-RADIX* T
    Fix(n) => sb.write_string(n.to_string() + ".")
    Big(b) => sb.write_string(b.to_string() + ".")
    Ratio(n, d) => sb.write_string("#10r" + n.to_string() + "/" + d.to_string())
    Cons({ car: Sym({ name: "quote", .. }), cdr: Cons({ car: q, cdr: Nil }) }) if pretty => {
      sb.write_char('\'')
      transs__print(sb, q, pretty~)
    }
    Cons({ car: Sym({ name: "function", .. }), cdr: Cons({ car: q, cdr: Nil }) }) if pretty => {
      sb.write_string("#'")
      transs__print(sb, q, pretty~)
    }
    Cons(_) => {
      sb.write_char('(')
      let mut p = x
      let mut first = true
      while true {
        match p {
          Cons(c) => {
            if !first {
              sb.write_char(' ')
            }
            first = false
            transs__print(sb, c.car, pretty~)
            p = c.cdr
          }
          Nil => break
          _ => {
            sb.write_string(" . ")
            transs__print(sb, p, pretty~)
            break
          }
        }
      }
      sb.write_char(')')
    }
    Func(f) => sb.write_string("#<FUNCTION " + invert_case(f.name) + ">")
    Vec(a) if a.elt != "character" && a.dims.length() == 1 => {
      sb.write_string("#(")
      let n = match a.fill {
        Some(f) => f
        None => a.data.length()
      }
      for i in 0..<n {
        if i > 0 {
          sb.write_char(' ')
        }
        transs__print(sb, a.data[i], pretty~)
      }
      sb.write_char(')')
    }
    _ => print_value(sb, x, true)
  }
}

///|
/// The flat printed representation of X.
fn transs__flat(x : Value, pretty~ : Bool = true) -> String {
  let sb = StringBuilder::new()
  transs__print(sb, x, pretty~)
  sb.to_string()
}

///|
let transs__line_width : Int = 80

///|
/// Pretty print X at column COL: a form that does not fit on the line is
/// written with its operator and first argument on the first line and each
/// further element on its own line, indented.
fn transs__pprint(sb : StringBuilder, x : Value, col : Int) -> Unit {
  let flat = transs__flat(x)
  if col + flat.length() <= transs__line_width || !consp(x) || !(cdr(x) is Cons(_)) {
    sb.write_string(flat)
    return
  }
  match x {
    Cons({ car: Sym({ name: "quote", .. }), cdr: Cons({ car: q, cdr: Nil }) }) => {
      sb.write_char('\'')
      transs__pprint(sb, q, col + 1)
      return
    }
    Cons({ car: Sym({ name: "function", .. }), cdr: Cons({ car: q, cdr: Nil }) }) => {
      sb.write_string("#'")
      transs__pprint(sb, q, col + 2)
      return
    }
    _ => ()
  }
  let head = car(x)
  sb.write_char('(')
  let indent = col + (if consp(head) { 1 } else { 2 })
  let mut rest = cdr(x)
  if consp(head) {
    transs__pprint(sb, head, col + 1)
  } else {
    let h = transs__flat(head)
    sb.write_string(h)
    // the first argument stays on the operator's line
    match rest {
      Cons({ car: a, cdr: r }) => {
        sb.write_char(' ')
        transs__pprint(sb, a, col + 1 + h.length() + 1)
        rest = r
      }
      _ => ()
    }
  }
  while true {
    match rest {
      Cons({ car: a, cdr: r }) => {
        sb.write_char('\n')
        sb.write_string(" ".repeat(indent))
        transs__pprint(sb, a, indent)
        rest = r
      }
      Nil => break
      r => {
        sb.write_string(" . ")
        transs__print(sb, r, pretty=true)
        break
      }
    }
  }
  sb.write_char(')')
}

///|
/// `(prin1 x stream)` with *PRINT-PRETTY* PRETTY, in Maxima io syntax.
fn transs__prin1(x : Value, stream : Value, pretty : Bool) -> Unit {
  let sb = StringBuilder::new()
  if pretty {
    transs__pprint(sb, x, 0)
  } else {
    transs__print(sb, x)
  }
  write_string(sb.to_string(), stream~)
}

// ---------------------------------------------------------------------------

///|
/// $COMPFILE
fn d_compfile(forms : Value) -> Value raise {
  let mut forms = cdr(forms)
  if length(forms) == 1 {
    merr(
      "compfile: no functions specified; I refuse to create an empty file.",
      [],
    )
    |> ignore
  }
  transm__with_transl_state(() => {
    set(q_ear_in_compfile, t) |> ignore
    let out_file_name = princ_to_string(maxima_string(meval(car(forms))))
    let mut t_error : Value = Nil
    let b = bind(q_ear_translation_msgs_files, Nil)
    defer unbind(b)
    forms = cdr(forms)
    let out = make_string_output_stream()
    set(q_transl_file, out) |> ignore
    // UNWIND-PROTECT: the file is closed (kept) also when the translation
    // exits abnormally, and deleted when T-ERROR is set.
    defer {
      if t_error is Nil {
        write_file(out_file_name, get_output_stream_string(out)) catch {
          _ => ()
        }
      }
    }
    dskfn__with_io_syntax(() => {
      if memq(q_d_all, forms).truthy() || memq(q_d_functions, forms).truthy() {
        forms = mapcar(x => caar(x), cdr(symval(q_d_functions)))
      }
      let ba = bind(q_tr_abort, Nil)
      defer unbind(ba)
      for item0 in forms.iter() {
        set(q_tr_abort, Nil) |> ignore
        let mut item = item0
        if !atom(item) {
          print_star(dconvx(translate(item))) |> ignore
        } else {
          item = d_verbify(item)
          let t_item = compile_function(item)
          if symval(q_tr_abort).truthy() {
            t_error = print_abort_msg(item, q_compfile)
          } else {
            if symval(q_d_compgrind).truthy() {
              mformat(list([out, Str("~2%;; Function ~:@M~%"), item])) |> ignore
            }
            print_star(t_item) |> ignore
          }
        }
      }
      Nil
    })
    |> ignore
    Str(out_file_name)
  })
}

///|
/// COMPILE-FUNCTION
fn compile_function(f : Value) -> Value raise {
  tr_format(Str("~%Translating ~:@M"), list1(f)) |> ignore
  let fun = tr_mfun(f)
  if symval(q_tr_abort).truthy() {
    Nil
  } else {
    fun
  }
}

///|
/// $COMPILE_FILE
fn d_compile_file(
  input_file : Value,
  bin_file? : Value = Nil,
  translation_output_file? : Value = Nil,
) -> Value raise {
  let mut input_file = maxima_string(input_file)
  let mut bin_file = bin_file
  let mut translation_output_file = translation_output_file
  if bin_file.truthy() {
    bin_file = maxima_string(bin_file)
  }
  if translation_output_file.truthy() {
    translation_output_file = maxima_string(translation_output_file)
  }
  let result = if transs__pathname_type(input_file).to_upper() == "LISP" {
    list2(list1(q_mlist), input_file)
  } else {
    let r = translate_file(input_file, translation_output_file)
    input_file = caddr(r)
    r
  }
  // (compile-file input-file :output-file bin-file): the port has no Lisp
  // compiler; the "compiled" file is a copy of the Lisp source, which LOAD
  // reads and evaluates.
  let out = if bin_file.truthy() {
    princ_to_string(bin_file)
  } else {
    princ_to_string(
      alter_pathname(input_file, list2(q_kw_type, Str("fasl"))),
    )
  }
  let bin_file = (fn() -> Value raise {
    write_file(out, read_file(princ_to_string(input_file)))
    Str(out)
  })() catch {
    _ => Nil
  }
  append(result, list1(bin_file))
}

///|
/// MAXIMA-STRING
fn maxima_string(symb : Value) -> Value raise {
  print_invert_case(symb)
}

///|
/// $TRANSLATE_FILE
fn d_translate_file(input_file : Value, output_file? : Value = Nil) -> Value raise {
  let input_file = maxima_string(input_file)
  let output_file = if output_file.truthy() {
    maxima_string(output_file)
  } else {
    output_file
  }
  translate_file(input_file, output_file)
}

///|
/// PPRINT-DEFMTRFUN: the pretty printer for DEFMTRFUN forms (the port's
/// pretty printer lays out every form the same way).
fn pprint_defmtrfun(stream : Value, s : Value) -> Value raise {
  transs__prin1(s, stream, true)
  Nil
}

///|
/// CALL-BATCH1
fn call_batch1(in_stream : Value, out_stream : Value) -> Value raise {
  cleanup() |> ignore
  // we want the thing to start with a newline..
  newline(in_stream) |> ignore
  while true {
    let expr = mread(list1(in_stream))
    if !(expr.truthy() && consp(expr)) {
      break
    }
    let transl = translate_macexpr_toplevel(caddr(expr))
    if symval(q_ear_pretty_print_translation).truthy() {
      // (pprint transl out-stream)
      write_char('\n', stream=out_stream)
      transs__prin1(transl, out_stream, true)
    } else {
      write_string(princ_to_string(transl), stream=out_stream)
    }
  }
  Nil
}

///|
/// The type (extension) of a pathname string, "" if none.
fn transs__pathname_type(p : Value) -> String {
  let s = princ_to_string(p)
  let slash = match s.rev_find("/") {
    Some(i) => i + 1
    None => 0
  }
  let name = s.substring(start=slash)
  match name.rev_find(".") {
    Some(i) if i > 0 => name.substring(start=i + 1)
    _ => ""
  }
}

///|
/// ALTER-PATHNAME: `(make-pathname :defaults pathname . options)`; the
/// options :TYPE and :NAME are supported.
fn alter_pathname(pathname : Value, options : Value) -> Value raise {
  let s = princ_to_string(pathname)
  let slash = match s.rev_find("/") {
    Some(i) => i + 1
    None => 0
  }
  let dir = s.substring(end=slash)
  let file = s.substring(start=slash)
  let (name0, type0) : (String, String?) = match file.rev_find(".") {
    Some(i) if i > 0 => (file.substring(end=i), Some(file.substring(start=i + 1)))
    _ => (file, None)
  }
  let mut name = name0
  let mut type_ = type0
  let mut o = options
  while o is Cons(_) {
    let k = car(o)
    let v = cadr(o)
    if eq(k, q_kw_type) {
      type_ = if v is Nil { None } else { Some(princ_to_string(v)) }
    } else if eq(k, q_kw_name) {
      name = princ_to_string(v)
    }
    o = cddr(o)
  }
  Str(
    dir +
    name +
    (match type_ {
      Some(t) => "." + t
      None => ""
    }),
  )
}

///|
/// DELETE-WITH-SIDE-EFFECTS-IF: rudimentary DELETE-IF which, however, is
/// guaranteed to call the function TEST exactly once for each element of
/// LIST, from left to right.
fn delete_with_side_effects_if(test_ : Value, list_ : Value) -> Value raise {
  let mut list_ = list_
  while list_.truthy() && funcall(test_, [car(list_)]).truthy() {
    list_ = cdr(list_)
  }
  let mut l = list_
  while cdr(l).truthy() {
    if funcall(test_, [cadr(l)]).truthy() {
      rplacd(l, cddr(l)) |> ignore
    } else {
      l = cdr(l)
    }
  }
  list_
}

///|
/// INSERT-NECESSARY-FUNCTION-DECLARES: write to STREAM two lists: the
/// functions which are known to be translated without actually being in
/// the list passed to $DECLARE_TRANSLATED, and those which are not known to
/// be translated.
fn insert_necessary_function_declares(stream : Value) -> Value raise {
  let mut hint : Value = Nil
  set(
    q_ear_untranslated_functions_called,
    delete_with_side_effects_if(
      lfunc("insert-necessary-function-declares-test", args => {
        let v = arg(args, 0)
        let translated = {
          let a = get(v, q_once_translated)
          if a.truthy() {
            a
          } else {
            get(v, q_translated)
          }
        }
        let r = if translated.truthy() {
          translated
        } else if fboundp(v) && mget(v, q_mexpr) is Nil {
          // might be traced
          t
        } else {
          get(v, q_mfexpr_star)
        }
        if translated.truthy() &&
          memq(v, symval(q_ear_declared_translated_functions)) is Nil {
          hint = cons(v, hint)
        }
        r
      }),
      symval(q_ear_untranslated_functions_called),
    ),
  )
  |> ignore
  if hint.truthy() {
    format(
      stream,
      "~2%/* The compiler might be able to optimize some function calls if you prepend the following declaration to your Maxima code: */~%",
      [],
    )
    |> ignore
    mgrind(
      list3(
        list1(q_d_eval_when),
        q_d_translate,
        cons(list1(q_d_declare_translated), hint),
      ),
      stream,
    )
    |> ignore
    format(stream, "$", []) |> ignore
  }
  if symval(q_ear_untranslated_functions_called).truthy() {
    format(
      stream,
      "~2%/* The following functions are not known to be translated:~%",
      [],
    )
    |> ignore
    mgrind(
      cons(list1(q_mlist), nreverse(symval(q_ear_untranslated_functions_called))),
      stream,
    )
    |> ignore
    format(stream, "$ */", []) |> ignore
  }
  fresh_line(stream~) |> ignore
  if hint.truthy() || symval(q_ear_untranslated_functions_called).truthy() {
    format(
      t,
      "~&translator: see the 'unlisp' file for possible optimizations.~%",
      [],
    )
    |> ignore
  }
  Nil
}

///|
/// PRINT-TRANSL-HERALD
fn print_transl_herald(stream : Value) -> Value raise {
  let (secs, mins, hours, day, month, year, _, dst, tz) = commac__decode_universal_time(
    commac__get_universal_time(),
    Nil,
  )
  // TIMEZONE-ISO8601-NAME (borrowed from CMUCL)
  let tzname : Value = {
    let tz = num_neg(tz)
    if dst is Nil && zerop(tz) {
      Str("Z")
    } else {
      let (hrs, minutes) = num_truncate(
        if dst.truthy() {
          num_add(tz, Fix(1L))
        } else {
          tz
        },
      )
      format(Nil, "~C~2,'0D:~2,'0D", [
        Char(if minusp(tz) { '-' } else { '+' }),
        num_abs(hrs),
        num_abs(truncate1(num_mul(minutes, Fix(60L)))),
      ])
    }
  }
  format(stream, "; Translated on: ~D-~2,'0D-~2,'0D ~2,'0D:~2,'0D:~2,'0D~A~%", [
    year, month, day, hours, mins, secs, tzname,
  ])
  |> ignore
  format(stream, "; Maxima version: ~A~%", [symval(q_ear_autoconf_version)])
  |> ignore
  format(stream, "; Lisp implementation: ~A~%", [
    Str(macsys__lisp_implementation_type()),
  ])
  |> ignore
  format(stream, "; Lisp version: ~A~%;~%", [
    Str(macsys__lisp_implementation_version()),
  ])
  |> ignore
  format(stream, "; Translator state vars:~%;~%", []) |> ignore
  for v in cdr(symval(q_d_tr_state_vars)).iter() {
    mformat(list([stream, Str(";   ~:M: ~:M;~%"), v, symval(v)])) |> ignore
  }
  Nil
}

///|
/// TRANSLATE-FILE
fn translate_file(in_file_name : Value, out_file_name : Value) -> Value raise {
  let bs = bind_all([
    (q_ear_translation_msgs_files, Nil),
    (q_ear_untranslated_functions_called, Nil),
    (q_ear_declared_translated_functions, Nil),
  ])
  defer unbind_all(bs)
  transm__with_transl_state(() => {
    set(q_ear_in_translate_file, t) |> ignore
    let translated_file = alter_pathname(
      if out_file_name.truthy() {
        out_file_name
      } else {
        in_file_name
      },
      list2(q_kw_type, Str("LISP")),
    )
    let warn_file = alter_pathname(in_file_name, list2(q_kw_type, Str("UNLISP")))
    let in_name = princ_to_string(in_file_name)
    let in_stream = open_input_file(in_name)
    let out_stream = make_string_output_stream()
    let warn_stream = make_string_output_stream()
    set(q_ear_translation_msgs_files, list1(warn_stream)) |> ignore
    if symval(q_d_tr_file_tty_messagesp).truthy() {
      set(
        q_ear_translation_msgs_files,
        cons(symval(standard_output), symval(q_ear_translation_msgs_files)),
      )
      |> ignore
    }
    format(
      out_stream,
      ";;; -*- Mode: Lisp; package:maxima; syntax:common-lisp ;Base: 10 -*- ;;;~%~%",
      [],
    )
    |> ignore
    print_transl_herald(out_stream) |> ignore
    format(out_stream, "~%(in-package :maxima)~%", []) |> ignore
    format(warn_stream, "This is the unlisp file for ~A~%", [Str(in_name)])
    |> ignore
    mformat(
      list([
        symval(q_ear_terminal_io),
        Str("translator: begin translating ~A.~%"),
        Str(in_name),
      ]),
    )
    |> ignore
    dskfn__with_io_syntax(() => call_batch1(in_stream, out_stream)) |> ignore
    insert_necessary_function_declares(warn_stream) |> ignore
    // WITH-OPEN-FILE: the files are kept only when the translation does not
    // exit abnormally.
    write_file(
      princ_to_string(translated_file),
      get_output_stream_string(out_stream),
    )
    write_file(princ_to_string(warn_file), get_output_stream_string(warn_stream))
    // BATCH1 calls TRANSLATE-MACEXPR-toplevel on each expression read.
    list4(list1(q_mlist), Str(in_name), translated_file, warn_file)
  })
}

///|
/// PRINT*
fn print_star(p : Value) -> Value raise {
  if !atom(p) {
    let pretty = symval(q_d_compgrind).truthy() ||
      symval(transs__q_print_pretty).truthy()
    transs__prin1(p, symval(q_transl_file), pretty)
    terpri(stream=symval(q_transl_file))
  }
  Nil
}

///|
/// PRINT-ABORT-MSG
fn print_abort_msg(fun : Value, from : Value) -> Value raise {
  tr_format(
    Str(
      "compfile: failed to translate ~:@M.~%~A will continue, but file output will be aborted.~%",
    ),
    list2(fun, from),
  )
}

///|
/// $TRANSLATE
fn d_translate(functs : Value) -> Value raise {
  let mut functs = cdr(functs)
  if functs.truthy() && stringp(car(functs)) {
    return merr(
      "translate: call 'translate_file' to translate a file; found: ~M",
      [car(functs)],
    )
  }
  if memq(q_d_functions, functs).truthy() || memq(q_d_all, functs).truthy() {
    functs = mapcar(x => caar(x), cdr(symval(q_d_functions)))
  }
  let mut v : Value = Nil
  for f in functs.iter() {
    if atom(f) {
      let it = translate_function(d_verbify(f))
      if it.truthy() {
        v = cons(it, v)
      }
    } else {
      tr_format(
        Str("error: 'translate' argument must be an atom; found: ~M~%"),
        list1(f),
      )
      |> ignore
    }
  }
  cons(list1(q_mlist), nreverse(v))
}

///|
/// $COMPILE: translate, then compile the named translated functions. The
/// port has no Lisp compiler: the translated definitions are already
/// installed by the Lisp evaluator.
fn d_compile(form : Value) -> Value raise {
  meval(cons(list1(q_d_translate), cdr(form)))
}

///|
fn init_transs() -> Unit raise {
  for v in [
    q_d_tr_file_tty_messagesp, q_transl_file, q_d_compgrind, q_d_tr_true_name_of_file_being_translated,
    q_d_tr_state_vars,
  ] {
    defmvar(v, val=symval(v), Nil) |> ignore
  }
}
