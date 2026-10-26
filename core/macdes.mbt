// Port of src/macdes.lisp: example(), create_list, describe/apropos, and
// the display of help topics (as text from the info files, or in a
// browser from the html manual).

///|
/// (read st nil nil) of the topic that follows "&&" in the manual demo
/// file: a symbol token.  NIL at end of file.
fn macdes__read_topic(st : Value) -> Value raise {
  // skip whitespace
  while true {
    match peek_char(stream=st, eof_value=Nil) {
      Char(c) if c == ' ' || c == '\t' || c == '\n' || c == '\r' ||
        c == '\u{0C}' => read_char(stream=st) |> ignore
      _ => break
    }
  }
  let tok = StringBuilder::new()
  while true {
    match peek_char(stream=st, eof_value=Nil) {
      Char(c) if !(
          c == ' ' ||
          c == '\t' ||
          c == '\n' ||
          c == '\r' ||
          c == '(' ||
          c == ')' ||
          c == ';' ||
          c == '"' ||
          c == '\''
        ) => {
        read_char(stream=st) |> ignore
        tok.write_char(c)
      }
      _ => break
    }
  }
  let s = tok.to_string()
  if s == "" {
    Nil
  } else {
    lread(s)
  }
}

///|
fn d_example(l : Value) -> Value raise {
  let mut example = second(l)
  if symbolp(example) {
    // Coerce a symbol to be a string.  Remove the first character if it
    // is a dollar sign.
    example = Str(char_list_to_string(exploden(stripdollar(example))))
  }
  if !stringp(example) {
    merr("example: argument must be a symbol or a string; found: ~M", [
      example,
    ])
    |> ignore
  }
  // Downcase the string. $example is not case sensitive.
  let example = string_downcase(lstring(example))
  let path = d_file_search1(
    symval(q_d_manual_demo),
    list2(list1(q_mlist), q_d_file_search_demo),
  )
  let st = open_input_file(lstring(path))
  let mut all : Value = Nil
  // again: find the topic
  let mut found = false
  while !found {
    let mut tem = read_char(stream=st, eof_value=Nil)
    if tem is Nil {
      break
    }
    if !(tem is Char('&')) {
      continue
    }
    tem = read_char(stream=st, eof_value=Nil)
    if !(tem is Char('&')) {
      continue
    }
    // so we are just after having read &&
    let topic = macdes__read_topic(st)
    if topic is Nil {
      break
    }
    // Coerce the topic in tem to be a string.
    let topic = char_list_to_string(exploden(topic))
    if topic == example {
      found = true
    } else {
      all = cons(Str(topic), all)
    }
  }
  if !found {
    // notfound
    set(q_ear_need_prompt, t) |> ignore
    return if length(l) == 1 {
      cons(list1(q_mlist), nreverse(all))
    } else {
      mtell(
        list([
          Str(
            "example: ~M not found. 'example();' returns the list of known examples.~%",
          ),
          Str(example),
        ]),
      )
      |> ignore
      q_d_done
    }
  }
  // At this stage we read maxima forms and print and eval until a peek
  // sees '&' as the first character of next expression, but at first skip
  // over whitespaces.
  while true {
    let mut tem = peek_char(stream=st, eof_value=Nil)
    if tem is Char(c) &&
      (c == '\t' || c == ' ' || c == '\n' || c == '\r' || c == '\u{0C}') {
      // Found whitespace. Read char and look for next char.  The && label
      // can be positioned anywhere before the next topic.
      read_char(stream=st) |> ignore
      continue
    }
    if tem is Nil || tem is Char('&') {
      set(q_ear_need_prompt, t) |> ignore
      return q_d_done
    }
    tem = dbm_read(stream=st, eof_error_p=Nil, eof_value=Nil)
    set(q_d_linenum, num_add(symval(q_d_linenum), Fix(1L))) |> ignore
    let c_tag = makelabel(symval(q_d_inchar))
    if !symval(q_d_nolabels).truthy() {
      set(c_tag, nth(2, tem)) |> ignore
    }
    with_special(q_d_display2d, Nil, () => displa(
      list([list1(q_mlabel), c_tag, nth(2, tem)]),
    ))
    |> ignore
    set(q_d_op_pct, meval_star(nth(2, tem))) |> ignore
    let d_tag = makelabel(symval(q_d_outchar))
    if !symval(q_d_nolabels).truthy() {
      set(d_tag, symval(q_d_op_pct)) |> ignore
    }
    if eq(caar(tem), q_displayinput) {
      displa(list([list1(q_mlabel), d_tag, symval(q_d_op_pct)])) |> ignore
    }
  }
  q_d_done
}

///|
fn mread_noprompt(read_args : Value) -> Value raise {
  with_specials(
    [(q_ear_mread_prompt, Str("")), (q_ear_prompt_on_read_hang, Nil)],
    () => {
      let read_args = if read_args is Nil {
        list1(symval(standard_input))
      } else {
        read_args
      }
      caddr(mread(read_args))
    },
  )
}

// Some list creation utilities.

///|
fn d_create_list(l : Value) -> Value raise {
  cons(list1(q_mlist), create_list1(cadr(l), cddr(l)))
}

///|
fn create_list1(form : Value, l : Value) -> Value raise {
  if l is Nil {
    return list1(meval(form))
  }
  let var1 = first(l)
  let mut lis = second(l)
  let mut l = cddr(l)
  if !symbolp(var1) {
    merr("create_list: expected a symbol; found: ~A", [var1]) |> ignore
  }
  lis = meval(lis)
  let vars = list1(var1)
  mlisp__mbinding(vars, vars, Nil, fn() {
    if numberp(lis) {
      let top = meval(car(l))
      l = cdr(l)
      if numberp(top) {
        // (loop for i from lis to top do (mset var1 i) append ...)
        let acc = Collector::new()
        let mut i = lis
        while num_le(i, top) {
          mset(var1, i) |> ignore
          acc.append_list(create_list1(form, l))
          i = num_add(i, Fix(1L))
        }
        return acc.result()
      }
    }
    if d_listp(lis).truthy() {
      let acc = Collector::new()
      for v in cdr(lis).iter() {
        mset(var1, v) |> ignore
        acc.append_list(create_list1(form, l))
      }
      acc.result()
    } else {
      merr("create_list: unexpected arguments.", [])
    }
  })
}

// The documentation is now in INFO format and can be printed using tex, or
// viewed using info or gnu emacs or using a web browser.  All versions of
// maxima have a builtin info retrieval mechanism.

///|
fn d_describe(x : Value) -> Value raise {
  let topic = d_sconcat(list1(cadr(x)))
  let exact_p = caddr(x) is Nil || eq(caddr(x), sym("$exact"))
  if exact_p {
    info_info_exact(topic)
  } else {
    info_info_inexact(topic)
  }
}

///|
/// CL `(apropos-list s :maxima)`: every symbol whose name contains `s`,
/// compared with CHAR-EQUAL (as SBCL does).
fn macdes__apropos_list(s : String) -> Array[Value] {
  let needle = s.to_lower()
  let acc : Array[Value] = []
  for sy in all_symbols() {
    if sy.name.to_lower().contains(needle) {
      acc.push(Sym(sy))
    }
  }
  acc
}

///|
fn d_apropos(s : Value) -> Value raise {
  let s0 = car(margs(s))
  let str = match s0 {
    Str(str) => str
    Sym(_) => symbol_name(stripdollar(s0))
    _ =>
      return merr("apropos: argument must be a string or symbol; found: ~M", [
        s0,
      ])
  }
  // A list of all Maxima names which contain the string S.  Filter the
  // names which are Maxima User symbols starting with % or $ and remove
  // duplicates.  DELETE-IF-NOT keeps the symbols themselves;
  // REMOVE-DUPLICATES keeps the last occurrence of each.
  let kept : Array[Value] = [list1(q_mlist)]
  for x in macdes__apropos_list(str) {
    let name = symbol_name(x)
    if name != "" && (name.has_prefix("$") || name.has_prefix("%")) {
      kept.push(x)
    }
  }
  let res = Collector::new()
  for i, x in kept {
    let mut later = false
    for j in (i + 1)..<kept.length() {
      if eq(kept[j], x) {
        later = true
        break
      }
    }
    if !later {
      res.add(x)
    }
  }
  res.result()
}

// Function to encode special characters in a URL string

///|
fn needs_encoding_p(char_ : Value) -> Value raise {
  let c = match char_ {
    Char(c) => c
    _ => return Nil
  }
  let special = "$*! \"'?<>&%"
  let mut i = 0
  for d in special {
    if d == c {
      return int(i)
    }
    i += 1
  }
  Nil
}

///|
fn encode_char(char_ : Value) -> Value raise {
  match char_ {
    Char(c) => format(Nil, "%~2,'0X", [int(c.to_int())])
    _ => format(Nil, "%~2,'0X", [Nil])
  }
}

///|
fn url_encode(url : Value) -> Value raise {
  let sb = StringBuilder::new()
  for c in lstring(url) {
    if needs_encoding_p(Char(c)).truthy() {
      sb.write_string(lstring(encode_char(Char(c))))
    } else {
      sb.write_char(c)
    }
  }
  Str(sb.to_string())
}

///|
/// Display help in browser instead of the terminal
fn display_html_help(x : Value) -> Value raise {
  // The pattern is basically " <nnn>" where "nnn" is any number of digits.
  let topic = d_sconcat(list1(x))
  let found_it = gethash(topic, symval(q_ear_html_index))
  if symval(q_ear_debug_display_html_help).truthy() {
    format(symval(q_ear_debug_io), "topic = ~S~%", [topic]) |> ignore
    format(symval(q_ear_debug_io), "found-it = ~S~%", [found_it]) |> ignore
  }
  if found_it is Nil {
    return Nil
  }
  let base_name = car(found_it)
  let id = cdr(found_it)
  let base = princ_to_string(base_name)
  let mut url : Value = Str(
    // If BASE-NAME is an absolute path, use "FILE://" as the protocol.
    // Otherwise use $URL_BASE.
    (if base.has_prefix("/") {
      "file://"
    } else {
      princ_to_string(symval(q_d_url_base))
    }) +
    "/" +
    base +
    "#" +
    princ_to_string(id),
  )
  // $system will concatenate the words in list cmd_list to create the
  // command to be executed
  let mut cmd_list : Value = Nil
  url = url_encode(url)
  if symval(q_ear_debug_display_html_help).truthy() {
    format(symval(q_ear_debug_io), "URL: ~S~%", [url]) |> ignore
  }
  if boundp(q_ear_autoconf_windows) &&
    string_equal(princ_to_string(symval(q_ear_autoconf_windows)), "true") &&
    !string_equal(princ_to_string(symval(q_d_browser)), "start") {
    // In Windows if the browser is not the default, its name should be
    // placed after "start".
    cmd_list = append(cmd_list, list1(Str("start")))
  }
  cmd_list = append(cmd_list, list2(symval(q_d_browser), url))
  if symval(q_ear_debug_display_html_help).truthy() {
    format(symval(q_ear_debug_io), "Command: ~{~a ~}~%", [cmd_list]) |> ignore
  }
  d_system(cmd_list)
}

///|
fn display_html_topics(wanted : Value) -> Value raise {
  if symval(q_ear_debug_display_html_help).truthy() {
    format(symval(q_ear_debug_io), "wanted = ~S~%", [wanted]) |> ignore
  }
  for w in wanted.iter() {
    let entry = second(w)
    display_html_help(car(entry)) |> ignore
  }
  Nil
}

///|
fn display_text_topics(wanted : Value) -> Value raise {
  for item in wanted.iter() {
    let doc = info_read_info_text(first(item), second(item))
    if doc.truthy() {
      format(t, "~A~%~%", [doc]) |> ignore
    } else {
      format(
        t,
        "Unable to find documentation for `~A'.~%Possible bug maxima-index.lisp or build_index.pl?~%",
        [first(second(item))],
      )
      |> ignore
    }
  }
  Nil
}

///|
/// When a frontend is running, this function should be redefined to
/// display the help in whatever way the frontend wants to.
fn display_frontend_topics(wanted : Value) -> Value raise {
  ignore(wanted)
  merr("output_format_for_help: frontend not implemented.", [])
}

///|
/// When $output_format_for_help is set, this function validates the value
/// and sets *help-display-function* to the function to display the help
/// item in the specified format.
fn set_output_format_for_help(assign_var : Value, val : Value) -> Value raise {
  // Don't need assign-var here.  It should be $output_format_for_help
  // since this function is only called when $output_format_for_help is
  // assigned.
  ignore(assign_var)
  if eq(val, sym("$text")) {
    set(q_ear_help_display_function, q_display_text_topics)
  } else if eq(val, sym("$html")) {
    set(q_ear_help_display_function, q_display_html_topics) |> ignore
    if symval(q_ear_verify_html_index_on_output_format).truthy() {
      set(q_ear_verify_html_index_on_output_format, Nil) |> ignore
      // Verify the html index.  This happens only when the output format
      // is set to html the first time.  It is also independent of the
      // value of *verify-html-index* (set via the command-line option
      // --verify-html-index).
      d_verify_html_index()
    } else {
      Nil
    }
  } else if eq(val, sym("$frontend")) {
    if symval(q_d_maxima_frontend).truthy() {
      set(q_ear_help_display_function, q_display_frontend_topics)
    } else {
      merr(
        "output_format_for_help set to frontend, but no frontend is running.",
        [],
      )
    }
  } else {
    merr("output_format_for_help should be one of text, html, or frontend: ~M", [
      val,
    ])
  }
}

///|
fn init_macdes() -> Unit raise {
  ()
}
