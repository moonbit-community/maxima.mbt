// Port of src/macsys.lisp: the ``New'' Macsyma System Stuff -- the
// read-eval-print loop (CONTINUE, MACSYMA-TOP-LEVEL), break loops,
// RETRIEVE, $read, build_info, writefile and friends, timing functions.
//
// Differences forced by the port:
// - The Lisp debugger hook is emulated: a Lisp-level error escaping an
//   evaluation in CONTINUE prints "Maxima encountered a Lisp error" and
//   continues with the next input, like MAXIMA-LISP-DEBUGGER.
// - CL two-way streams do not exist; *QUERY-IO-INPUT* (a port-only special)
//   names the input side when *QUERY-IO* is used as a two-way stream.
// - Memory accounting (used-area), dribble transcripts, $system, $room and
//   $ed are not available.

///|
/// INTERNAL-TIME-UNITS-PER-SECOND (as in SBCL).
let macsys__units_per_second : Double = 1000000.0

///|
/// GET-INTERNAL-RUN-TIME
fn macsys__run_time() -> Value {
  int64((cpu_time() * macsys__units_per_second).to_int64())
}

///|
/// GET-INTERNAL-REAL-TIME
fn macsys__real_time() -> Value {
  int64(wall_time_ms().reinterpret_as_int64() * 1000L)
}

///|
let macsys__t0_real : Ref[Value] = Ref(Fix(0L))

///|
let macsys__t0_run : Ref[Value] = Ref(Fix(0L))

///|
/// The port-only special naming the input side of *QUERY-IO*.
let macsys__q_query_input : Value = sym("*query-io-input*")

///|
/// Where RETRIEVE reads its answers from.
fn macsys__query_in() -> Value {
  let qi = symval(macsys__q_query_input)
  if qi is Stream(_) {
    return qi
  }
  match symval(q_ear_query_io) {
    Stream(st) as q if st.is_input => q
    _ => symval(standard_input)
  }
}

///|
/// Where RETRIEVE writes its prompts to.
fn macsys__query_out() -> Value {
  match symval(q_ear_query_io) {
    Stream(st) as q if !st.is_input => q
    Stream(_) => make_string_output_stream()
    _ => symval(standard_output)
  }
}

///|
fn macsys__lisp_implementation_type() -> String {
  "MoonBit"
}

///|
fn macsys__lisp_implementation_version() -> String {
  "0.1"
}

///|
fn macsys__version() -> Value {
  if boundp(q_ear_autoconf_version) && symval(q_ear_autoconf_version).truthy() {
    symval(q_ear_autoconf_version)
  } else {
    Str("5.50post")
  }
}

///|
/// Decoded UTC time: (sec, min, hour, day, month, year) for Unix seconds.
fn macsys__decode_time(secs : Int64) -> (Int, Int, Int, Int, Int, Int) {
  let days = secs / 86400L
  let rem = secs % 86400L
  let hour = (rem / 3600L).to_int()
  let min = (rem % 3600L / 60L).to_int()
  let sec = (rem % 60L).to_int()
  // Civil-from-days (Howard Hinnant).
  let z = days + 719468L
  let era = (if z >= 0L { z } else { z - 146096L }) / 146097L
  let doe = z - era * 146097L
  let yoe = (doe - doe / 1460L + doe / 36524L - doe / 146096L) / 365L
  let y = yoe + era * 400L
  let doy = doe - (365L * yoe + yoe / 4L - yoe / 100L)
  let mp = (5L * doy + 2L) / 153L
  let d = (doy - (153L * mp + 2L) / 5L + 1L).to_int()
  let m = (if mp < 10L { mp + 3L } else { mp - 9L }).to_int()
  let y = (if m <= 2 { y + 1L } else { y }).to_int()
  (sec, min, hour, d, m, y)
}

///|
fn macsys__now_decoded() -> (Int, Int, Int, Int, Int, Int) {
  macsys__decode_time(wall_time_ms().reinterpret_as_int64() / 1000L)
}

///|
fn toplevel_macsyma_eval(x : Value) -> Value raise {
  match macsys__toplevel_macsyma_eval_cell.val {
    Some(f) => f(x)
    None => macsys__toplevel_macsyma_eval_base(x)
  }
}

///|
/// The function cell of TOPLEVEL-MACSYMA-EVAL. Share packages (share/contrib/unit/unit-functions.lisp) redefine
/// it at load time, as CL Maxima does with DEFUN; callers in the port reach
/// the current definition through this cell (None: the standard one).
let macsys__toplevel_macsyma_eval_cell : Ref[((Value) -> Value raise)?] = Ref(None)

///|
fn macsys__toplevel_macsyma_eval_base(x : Value) -> Value raise {
  // Catch rat-err's here.
  suprv1__rat_error_to_merror(() => meval_star(x))
}

///|
fn used_area(unused? : Value = Nil) -> Value raise {
  ignore(unused)
  Fix(0L)
}

///|
/// MREAD-NOPROMPT (macdes.lisp)
fn macsys__mread_noprompt(stream : Value, eof : Value) -> Value raise {
  with_specials(
    [(q_ear_mread_prompt, Str("")), (q_ear_prompt_on_read_hang, Nil)],
    () => caddr(mread(list([stream, eof]))),
  )
}

///|
/// What MERROR does at top level when it is not caught: print the message
/// and return to the top level.  Used when a Maxima error condition reaches
/// CONTINUE unhandled.
fn macsys__report_toplevel_error() -> Value raise {
  with_special(standard_output, symval(error_output), () => {
    if symval(q_d_errormsg).truthy() {
      d_errormsg() |> ignore
    }
    fresh_line() |> ignore
    suprv1__fmt(t, "~& -- an error. To debug this try: debugmode(true);~%", [])
    |> ignore
    finish_output()
    Value::Nil
  })
  |> ignore
  if symval(q_ear_quit_on_error).truthy() {
    d_quit(exit_code=Fix(1L)) |> ignore
  }
  throw_tag(q_macsyma_quit, q_maxima_error)
}

///|
/// MAXIMA-LISP-DEBUGGER, entered with the message of a Lisp error.
fn macsys__lisp_error(msg : String) -> Unit raise {
  suprv1__fmt(t, "~&Maxima encountered a Lisp error:~%~% ~A", [Str(msg)])
  |> ignore
  suprv1__fmt(
    t,
    "~&~%Automatically continuing.~%To enable the Lisp debugger set *debugger-hook* to nil.~%",
    [],
  )
  |> ignore
  finish_output()
}

///|
/// Marker returned by one iteration of CONTINUE when it must return $done.
let macsys__done_marker : Value = gensym(prefix="done")

///|
fn continue_(
  input_stream? : Value,
  batch_or_demo_flag? : Value = Nil,
  one_shot? : Value = Nil,
) -> Value raise {
  let st = Ref(
    match input_stream {
      Some(s) => s
      None => symval(standard_input)
    },
  )
  let flag = Ref(batch_or_demo_flag)
  if symval(q_ear_maxima_run_string).truthy() {
    flag.val = q_kw_batch
  }
  if eq(flag.val, q_kw_demo) {
    suprv1__fmt(
      t,
      "~%At the '~A' prompt, type ';' and <enter> to proceed with the demonstration.~&To abort the demonstration, type 'end;' or 'eof;' and then <enter>.~%",
      [Str(princ_to_string(stripdollar(symval(q_d_prompt))))],
    )
    |> ignore
  }
  catch_tag(q_abort_demo, () => {
    let eof = list1(Nil)
    let mut finish = false
    while !finish {
      let r = catch_tag(q_return_from_debugger, () => macsys__continue_once(
        st, flag, eof,
      ) catch {
        e if suprv1__control_transfer(e) => raise e
        e if is_maxima_error(e) => macsys__report_toplevel_error()
        e => {
          macsys__lisp_error(suprv1__error_text(e))
          t
        }
      })
      if physical_equal_value(r, macsys__done_marker) {
        return q_d_done
      }
      finish = one_shot.truthy()
    }
    Value::Nil
  })
}

///|
/// One iteration of the CONTINUE loop: read, echo, evaluate and display one
/// statement.
fn macsys__continue_once(
  st : Ref[Value],
  flag : Ref[Value],
  eof : Value,
) -> Value raise {
  if !checklabel(symval(q_d_inchar)).truthy() ||
    !checklabel(symval(q_d_outchar)).truthy() {
    set(q_d_linenum, num_add(symval(q_d_linenum), Fix(1L))) |> ignore
  }
  let c_tag = makelabel(symval(q_d_inchar))
  let prompt : Value = if flag.val.truthy() { Nil } else { main_prompt() }
  let r = with_special(q_ear_mread_prompt, prompt, () => {
    while true {
      let r = dbm_read(stream=st.val, eof_error_p=Nil, eof_value=eof)
      if consp(r) && mdebug__keywordp(car(r)) {
        break_call(car(r), cdr(r), q_break_command) |> ignore
        if !flag.val.truthy() && !physical_equal_value(st.val, symval(standard_input)) {
          st.val = symval(standard_input)
        }
        continue
      }
      return r
    }
    Value::Nil
  })
  suprv1__fmt(t, "~a", [symval(q_ear_general_display_prefix)]) |> ignore
  if physical_equal_value(r, eof) {
    return macsys__done_marker
  }
  set(q_d_op__, caddr(r)) |> ignore
  if !symval(q_d_nolabels).truthy() {
    set(c_tag, symval(q_d_op__)) |> ignore
  }
  if flag.val.truthy() && !symval(q_ear_suppress_input_echo).truthy() {
    with_special(q_d_display2d, Nil, () => displa(
      list([list1(q_mlabel), c_tag, symval(q_d_op__)]),
    ))
    |> ignore
  }
  let time_before = macsys__run_time()
  let etime_before = macsys__real_time()
  let area_before = used_area()
  set(q_d_op_pct, toplevel_macsyma_eval(symval(q_d_op__))) |> ignore
  if !flag.val.truthy() && !physical_equal_value(st.val, symval(standard_input)) {
    st.val = symval(standard_input)
  }
  let etime_after = macsys__real_time()
  let time_after = macsys__run_time()
  let area_after = used_area()
  let time_used = to_double(num_sub(time_after, time_before)) /
    macsys__units_per_second
  let etime_used = to_double(num_sub(etime_after, etime_before)) /
    macsys__units_per_second
  set(
    q_accumulated_time,
    num_add(symval(q_accumulated_time), Flo(time_used)),
  )
  |> ignore
  let d_tag = makelabel(symval(q_d_outchar))
  if !symval(q_d_nolabels).truthy() {
    set(d_tag, symval(q_d_op_pct)) |> ignore
  }
  set(q_d_op_, symval(q_d_op__)) |> ignore
  if symval(q_d_showtime).truthy() {
    // we don't distinguish showtime:all?? /RJF
    suprv1__fmt(t, "Evaluation took ~,4F seconds (~,4F elapsed)", [
      Flo(time_used),
      Flo(etime_used),
    ])
    |> ignore
    let total_bytes = to_int64(num_sub(area_after, area_before))
    if total_bytes > 1024L * 1024L {
      suprv1__fmt(t, " using ~,3F MB.~%", [
        Flo(total_bytes.to_double() / (1024.0 * 1024.0)),
      ])
      |> ignore
    } else if total_bytes > 1024L {
      suprv1__fmt(t, " using ~,3F KB.~%", [Flo(total_bytes.to_double() / 1024.0)])
      |> ignore
    } else {
      suprv1__fmt(t, " using ~:D bytes.~%", [int64(total_bytes)]) |> ignore
    }
    finish_output()
  }
  if !symval(q_d_nolabels).truthy() {
    putprop(q_d_op_pct, cons(Flo(time_used), Fix(0L)), q_time) |> ignore
    putprop(d_tag, cons(Flo(time_used), Fix(0L)), q_time) |> ignore
  }
  if eq(caar(r), q_displayinput) {
    displa(list([list1(q_mlabel), d_tag, symval(q_d_op_pct)])) |> ignore
  }
  if eq(flag.val, q_kw_demo) {
    princ(break_prompt()) |> ignore
    finish_output()
    let mut quitting = false
    while true {
      match read_char(stream=symval(standard_input), eof_value=Nil) {
        Char('\u{0C}') => {
          fresh_line() |> ignore
          princ(break_prompt()) |> ignore
          finish_output()
        }
        Char('?') =>
          suprv1__fmt(
            t,
            "  Pausing. Type a ';' and <enter> to continue demo.~%",
            [],
          )
          |> ignore
        Char(' ') | Char(';') | Char('n') | Char('e') | Char('x') | Char('t') =>
          ()
        Char('\n') =>
          if quitting {
            throw_tag(q_abort_demo, Nil) |> ignore
          } else {
            break
          }
        Nil => break
        _ => quitting = true
      }
    }
  }
  // This is sort of a kludge -- eat newlines and blanks so that they don't
  // echo
  if flag.val.truthy() {
    while true {
      match read_char(stream=st.val, eof_value=Nil) {
        Char(c) =>
          if !(c == ' ' || c == '\n' || c == '\r' || c == '\t') {
            unread_char(c, stream=st.val)
            break
          }
        _ => {
          if symval(q_ear_maxima_run_string).truthy() {
            flag.val = Nil
            set(q_ear_maxima_run_string, Nil) |> ignore
            st.val = symval(standard_input)
            throw_tag(q_return_from_debugger, t) |> ignore
          }
          throw_tag(q_macsyma_quit, Nil) |> ignore
        }
      }
    }
  }
  Nil
}

///|
fn d_break(arg_list : Value) -> Value raise {
  let v = d_print(arg_list)
  mbreak_loop() |> ignore
  v
}

///|
fn mbreak_loop() -> Value raise {
  with_specials(
    [(standard_input, console_in), (standard_output, symval(q_ear_debug_io))],
    () => catch_tag(q_break_exit, () => {
      suprv1__fmt(
        t,
        "~%Entering a Maxima break point. Type 'exit;' to resume.",
        [],
      )
      |> ignore
      while true {
        fresh_line() |> ignore
        let form = with_special(q_ear_mread_prompt, break_prompt(), () => mread(
          list1(symval(standard_input)),
        ))
        if form is Nil {
          // End of input: leave the break loop.
          break
        }
        let r = caddr(form)
        if eq(r, q_d_exit) {
          throw_tag(q_break_exit, t) |> ignore
        }
        errset(() => displa(meval(r))) |> ignore
      }
      Value::Nil
    }),
  )
}

///|
fn merrbreak(arg? : Value = Nil) -> Value raise {
  suprv1__fmt(symval(q_ear_debug_io), "~%Merrbreak:~A", [arg]) |> ignore
  mbreak_loop()
}

///|
fn retrieve(msg : Value, flag : Value) -> Value raise {
  with_specials([(q_msg, msg), (q_flag, flag), (q_print_q, Nil)], () => {
    if !eq(flag, q_noprint) {
      set(q_print_q, t) |> ignore
    }
    let qout = macsys__query_out()
    if !symval(q_print_q).truthy() {
      set(q_print_q, t) |> ignore
      format_prompt(qout, Str(""), Nil) |> ignore
    } else if msg is Nil {
      format_prompt(qout, Str(""), Nil) |> ignore
    } else if atom(msg) {
      format_prompt(qout, Str("~A"), list1(msg)) |> ignore
      mterpri(ostream=qout) |> ignore
    } else if eq(flag, t) {
      format_prompt(qout, Str("~{~A~}"), list1(cdr(msg))) |> ignore
      mterpri(ostream=qout) |> ignore
    } else {
      format_prompt(qout, Str("~M"), list1(msg)) |> ignore
      mterpri(ostream=qout) |> ignore
    }
    let res = macsys__mread_noprompt(macsys__query_in(), Nil)
    princ(symval(q_ear_general_display_prefix), stream=qout) |> ignore
    if res is Nil {
      merr("RETRIEVE: End of file encountered.", [])
    } else {
      res
    }
  })
}

///|
fn d_eval_string_lisp(string_ : Value) -> (Value, Value) raise {
  if !stringp(string_) {
    merr("eval_string_lisp: Expected a string, got ~M.", [string_]) |> ignore
  }
  let mut values : Value = Nil
  let st = make_string_input_stream(lstring(string_))
  let eof = cons(Fix(0L), Fix(0L))
  while true {
    let input = lisp_read(st, eof)
    if physical_equal_value(input, eof) {
      break
    }
    values = list(lisp_eval_form_values(input))
  }
  // Mark the list as simplified
  (cons(list2(q_mlist, q_simp), values), Nil)
}

///|
fn d_read(l : Value) -> Value raise {
  meval(d_readonly(l))
}

///|
fn d_readonly(l : Value) -> Value raise {
  let prompt = if l.truthy() {
    string_right_trim(
      "n",
      with_output_to_string(s => with_special(standard_output, s, () => d_print(
        l,
      ))
      |> ignore),
    )
  } else {
    ""
  }
  let prompt = format_prompt(Nil, Str("~A"), list1(Str(prompt)))
  with_special(q_ear_mread_prompt, prompt, () => third(
    mread(list1(symval(standard_input))),
  ))
}

///|
fn d_bug_report() -> Value raise {
  let fe = symval(q_d_maxima_frontend).truthy()
  if fe {
    suprv1__fmt(
      t,
      "~%Please report bugs in maxima, the tool that does the actual maths, to:~%",
      [],
    )
    |> ignore
  } else {
    suprv1__fmt(t, "~%Please report bugs to:~%", []) |> ignore
  }
  suprv1__fmt(t, "    https://sourceforge.net/p/maxima/bugs~%", []) |> ignore
  suprv1__fmt(t, "To report a bug, you must have a Sourceforge account.~%", [])
  |> ignore
  if fe {
    suprv1__fmt(
      t,
      "~%Bugs affecting UI and display should be reported to the frontend's homepage.~%",
      [],
    )
    |> ignore
    if symval(q_d_maxima_frontend_bugreportinfo).truthy() {
      suprv1__fmt(t, "The front end provides the following info:~%~a~%", [
        symval(q_d_maxima_frontend_bugreportinfo),
      ])
      |> ignore
    } else {
      suprv1__fmt(
        t,
        "The front end doesn't provide any additional bug report info.~%",
        [],
      )
      |> ignore
    }
  }
  suprv1__fmt(
    t,
    "Please include the following information with your bug report:~%",
    [],
  )
  |> ignore
  suprv1__fmt(
    t,
    "-------------------------------------------------------------~%",
    [],
  )
  |> ignore
  // Display the 2D-formatted build information
  with_special(q_d_display2d, t, () => displa(d_build_info())) |> ignore
  suprv1__fmt(
    t,
    "-------------------------------------------------------------~%",
    [],
  )
  |> ignore
  suprv1__fmt(
    t,
    "The above information is also reported by the function 'build_info()'.~%~%",
    [],
  )
  |> ignore
  Str("")
}

///|
/// Build time of this image, formatted as "YYYY-MM-DD hh:mm:ss" (UTC);
/// taken when the system is initialized.
let macsys__build_time : Ref[String] = Ref("")

///|
fn d_build_info() -> Value raise {
  let cached = symval(q_ear_maxima_build_info)
  if cached.truthy() {
    return cached
  }
  let info = mfuncall(
    q_d_new,
    list1(
      list([
        list1(q_p_build_info),
        macsys__version(),
        Str(macsys__build_time.val),
        if boundp(q_ear_autoconf_host) && symval(q_ear_autoconf_host).truthy() {
          symval(q_ear_autoconf_host)
        } else {
          Str("")
        },
        ensure_readably_printable_string(Str(macsys__lisp_implementation_type())),
        ensure_readably_printable_string(
          Str(macsys__lisp_implementation_version()),
        ),
        symval(q_d_maxima_userdir),
        symval(q_d_maxima_tempdir),
        symval(q_d_maxima_objdir),
        symval(q_d_maxima_frontend),
        symval(q_d_maxima_frontend_version),
      ]),
    ),
  )
  set(q_ear_maxima_build_info, info)
}

///|
fn ensure_readably_printable_string(x : Value) -> Value raise {
  x
}

///|
fn dimension_build_info(form : Value, result : Value) -> Value raise {
  // Usually the result of (MFUNCALL '$@ ...) is a string, but ensure that
  // output makes sense even if it is not.
  let display_item = (item : Value, item_label : String) => {
    let v = mfuncall(q_d_op_at, list([form, item]))
    let s = item_label + ": " + char_list_to_string(mstring(v))
    let mut l : Value = Nil
    for c in s {
      l = cons(Char(c), l)
    }
    forcebreak(l, Fix(0L)) |> ignore
  }
  with_specials(
    [
      (q_bkptht, Fix(1L)),
      (q_bkptdp, Fix(0L)),
      (q_lines, Fix(0L)),
      (q_break, Fix(0L)),
    ],
    () => {
      forcebreak(result, Fix(0L)) |> ignore
      display_item(q_d_version, "Maxima-version")
      display_item(q_d_timestamp, "Maxima build date")
      display_item(q_d_host, "Host type")
      display_item(q_d_lisp_name, "Lisp implementation type")
      display_item(q_d_lisp_version, "Lisp implementation version")
      display_item(q_d_maxima_userdir, "User dir")
      display_item(q_d_maxima_tempdir, "Temp dir")
      display_item(q_d_maxima_objdir, "Object dir")
      display_item(q_d_maxima_frontend, "Frontend")
      if symval(q_d_maxima_frontend).truthy() {
        display_item(q_d_maxima_frontend_version, "Frontend version")
      }
      Nil
    },
  )
}

///|
fn macsyma_top_level(
  input_stream? : Value,
  batch_flag? : Value = Nil,
) -> Value raise {
  let input_stream = match input_stream {
    Some(s) => s
    None => symval(standard_input)
  }
  macsys__top_level(input_stream, batch_flag, true)
  Nil
}

///|
/// MACSYMA-TOP-LEVEL.  When EXIT is false, return instead of calling BYE
/// once the input is exhausted.
fn macsys__top_level(
  input_stream : Value,
  batch_flag : Value,
  exit : Bool,
) -> Unit raise {
  if symval(q_ear_maxima_started).truthy() {
    suprv1__fmt(t, "Maxima restarted.~%", []) |> ignore
  } else {
    if !symval(q_ear_maxima_quiet).truthy() {
      maxima_banner() |> ignore
    }
    set(q_ear_maxima_started, t) |> ignore
  }
  let finished = Ref(false)
  catch_tag(q_quit_to_lisp, () => {
    while !finished.val {
      catch_tag(q_continue, () => catch_tag(q_macsyma_quit, () => {
        continue_(input_stream~, batch_or_demo_flag=batch_flag) |> ignore
        suprv1__fmt(t, lstring(symval(q_ear_maxima_epilog)), []) |> ignore
        if exit {
          bye() |> ignore
        }
        finished.val = true
        Value::Nil
      }))
      |> ignore
    }
    Value::Nil
  })
  |> ignore
  finish_output()
}

///|
fn maxima_banner() -> Value raise {
  suprv1__fmt(t, lstring(symval(q_ear_maxima_prolog)), []) |> ignore
  suprv1__fmt(t, "~&Maxima ~a https://maxima.sourceforge.io~%", [
    macsys__version(),
  ])
  |> ignore
  suprv1__fmt(t, "using Lisp ~a ~a", [
    Str(macsys__lisp_implementation_type()),
    Str(macsys__lisp_implementation_version()),
  ])
  |> ignore
  suprv1__fmt(
    t,
    "~%Distributed under the GNU Public License. See the file COPYING.~%",
    [],
  )
  |> ignore
  suprv1__fmt(t, "Dedicated to the memory of William Schelter.~%", [])
  |> ignore
  suprv1__fmt(
    t,
    "The function bug_report() provides bug reporting information.~%",
    [],
  )
}

///|
fn throw_macsyma_top() -> Value raise {
  throw_tag(q_macsyma_quit, t)
}

///|
fn start_dribble(name : Value) -> Value raise {
  // DRIBBLE returns no values; transcripts are not recorded by the port.
  suprv1__fmt(t, "~&~A~&", [Str("NIL")]) |> ignore
  set(q_ear_appendfile_data, cons(name, symval(q_ear_appendfile_data)))
  |> ignore
  let (sec, min, hour, day, month, year) = macsys__now_decoded()
  suprv1__fmt(
    t,
    "~&/* Starts dribbling to ~A (~d/~d/~d, ~2,'0d:~2,'0d:~2,'0d).*/~&",
    [name, int(year), int(month), int(day), int(hour), int(min), int(sec)],
  )
  |> ignore
  q_d_done
}

///|
fn macsys__in_appendfile_data(name : Value) -> Bool {
  for x in symval(q_ear_appendfile_data).iter() {
    if lstring(string(x)) == lstring(string(name)) {
      return true
    }
  }
  false
}

///|
fn d_writefile(name : Value) -> Value raise {
  if macsys__in_appendfile_data(name) {
    merr("writefile: already in writefile, you must call closefile first.", [])
    |> ignore
  }
  start_dribble(name)
}

///|
fn d_appendfile(name : Value) -> Value raise {
  if macsys__in_appendfile_data(name) {
    merr("appendfile: already in appendfile, you must call closefile first.", [])
    |> ignore
  }
  start_dribble(name)
}

///|
fn d_closefile() -> Value raise {
  if symval(q_ear_appendfile_data).truthy() {
    suprv1__fmt(t, "~&~A~&", [Str("NIL")]) |> ignore
    let (sec, min, hour, day, month, year) = macsys__now_decoded()
    suprv1__fmt(
      t,
      "~&/* Quits dribbling to ~A (~d/~d/~d, ~2,'0d:~2,'0d:~2,'0d).*/~&",
      [
        car(symval(q_ear_appendfile_data)),
        int(year),
        int(month),
        int(day),
        int(hour),
        int(min),
        int(sec),
      ],
    )
    |> ignore
    set(q_ear_appendfile_data, cdr(symval(q_ear_appendfile_data))) |> ignore
  }
  q_d_done
}

///|
fn d_ed(x : Value) -> Value raise {
  ignore(x)
  merr("ed: not supported in this port", [])
}

///|
fn nsubstring(x : Value, y : Value) -> Value raise {
  subseq(x, to_int(y))
}

///|
fn filestrip(x : Value) -> Value raise {
  Str(princ_to_string(car(x)).substring(start=1))
}

///|
fn d_with_stdout(arg : Value) -> Value raise {
  let arg = cdr(arg)
  let output = meval(car(arg))
  let body = cdr(arg)
  let run = () => {
    let mut result : Value = Nil
    for v in body.iter() {
      result = meval(v)
    }
    result
  }
  if streamp(output) {
    return with_special(standard_output, output, run)
  }
  let fname = princ_to_string(output)
  let append_ = eq(symval(q_d_file_output_append), q_d_true) ||
    eq(symval(q_d_file_output_append), t)
  let s = make_string_output_stream()
  let write = () => {
    let old = if append_ && probe_file(fname) { read_file(fname) } else { "" }
    write_file(fname, old + get_output_stream_string(s))
  }
  let result = with_special(standard_output, s, run) catch {
    e => {
      write()
      raise e
    }
  }
  write()
  result
}

///|
fn d_sconcat(x : Value) -> Value raise {
  let sb = StringBuilder::new()
  for v in x.iter() {
    match v {
      Str(s) => sb.write_string(s)
      _ => sb.write_string(char_list_to_string(mstring(v)))
    }
  }
  Str(sb.to_string())
}

///|
fn d_system(args : Value) -> Value raise {
  ignore(args)
  merr("system: not supported in this port", [])
}

///|
fn d_room(arg? : Value) -> Value raise {
  ignore(arg)
  Nil
}

///|
fn maxima_lisp_debugger(
  condition : Value,
  me_or_my_encapsulation : Value,
) -> Value raise {
  ignore(me_or_my_encapsulation)
  macsys__lisp_error(princ_to_string(condition))
  throw_tag(q_return_from_debugger, t)
}

///|
fn initialize_real_and_run_time() -> Value raise {
  macsys__t0_real.val = macsys__real_time()
  macsys__t0_run.val = macsys__run_time()
  macsys__t0_run.val
}

///|
fn d_absolute_real_time() -> Value raise {
  // GET-UNIVERSAL-TIME: seconds since 1900-01-01.
  int64(wall_time_ms().reinterpret_as_int64() / 1000L + 2208988800L)
}

///|
fn d_elapsed_real_time() -> Value raise {
  let elapsed = num_sub(macsys__real_time(), macsys__t0_real.val)
  Flo(to_double(elapsed) / macsys__units_per_second)
}

///|
fn d_elapsed_run_time() -> Value raise {
  let elapsed = num_sub(macsys__run_time(), macsys__t0_run.val)
  Flo(to_double(elapsed) / macsys__units_per_second)
}

///|
/// Tries to manually trigger the lisp's garbage collector and returns true
/// if it knew how to do that.
fn d_garbage_collect() -> Value raise {
  Nil
}

// ---------------------------------------------------------------------------
// Entry points for a main program.

///|
/// Run Maxima's batch processing over the string S, like
/// `maxima --batch-string=S`: each statement is echoed with its %i label,
/// evaluated and displayed; errors are reported and processing continues.
/// Returns when the input is exhausted (without calling BYE).
fn maxima_batch_string(s : String, quiet? : Bool = false) -> Unit raise {
  let stream = make_string_input_stream(s)
  displa__interactive.val = false
  if quiet {
    set(q_ear_maxima_quiet, t) |> ignore
  }
  // see RETRIEVE: answers to questions come from the batch string.
  set(q_d_batch_answers_from_file, t) |> ignore
  with_specials(
    [
      (standard_input, stream),
      (q_ear_query_io, make_string_output_stream()),
      (macsys__q_query_input, stream),
    ],
    () => macsys__top_level(stream, q_kw_batch, false),
  )
}

///|
/// Run a Maxima batch file, like `maxima -b FILE`.
fn maxima_batch_file(path : String, quiet? : Bool = false) -> Unit raise {
  let stream = make_string_input_stream("batch(\"" + path + "\");")
  displa__interactive.val = false
  if quiet {
    set(q_ear_maxima_quiet, t) |> ignore
  }
  macsys__top_level(stream, q_kw_batch, false)
}

///|
/// Run the interactive read-eval-print loop on the console (prompts
/// "(%i1) ", output labels "(%o1)"), until end of input or quit().
fn maxima_interactive(quiet? : Bool = false) -> Unit raise {
  displa__interactive.val = true
  if quiet {
    set(q_ear_maxima_quiet, t) |> ignore
  }
  macsys__top_level(symval(standard_input), Nil, false)
}

///|
fn init_macsys() -> Unit raise {
  defvar_init(macsys__q_query_input, Nil)
  trmode__init()
  let (sec, min, hour, day, month, year) = macsys__now_decoded()
  macsys__build_time.val = format_to_string(
    "~4,'0d-~2,'0d-~2,'0d ~2,'0d:~2,'0d:~2,'0d",
    [int(year), int(month), int(day), int(hour), int(min), int(sec)],
  )
  // Declare a build_info structure, then remove it from the list of
  // user-defined structures.
  let _ = (fn() -> Value raise { defstruct1(
    lread(
      "((%build_info) $version $timestamp $host $lisp_name $lisp_version $maxima_userdir $maxima_tempdir $maxima_objdir $maxima_frontend $maxima_frontend_version)",
    ),
  ) })() catch { _ => Value::Nil }
  set(
    q_d_structures,
    cons(
      list1(q_mlist),
      remove_if(x => eq(caar(x), q_p_build_info), cdr(symval(q_d_structures))),
    ),
  )
  |> ignore
  setf_get(q_p_build_info, q_dimension, q_dimension_build_info) |> ignore
  initialize_real_and_run_time() |> ignore
  defun(q_d_absolute_real_time, args => {
    check_arity("$absolute_real_time", args, 0)
    d_absolute_real_time()
  })
  defun(q_d_elapsed_real_time, args => {
    check_arity("$elapsed_real_time", args, 0)
    d_elapsed_real_time()
  })
  defun(q_d_elapsed_run_time, args => {
    check_arity("$elapsed_run_time", args, 0)
    d_elapsed_run_time()
  })
}
