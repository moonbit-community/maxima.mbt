// Port of src/command-line.lisp: the CL-OPTION structure describing a
// command-line option, the --help listing, and PROCESS-ARGS, which parses
// the arguments with GETOPT and runs the actions of the options found.

///|
/// (defstruct cl-option names argument action help-string)
fn cmdline__make_cl_option(
  names~ : Value,
  argument? : Value = Nil,
  action? : Value = Nil,
  help_string? : Value = Nil,
) -> Value {
  make_struct("cl-option", [names, argument, action, help_string])
}

///|
fn cmdline__cl_option_names(o : Value) -> Value raise {
  struct_ref(o, 0)
}

///|
fn cmdline__cl_option_argument(o : Value) -> Value raise {
  struct_ref(o, 1)
}

///|
fn cmdline__cl_option_action(o : Value) -> Value raise {
  struct_ref(o, 2)
}

///|
fn cmdline__cl_option_help_string(o : Value) -> Value raise {
  struct_ref(o, 3)
}

///|
fn cmdline_cl_option_description(name : Value, arg : Value) -> Value raise {
  if arg.truthy() {
    let n = lstring(name)
    if string_length(n) == 1 {
      format(Nil, "~a ~a", [name, arg])
    } else if substring(n, 0, end=2) == "--" {
      format(Nil, "~a=~a", [name, arg])
    } else {
      format(Nil, "~a ~a", [name, arg])
    }
  } else {
    name
  }
}

///|
/// The column the next character written to *standard-output* lands in.
fn cmdline__column() -> Int {
  stream_column(stream=symval(standard_output))
}

///|
/// (format t "~{~<PREFIX~SPARE,WIDTH:;SEGMENT~>~^SEPARATOR~}" items): print
/// each item's segment, preceded by PREFIX (a newline and indentation) when
/// the segment plus SPARE columns would not fit before column WIDTH.
fn cmdline__wrap_items(
  items : Array[String],
  segment_prefix : String,
  separator : String,
  newline_indent : String,
  spare~ : Int = 1,
  width~ : Int = 80,
) -> Unit {
  let out = symval(standard_output)
  for i, item in items {
    let seg = segment_prefix + item
    if cmdline__column() + string_length(seg) + spare > width {
      write_string("\n" + newline_indent, stream=out)
    }
    write_string(seg, stream=out)
    if i + 1 < items.length() {
      write_string(separator, stream=out)
    }
  }
}

///|
/// Print the help string neatly by breaking long lines as needed. This
/// assumes that the HELP-STRING doesn't have any kind of manually inserted
/// formatting.
fn cmdline_print_help_string(help_string : Value) -> Value raise {
  if symval(q_ear_wrap_help_string).truthy() {
    // Break the help string into a list of words and print the list of
    // words individually with a single space after, and inserting a
    // newline as needed.  Each line is prefixed by 8 spaces and we wrap
    // the line at 80 columns:
    // (format t "        ~{~<~%        ~1,80:; ~A~>~^~}" words)
    let words = rx_pregexp_split(Str("\\s+"), help_string)
    write_string("        ", stream=symval(standard_output))
    cmdline__wrap_items(
      list_to_array(words).map(w => princ_to_string(w)),
      " ",
      "",
      "        ",
    )
  } else {
    format(t, "        ~a", [help_string]) |> ignore
  }
  Nil
}

///|
/// Prints all the command line options for Maxima in a neat form.  If
/// :TEXI-TABLE-FORM is non-NIL, the output is suitable for adding a table
/// to commandline-options.texi.
fn cmdline_list_cl_options(
  cl_option_list : Value,
  texi_table_form? : Value = Nil,
) -> Value raise {
  if texi_table_form.truthy() {
    format(t, "@need 100~%@table @code~%", []) |> ignore
  } else {
    format(t, "options:~%", []) |> ignore
  }
  for opt in cl_option_list.iter() {
    let help_string = cmdline__cl_option_help_string(opt)
    let names = cmdline__cl_option_names(opt)
    let arg = cmdline__cl_option_argument(opt)
    if texi_table_form.truthy() {
      format(t, "@need 150~%@item ", []) |> ignore
    }
    let options = mapcar(name => cmdline_cl_option_description(name, arg), names)
    // Wrap any long list of options, except we don't when producing output
    // for the texi file.
    if texi_table_form.truthy() {
      format(t, "~{~A~^, ~}~%", [options]) |> ignore
    } else {
      // The output is 4 spaces, then each of the options separated by a
      // ", ".  The output is wrapped at column 80:
      // (format t "    ~{~<~%      ~1,80:;~A~>~^, ~}~%" options)
      write_string("    ", stream=symval(standard_output))
      cmdline__wrap_items(
        list_to_array(options).map(o => princ_to_string(o)),
        "",
        ", ",
        "      ",
      )
      terpri(stream=symval(standard_output))
    }
    if help_string.truthy() {
      cmdline_print_help_string(help_string) |> ignore
    }
    if texi_table_form.truthy() {
      format(t, "~2%", []) |> ignore
    }
    terpri(stream=symval(standard_output))
  }
  if texi_table_form.truthy() {
    format(t, "@end table~%", []) |> ignore
  }
  finish_output(stream=symval(standard_output))
  Nil
}

///|
fn cmdline_process_args(args : Value, cl_option_list : Value) -> Value raise {
  // Massage cl-option into the format wanted by getopt.  Basically, remove
  // any leading dashes, and if the cl-option includes an argument, treat
  // it as a required argument.
  let fixup = (options : Value) => {
    let opts = Collector::new()
    for o in options.iter() {
      for name in cmdline__cl_option_names(o).iter() {
        opts.add(
          list3(
            Str(string_left_trim("-", lstring(name))),
            if cmdline__cl_option_argument(o).truthy() {
              kw("required")
            } else {
              kw("none")
            },
            Nil,
          ),
        )
      }
    }
    opts.result()
  }
  let options = fixup(cl_option_list)
  let (_non_opts, opts, errors) = getopt_getopt(
    args,
    options,
    allow_exact_match=t,
  )
  // non-opts ignored for now.  Look over all of opts and run the action.
  for o in opts.iter() {
    // Try to find the corresponding cl-option: strip off any leading
    // dashes from the option name and compare with the desired option.
    let desired = car(o)
    let mut cl_opt : Value = Nil
    for e in cl_option_list.iter() {
      let mut found = false
      for n in cmdline__cl_option_names(e).iter() {
        if equal(desired, Str(string_left_trim("-", lstring(n)))) {
          found = true
          break
        }
      }
      if found {
        cl_opt = e
        break
      }
    }
    if cl_opt.truthy() {
      let action = cmdline__cl_option_action(cl_opt)
      if action.truthy() && cmdline__cl_option_argument(cl_opt).truthy() {
        funcall(action, [cdr(o)]) |> ignore
      } else if action.truthy() {
        funcall(action, []) |> ignore
      }
    } else {
      write_stderr(
        format_to_string(
          "WARNING: Could not find option ~S in cl-options: ~S.~%Please report this bug.~%",
          [o, cl_option_list],
        ),
      )
    }
  }
  format(t, "~{Warning: argument ~A not recognized.~%~}", [errors]) |> ignore
  // What do we do about non-option arguments?  We just ignore them for
  // now.
  Nil
}

///|
/// The command-line arguments of the program (without the program name).
let cmdline__argv : Ref[Array[String]] = Ref([])

///|
fn cmdline_get_application_args() -> Value raise {
  // -- is used to distinguish between options for a lisp implementation
  // and for Maxima.
  let arglist = list(cmdline__argv.val.map(a => Str(a)))
  let dashes = member_equal(Str("--"), arglist)
  if dashes.truthy() {
    cdr(dashes)
  } else {
    arglist
  }
}

///|
fn init_command_line() -> Unit raise {
  ()
}
