// Public entry points of the core package.

///|
let api__initialized : Ref[Bool] = Ref(false)

///|
/// Initialize Maxima (idempotent).
pub fn initialize() -> Unit raise {
  if !api__initialized.val {
    api__initialized.val = true
    init_cl_specials()
    init_generated()
    init_macdes()
    register_cl_functions()
    init_cl__setup_paths()
  }
}

///|
/// Exit the process with a status code.
pub fn exit(code : Int) -> Unit {
  flush_stdout()
  exit_process(code)
}

///|
/// Command-line driver. Supported options (a subset of maxima's):
///   --batch-string=<s>  evaluate Maxima code and exit
///   -b <file> / --batch=<file>  batch a file and exit
///   -q / --quiet, --very-quiet, --no-init (accepted)
/// With no batch options, runs the interactive loop.
pub fn cli_main(args : Array[String]) -> Int {
  (fn() -> Int raise {
    let mut quiet = false
    let mut very_quiet = false
    let actions : Array[(String, String)] = []
    let mut i = 1
    while i < args.length() {
      let a = args[i]
      if a == "-q" || a == "--quiet" {
        quiet = true
      } else if a == "--very-quiet" {
        quiet = true
        very_quiet = true
      } else if a == "--no-init" {
        ()
      } else if a.has_prefix("--batch-string=") {
        actions.push(("string", a.substring(start=15)))
      } else if a == "--batch-string" && i + 1 < args.length() {
        i += 1
        actions.push(("string", args[i]))
      } else if a.has_prefix("--batch=") {
        actions.push(("file", a.substring(start=8)))
      } else if (a == "-b" || a == "--batch") && i + 1 < args.length() {
        i += 1
        actions.push(("file", args[i]))
      } else {
        write_stdout("maxima: unrecognized option \{a}\n")
        return 1
      }
      i += 1
    }
    initialize()
    if very_quiet {
      // as init-cl.lisp does for --very-quiet
      set(q_ear_display_labels_p, Nil) |> ignore
    }
    if actions.is_empty() {
      maxima_interactive(quiet~)
    } else {
      for act in actions {
        match act.0 {
          "string" => maxima_batch_string(act.1, quiet~)
          _ => maxima_batch_file(act.1, quiet~)
        }
      }
    }
    0
  })() catch {
    e => {
      write_stdout("fatal: \{e}\n")
      1
    }
  }
}
