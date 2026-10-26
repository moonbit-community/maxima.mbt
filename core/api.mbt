// Public entry points of the core package.

///|
let api__initialized : Ref[Bool] = Ref(false)

///|
/// Load and initialize every part of Maxima, but not the run-time globals
/// (INITIALIZE-RUNTIME-GLOBALS: paths, help index, ...).
fn api__initialize_system() -> Unit raise {
  init_cl_specials()
  init_generated()
  globals__record_other_defmvars()
  register_cl_functions()
  init_translate_compat()
}

///|
/// Initialize Maxima (idempotent).
pub fn initialize() -> Unit raise {
  if !api__initialized.val {
    api__initialized.val = true
    api__initialize_system()
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
/// Command-line driver: CL-USER::RUN.  ARGS are the program arguments,
/// starting with the program name; the options are those of
/// PROCESS-MAXIMA-ARGS (see `maxima --help`), parsed by GETOPT:
///   --batch-string=<s>  evaluate Maxima code and exit
///   -b <file> / --batch=<file>  batch a file and exit
///   -q / --quiet, --very-quiet, --no-init, -r, -s <port>, --version, ...
/// With no batch options, runs the interactive loop.
pub fn cli_main(args : Array[String]) -> Int {
  (fn() -> Int raise {
    if !api__initialized.val {
      api__initialized.val = true
      api__initialize_system()
    }
    init_cl__set_application_args(
      if args.length() > 0 {
        args[1:].to_array()
      } else {
        []
      },
    )
    run() |> ignore
    0
  })() catch {
    e => {
      write_stdout("fatal: \{e}\n")
      1
    }
  }
}
