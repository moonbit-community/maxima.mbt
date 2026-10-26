// Public entry points of the core package.

///|
let api__initialized : Ref[Bool] = Ref(false)

///|
/// Initialize Maxima (idempotent).
pub fn initialize() -> Unit raise {
  if !api__initialized.val {
    api__initialized.val = true
    init_generated()
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
    initialize()
    0
  })() catch {
    e => {
      write_stdout("fatal: \{e}\n")
      1
    }
  }
}
