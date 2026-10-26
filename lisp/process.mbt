// Process, directory and socket primitives (native only).

///|
#borrow(cmd)
extern "c" fn c_system(cmd : Bytes) -> Int = "maxima_system"

///|
#borrow(cmd, status)
extern "c" fn c_shell_output(cmd : Bytes, status : Ref[Int]) -> Bytes = "maxima_shell_output"

///|
#borrow(path)
extern "c" fn c_chdir(path : Bytes) -> Int = "maxima_chdir"

///|
extern "c" fn c_getcwd() -> Bytes = "maxima_getcwd"

///|
extern "c" fn c_getpid() -> Int = "maxima_getpid"

///|
#borrow(host)
extern "c" fn c_tcp_connect(host : Bytes, port : Int) -> Int = "maxima_tcp_connect"

///|
#borrow(b)
extern "c" fn c_fd_write(fd : Int, b : Bytes, len : Int) -> Int = "maxima_fd_write"

///|
extern "c" fn c_fd_read(fd : Int, max : Int) -> Bytes = "maxima_fd_read"

///|
extern "c" fn c_fd_close(fd : Int) -> Int = "maxima_fd_close"

///|
fn cstr(s : String) -> Bytes {
  // NUL-terminated UTF-8 (the runtime also terminates Bytes, but be explicit)
  let b = @utf8.encode(s)
  let a = b.to_array()
  a.push(b'\x00')
  Bytes::from_array(a)
}

///|
/// Run a shell command (`/bin/sh -c`); returns the exit status, or -1.
pub fn run_shell_command(cmd : String) -> Int {
  flush_stdout()
  c_system(cstr(cmd))
}

///|
/// Run a shell command and capture its standard output.
pub fn shell_command_output(cmd : String) -> (Int, String) {
  flush_stdout()
  let st = Ref(0)
  let out = c_shell_output(cstr(cmd), st)
  (st.val, @utf8.decode_lossy(out))
}

///|
/// Change the process's working directory; true on success.
pub fn change_directory(path : String) -> Bool {
  c_chdir(cstr(path)) == 0
}

///|
/// The process's working directory.
pub fn current_directory() -> String {
  @utf8.decode_lossy(c_getcwd())
}

///|
pub fn process_id() -> Int {
  c_getpid()
}

///|
/// Open a TCP connection; returns a file descriptor or -1.
pub fn tcp_connect(host : String, port : Int) -> Int {
  c_tcp_connect(cstr(host), port)
}

///|
/// Write a string to a file descriptor; returns bytes written or -1.
pub fn fd_write_string(fd : Int, s : String) -> Int {
  let b = @utf8.encode(s)
  c_fd_write(fd, b, b.length())
}

///|
/// Read up to `max` bytes as text; empty string at EOF.
pub fn fd_read_string(fd : Int, max? : Int = 4096) -> String {
  @utf8.decode_lossy(c_fd_read(fd, max))
}

///|
pub fn fd_close(fd : Int) -> Unit {
  c_fd_close(fd) |> ignore
}

///|
#borrow(cmd)
extern "c" fn c_pipe_open(cmd : Bytes) -> Int = "maxima_pipe_open"

///|
#borrow(b)
extern "c" fn c_pipe_write(h : Int, b : Bytes, len : Int) -> Int = "maxima_pipe_write"

///|
extern "c" fn c_pipe_close(h : Int) -> Int = "maxima_pipe_close"

///|
/// Start a shell command (`/bin/sh -c`) with a pipe to its standard input;
/// returns a pipe handle, or -1.
pub fn open_output_pipe(cmd : String) -> Int {
  flush_stdout()
  c_pipe_open(cstr(cmd))
}

///|
/// Write a string to the pipe and flush it; false if that failed (e.g. the
/// process has exited).
pub fn pipe_write_string(h : Int, s : String) -> Bool {
  let b = @utf8.encode(s)
  c_pipe_write(h, b, b.length()) == b.length()
}

///|
/// Close the pipe and wait for the process; returns its exit status, or -1.
pub fn close_output_pipe(h : Int) -> Int {
  c_pipe_close(h)
}

///|
/// The path the program was started with (argv[0]); "" if unknown.
pub fn program_path() -> String {
  let args = @env.args()
  if args.length() > 0 {
    args[0]
  } else {
    ""
  }
}

///|
extern "c" fn c_run_with_stack(
  call : FuncRef[(() -> Unit) -> Unit],
  closure : () -> Unit,
  stack_size : Int64,
) -> Int = "maxima_run_with_stack"

///|
/// Run `f` on a thread with a `stack_size`-byte stack and wait for it
/// (directly on this thread if no thread can be created).
pub fn run_with_stack(stack_size : Int64, f : () -> Unit) -> Unit {
  c_run_with_stack(g => g(), f, stack_size) |> ignore
}
