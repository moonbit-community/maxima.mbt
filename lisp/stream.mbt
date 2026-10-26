///|
#borrow(b)
extern "c" fn c_write_stdout(b : Bytes, len : Int) = "maxima_write_stdout"

///|
extern "c" fn c_flush_stdout() = "maxima_flush_stdout"

///|
#borrow(eof)
extern "c" fn c_read_line(eof : Ref[Int]) -> Bytes = "maxima_read_line"

///|
extern "c" fn c_cpu_time() -> Double = "maxima_cpu_time"

///|
extern "c" fn c_exit(code : Int) = "maxima_exit"

///|
/// Write a string to the process's stdout (unbuffered at this layer).
pub fn write_stdout(s : String) -> Unit {
  let b = @utf8.encode(s)
  c_write_stdout(b, b.length())
}

///|
pub fn flush_stdout() -> Unit {
  c_flush_stdout()
}

///|
/// Read a line from stdin, including its newline; None at EOF.
pub fn read_stdin_line() -> String? {
  let eof = Ref(0)
  let b = c_read_line(eof)
  if eof.val == 1 {
    None
  } else {
    Some(@utf8.decode_lossy(b))
  }
}

///|
/// CPU seconds used by this process.
pub fn cpu_time() -> Double {
  c_cpu_time()
}

///|
/// Wall-clock milliseconds since the epoch.
pub fn wall_time_ms() -> UInt64 {
  @env.now()
}

///|
/// Exit the process.
pub fn exit_process(code : Int) -> Unit {
  c_exit(code)
}

///|
/// Read a whole file as a string.
pub fn read_file(path : String) -> String raise LispError {
  @fs.read_file_to_string(path) catch {
    _ =>
      raise Condition(intern("file-error"), "cannot open file \{path}", Str(path))
  }
}

///|
/// Read a whole file as octets (`:element-type '(unsigned-byte 8)`).
pub fn read_file_bytes(path : String) -> Bytes raise LispError {
  @fs.read_file_to_bytes(path) catch {
    _ =>
      raise Condition(intern("file-error"), "cannot open file \{path}", Str(path))
  }
}

///|
/// Write a whole file.
pub fn write_file(path : String, contents : String) -> Unit raise LispError {
  @fs.write_string_to_file(path, contents) catch {
    _ =>
      raise Condition(intern("file-error"), "cannot write file \{path}", Str(path))
  }
}

///|
/// Does a file exist?
pub fn probe_file(path : String) -> Bool {
  @fs.path_exists(path) && (@fs.is_file(path) catch { _ => false })
}

///|
pub fn directory_p(path : String) -> Bool {
  @fs.path_exists(path) && (@fs.is_dir(path) catch { _ => false })
}

///|
/// Entries of a directory.
pub fn list_directory(path : String) -> Array[String] {
  (@fs.read_dir(path) catch { _ => [][:] }).to_array()
}

///|
pub fn getenv(name : String) -> String? {
  @env.get_env_var(name)
}

// ---------------------------------------------------------------------------
// Lisp streams

///|
fn new_stream(
  input? : String = "",
  out? : StringBuilder,
  name? : String = "",
  sink? : (String) -> Unit,
  is_input? : Bool = false,
) -> LStream {
  {
    input,
    pos: 0,
    unread: [],
    out,
    name,
    sink,
    column: 0,
    line: 1,
    is_input,
    eof: false,
  }
}

///|
/// The console output stream.
pub let console_out : Value = Stream(
  new_stream(sink=write_stdout, name="*terminal-io*"),
)

///|
/// Hook for reading more console input (one line at a time).
pub let console_reader : Ref[() -> String?] = Ref(read_stdin_line)

///|
/// The console input stream; refills from `console_reader`.
pub let console_in : Value = Stream(new_stream(is_input=true, name="*terminal-io*"))

///|
/// `*standard-output*`
pub let standard_output : Value = {
  let s = intern("*standard-output*")
  s.value = console_out
  s.bound = true
  Sym(s)
}

///|
/// `*standard-input*`
pub let standard_input : Value = {
  let s = intern("*standard-input*")
  s.value = console_in
  s.bound = true
  Sym(s)
}

///|
/// `*terminal-io*`
pub let terminal_io : Value = {
  let s = intern("*terminal-io*")
  s.value = console_out
  s.bound = true
  Sym(s)
}

///|
/// `*debug-io*` / `*error-output*`
pub let error_output : Value = {
  let s = intern("*error-output*")
  s.value = console_out
  s.bound = true
  let d = intern("*debug-io*")
  d.value = console_out
  d.bound = true
  let q = intern("*query-io*")
  q.value = console_out
  q.bound = true
  Sym(s)
}

///|
/// `(make-string-output-stream)`
pub fn make_string_output_stream() -> Value {
  Stream(new_stream(out=StringBuilder::new()))
}

///|
/// `(make-string-input-stream s)`
pub fn make_string_input_stream(s : String) -> Value {
  Stream(new_stream(input=s, is_input=true))
}

///|
/// Input stream over a file's contents.
pub fn open_input_file(path : String) -> Value raise LispError {
  let s = read_file(path)
  Stream(new_stream(input=s, name=path, is_input=true))
}

///|
/// `(get-output-stream-string s)`
pub fn get_output_stream_string(s : Value) -> String {
  match s {
    Stream({ out: Some(sb), .. }) => {
      let r = sb.to_string()
      sb.reset()
      r
    }
    _ => ""
  }
}

///|
/// Resolve a stream designator: nil -> *standard-output*, t -> terminal.
pub fn out_stream(s : Value) -> LStream {
  match s {
    Stream(st) => st
    Nil =>
      match symval(standard_output) {
        Stream(st) => st
        _ => match console_out {
          Stream(st) => st
          _ => abort("no console")
        }
      }
    _ =>
      match symval(terminal_io) {
        Stream(st) => st
        _ => match console_out {
          Stream(st) => st
          _ => abort("no console")
        }
      }
  }
}

///|
/// The current `*standard-output*` stream.
pub fn stdout_stream() -> Value {
  symval(standard_output)
}

///|
/// Write a string to a stream.
pub fn LStream::write_str(self : LStream, s : String) -> Unit {
  match self.out {
    Some(sb) => sb.write_string(s)
    None =>
      match self.sink {
        Some(f) => f(s)
        None => ()
      }
  }
  // track column
  for c in s {
    if c == '\n' {
      self.column = 0
      self.line += 1
    } else {
      self.column += 1
    }
  }
}

///|
/// `(write-string s stream)`
pub fn write_string(s : String, stream? : Value = Nil) -> Unit {
  out_stream(stream).write_str(s)
}

///|
/// `(write-char c stream)`
pub fn write_char(c : Char, stream? : Value = Nil) -> Unit {
  out_stream(stream).write_str(c.to_string())
}

///|
/// `(terpri stream)`
pub fn terpri(stream? : Value = Nil) -> Unit {
  out_stream(stream).write_str("\n")
}

///|
/// `(fresh-line stream)`
pub fn fresh_line(stream? : Value = Nil) -> Bool {
  let st = out_stream(stream)
  if st.column != 0 {
    st.write_str("\n")
    true
  } else {
    false
  }
}

///|
/// `(finish-output)` / `(force-output)`
pub fn finish_output(stream? : Value = Nil) -> Unit {
  let st = out_stream(stream)
  if st.sink is Some(_) {
    flush_stdout()
  }
}

///|
/// Current output column of a stream.
pub fn stream_column(stream? : Value = Nil) -> Int {
  out_stream(stream).column
}

///|
/// `(with-output-to-string (s) body)`: body receives the stream.
pub fn with_output_to_string(f : (Value) -> Unit raise) -> String raise {
  let s = make_string_output_stream()
  f(s)
  get_output_stream_string(s)
}

///|
/// Capture everything written to `*standard-output*` while running f.
pub fn capture_stdout(f : () -> Unit raise) -> String raise {
  let s = make_string_output_stream()
  with_special(standard_output, s, f)
  get_output_stream_string(s)
}

// ---------------------------------------------------------------------------
// Input

///|
fn in_stream(s : Value) -> LStream {
  match s {
    Stream(st) => st
    _ =>
      match symval(standard_input) {
        Stream(st) => st
        _ => match console_in {
          Stream(st) => st
          _ => abort("no console")
        }
      }
  }
}

///|
fn LStream::refill(self : LStream) -> Bool {
  if self.name == "*terminal-io*" && !self.eof {
    match (console_reader.val)() {
      Some(line) => {
        self.input = self.input.substring(start=self.pos) + line
        self.pos = 0
        true
      }
      None => {
        self.eof = true
        false
      }
    }
  } else {
    false
  }
}

///|
/// Read one character; None at EOF.
pub fn LStream::read_char(self : LStream) -> Char? {
  if self.unread.length() > 0 {
    return self.unread.pop()
  }
  while self.pos >= self.input.length() {
    if !self.refill() {
      return None
    }
  }
  let c0 = self.input[self.pos]
  let c = if c0.is_leading_surrogate() && self.pos + 1 < self.input.length() {
    let c1 = self.input[self.pos + 1]
    self.pos += 2
    let hi = c0.to_int() - 0xD800
    let lo = c1.to_int() - 0xDC00
    (0x10000 + (hi << 10) + lo).unsafe_to_char()
  } else {
    self.pos += 1
    c0.to_int().unsafe_to_char()
  }
  if c == '\n' {
    self.line += 1
  }
  Some(c)
}

///|
/// Peek one character without consuming it.
pub fn LStream::peek_char(self : LStream) -> Char? {
  match self.read_char() {
    Some(c) => {
      self.unread.push(c)
      Some(c)
    }
    None => None
  }
}

///|
pub fn LStream::unread_char(self : LStream, c : Char) -> Unit {
  self.unread.push(c)
}

///|
/// `(read-char stream nil eof)`: returns Char or the eof value.
pub fn read_char(stream? : Value = Nil, eof_value? : Value = Nil) -> Value {
  match in_stream(stream).read_char() {
    Some(c) => Char(c)
    None => eof_value
  }
}

///|
/// `(peek-char nil stream nil eof)`
pub fn peek_char(stream? : Value = Nil, eof_value? : Value = Nil) -> Value {
  match in_stream(stream).peek_char() {
    Some(c) => Char(c)
    None => eof_value
  }
}

///|
/// `(unread-char c stream)`
pub fn unread_char(c : Char, stream? : Value = Nil) -> Unit {
  in_stream(stream).unread_char(c)
}

///|
/// `(read-line stream nil eof)`
pub fn read_line(stream? : Value = Nil) -> String? {
  let st = in_stream(stream)
  let sb = StringBuilder::new()
  let mut any = false
  while true {
    match st.read_char() {
      Some('\n') => return Some(sb.to_string())
      Some(c) => {
        any = true
        sb.write_char(c)
      }
      None => break
    }
  }
  if any {
    Some(sb.to_string())
  } else {
    None
  }
}

///|
/// `(streamp x)`
pub fn streamp(x : Value) -> Bool {
  x is Stream(_)
}
