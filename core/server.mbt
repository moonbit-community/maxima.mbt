// Port of src/server.lisp: connect Maxima to a socket which has been
// opened by some third party, typically a GUI program which supplies input
// to Maxima.  Note that this code DOES NOT create a Maxima server: Maxima
// is the client!
//
// A socket stream is a bidirectional Lisp stream in CL.  The port's
// streams go one way, so OPEN-SOCKET returns a "socket-stream" structure
// holding the file descriptor and an output stream writing to it; the
// input side is the console input stream, whose reader SETUP-CLIENT
// switches to the socket (so the REPL's standard input is the socket, as
// in the reference).

///|
let server__q_trace_output : Value = sym("*trace-output*")

///|
fn server__socket_fd(sock : Value) -> Int raise {
  to_int(struct_ref(sock, 0))
}

///|
fn server__socket_output(sock : Value) -> Value raise {
  struct_ref(sock, 1)
}

///|
/// An output stream writing to the file descriptor FD.
fn server__fd_output_stream(fd : Int, name : String) -> Value {
  let st : LStream = {
    input: "",
    pos: 0,
    unread: [],
    out: None,
    name,
    sink: Some(s => fd_write_string(fd, s) |> ignore),
    column: 0,
    line: 1,
    is_input: false,
    eof: false,
  }
  Stream(st)
}

///|
/// Reads the next chunk of input from the file descriptor FD, for the
/// console input stream; None at end of file.
fn server__fd_reader(fd : Int) -> () -> String? {
  () => {
    flush_stdout()
    let s = fd_read_string(fd)
    if s == "" {
      None
    } else {
      Some(s)
    }
  }
}

///|
fn setup_client(port : Value, host? : Value = Str("localhost")) -> Value raise {
  let (sock, condition) = (fn() -> (Value, Value) raise {
    (open_socket(host, port), Nil)
  })() catch {
    e => (Nil, Str(suprv1__error_text(e)))
  }
  if sock is Nil {
    // It appears that we were unable to open a socket or connect to the
    // specified port.
    mtell(list([Str("~%Unable to connect Maxima to port ~:M.~%"), port]))
    |> ignore
    mtell(list([Str("Error: ~A~%"), condition])) |> ignore
    d_quit() |> ignore
  }
  set(q_ear_socket_connection, sock) |> ignore
  set(q_d_old_stderr, symval(error_output)) |> ignore
  set(q_d_old_stdout, symval(standard_output)) |> ignore
  let out = server__socket_output(sock)
  console_reader.val = server__fd_reader(server__socket_fd(sock))
  set(standard_input, console_in) |> ignore
  set(standard_output, out) |> ignore
  set(error_output, out) |> ignore
  set(terminal_io, out) |> ignore
  set(server__q_trace_output, out) |> ignore
  format(t, "pid=~a~%", [getpid()]) |> ignore
  finish_output(stream=out)
  set(q_ear_debug_io, out) |> ignore
  // *query-io* is the socket as well (the REPL answers questions from it).
  set(q_ear_query_io, out) |> ignore
  Nil
}

///|
fn close_client() -> Value raise {
  Nil
}

///|
/// Open a socket connection to `host' at `port'.  (From CLOCC.)
fn open_socket(host : Value, port : Value, bin? : Value = Nil) -> Value raise {
  ignore(bin)
  let host = match host {
    Str(h) => h
    _ =>
      if integerp(host) {
        // Can't actually handle this case for lack of HOSTENT-NAME and
        // RESOLVE-HOST-IPADDR.
        return merr(
          "OPEN-SOCKET: can't handle integer host argument (host=~M)~%",
          [host],
        )
      } else {
        raise LispError::SimpleError(
          prin1_to_string(host) +
          " fell through ETYPECASE expression. Wanted one of (STRING INTEGER).",
        )
      }
  }
  let fd = tcp_connect(host, to_int(port))
  if fd < 0 {
    raise LispError::SimpleError(
      format_to_string("Socket error in \"connect\": could not connect to ~A:~A", [
        Str(host),
        port,
      ]),
    )
  }
  make_struct("socket-stream", [
    Fix(fd.to_int64()),
    server__fd_output_stream(fd, "socket"),
  ])
}

///|
fn start_client(port : Value, host? : Value = Str("localhost")) -> Value raise {
  format(t, "Connecting Maxima to server on port ~a~%", [port]) |> ignore
  set(q_d_in_netmath, t) |> ignore
  set(q_d_show_openplot, Nil) |> ignore
  setup_client(port, host~)
}

///|
fn getpid_from_environment() -> Value raise {
  let s = maxima_getenv(Str("PID"))
  match s {
    Str(str) =>
      match parse_integer(str) {
        Some(v) => v
        None => Fix(-1L)
      }
    _ => Fix(-1L)
  }
}

///|
fn getpid() -> Value raise {
  Fix(process_id().to_int64())
}

///|
fn xchdir(w : Value) -> Value raise {
  // (sb-posix:chdir w) returns 0, or signals an error.
  if change_directory(lstring(w)) {
    Fix(0L)
  } else {
    raise LispError::SimpleError(
      format_to_string("Error in chdir(~S)", [w]),
    )
  }
}

///|
fn init_server() -> Unit raise {
  ()
}
