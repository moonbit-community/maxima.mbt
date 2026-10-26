// Port of share/contrib/maxima-server.lisp: create simultaneous,
// independent Maxima sessions via POSIX fork.  SERVER-RUN implements a
// simple Unix server: listen, accept, fork (twice, so the grandchild
// cannot become a zombie), and run Maxima on the accepted connection.
//
// The port's runtime has TCP client connections only: it cannot bind,
// listen, accept or fork.  Loading the file (which creates the listening
// socket on 127.0.0.1:1042) and SERVER-RUN therefore signal a Maxima error
// naming the missing facility.

///|
fn share_maxima_server__unsupported(what : String) -> Value raise {
  merr(
    "maxima-server: ~A is not available in this port (its runtime cannot listen on, accept or fork for sockets).",
    [Str(what)],
  )
}

///|
fn server_run() -> Value raise {
  // (loop (socket-accept listening-socket) ... (sb-posix:fork) ...)
  share_maxima_server__unsupported("SERVER-RUN")
}

///|
fn init_share_maxima_server() -> Unit raise {
  // (defvar listening-socket (make-instance 'sb-bsd-sockets:inet-socket ...))
  // (sb-bsd-sockets:socket-bind listening-socket ... 1042)
  // (sb-bsd-sockets:socket-listen listening-socket 5)
  share_maxima_server__unsupported("a listening socket") |> ignore
}
