// Port of share/contrib/operatingsystem/operatingsystem.lisp (functions
// from CLOCC, added to Maxima by Wolfgang Dautermann): directory and file
// operations used by operatingsystem.mac. The port uses the file functions
// of moonbitlang/x/fs and the runtime's process primitives.

///|
/// Change the working directory; returns the new working directory (SBCL's
/// new *DEFAULT-PATHNAME-DEFAULTS*), with a trailing slash.
fn os_chdir(dir : Value) -> Value raise {
  if !change_directory(lstring(dir)) {
    raise LispError::Condition(
      intern("sb-posix:syscall-error"),
      "Error in SB-POSIX:CHDIR: cannot change to " + lstring(dir),
      dir,
    )
  }
  Str(current_directory() + "/")
}

///|
/// Create a directory (T on success, NIL on failure, like SBCL's
/// unix-mkdir).
fn os_mkdir(dir : Value) -> Value raise {
  let path = lstring(dir)
  @fs.create_dir(path) catch {
    _ => return Nil
  }
  t
}

///|
/// Delete a directory.
fn os_rmdir(dir : Value) -> Value raise {
  let path = lstring(dir)
  @fs.remove_dir(path) catch {
    _ => merr("rmdir: cannot delete the directory ~M", [dir]) |> ignore
  }
  t
}

///|
/// Return the current directory (with a trailing slash, as a namestring).
fn os_getcurrentdirectory() -> Value raise {
  let d = current_directory()
  Str(if d.has_suffix("/") { d } else { d + "/" })
}

///|
/// Copy a file byte by byte.
fn os_copy_file(from_file : Value, to_file : Value) -> Value raise {
  let from = lstring(from_file)
  let to = lstring(to_file)
  let bytes = read_file_bytes(from)
  @fs.write_bytes_to_file(to, bytes) catch {
    _ =>
      raise LispError::Condition(
        intern("file-error"),
        "cannot write file \{to}",
        Str(to),
      )
  }
  Nil
}

///|
fn init_share_operatingsystem() -> Unit raise {

}
