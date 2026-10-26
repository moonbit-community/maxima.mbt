// Port of share/contrib/operatingsystem/operatingsystem.lisp (functions
// from CLOCC, added to Maxima by Wolfgang Dautermann): directory and file
// operations used by operatingsystem.mac. The port uses the file functions
// of moonbitlang/x/fs; changing the working directory is not available.

///|
/// Change the working directory.
fn os_chdir(dir : Value) -> Value raise {
  merr("chdir: changing the working directory is not supported in this port; cannot change to ~M", [
    dir,
  ])
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
/// The port never changes its working directory, so this is the directory
/// it was started in.
fn os_getcurrentdirectory() -> Value raise {
  match getenv("PWD") {
    Some(d) if d != "" => Str(if d.has_suffix("/") { d } else { d + "/" })
    _ =>
      merr("getcurrentdirectory: the current directory is not available in this port", [])
  }
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
