// Port of share/utils/mactex-utilities.lisp: additional mactex utilities
// (based on code by Richard J. Fateman, 1987, ported to Common Lisp by
// William Schelter). Loading it redefines TEX-MQUOTIENT (LaTeX style
// quotients) and TEX-MATRIX (amsmath style matrices).

///|
/// DEFUN of a mactex function: install it in the function cell and in
/// mactex's table of redefinitions.
fn share_mactex_utilities__redefine(
  name : Value,
  f : (Array[Value]) -> Value raise,
) -> Unit raise {
  defun(name, f, name=symbol_name(name))
  mactex__redefined.set(symbol_name(name), f)
}

///|
/// If you want LaTeX style quotients, first load mactex and second define
/// tex-mquotient as follows
fn share_mactex_utilities__tex_mquotient(
  x : Value,
  l : Value,
  r : Value,
) -> Value raise {
  if cddr(x) is Nil || cdddr(x).truthy() {
    wna_err(caar(x)) |> ignore
  }
  let l = tex(cadr(x), append(l, list1(Str("\\frac{"))), Nil, q_mparen, q_mparen)
  let r = tex(
    caddr(x),
    list1(Str("}{")),
    append(list1(Str("}")), r),
    q_mparen,
    q_mparen,
  )
  append(l, r)
}

///|
/// To use amsmath style matrices (to TeX the code, you'll need to
/// \usepackage{amsmath}). matrix looks like ((mmatrix)((mlist) a b) ...)
fn share_mactex_utilities__tex_matrix(
  x : Value,
  l : Value,
  r : Value,
) -> Value raise {
  append(
    l,
    append(
      list1(Str("\\begin{pmatrix}")),
      append(
        mapcan(y => tex_list(cdr(y), Nil, list1(Str(" \\\\ ")), Str(" & ")), cdr(
          x,
        )),
        append(list1(Str("\\end{pmatrix}")), r),
      ),
    ),
  )
}

///|
fn init_share_mactex_utilities() -> Unit raise {
  share_mactex_utilities__redefine(q_tex_mquotient, a => share_mactex_utilities__tex_mquotient(
    arg(a, 0),
    arg(a, 1),
    arg(a, 2),
  ))
  share_mactex_utilities__redefine(q_tex_matrix, a => share_mactex_utilities__tex_matrix(
    arg(a, 0),
    arg(a, 1),
    arg(a, 2),
  ))
}
