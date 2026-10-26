// Port of share/contrib/maximaMathML/mathmldisplay.lisp: makes Maxima
// display MathML (Paul S. Wang, 1999). Loading it redefines DISPLA.

///|
/// (print 'sym): CL prints the symbol's name in upper case.
fn share_mathmldisplay__print(name : String) -> Unit raise {
  terpri() |> ignore
  write_string(name + " ")
}

///|
/// The redefined DISPLA.
fn share_mathmldisplay__displa(exp_ : Value) -> Value raise {
  let exp_ = caddr(exp_) // get rid of output label
  share_mathmldisplay__print("PRESENTATION-EXP")
  d_prmathml(list1(exp_)) |> ignore
  share_mathmldisplay__print("CONTENT-EXP")
  d_ctmathml(list1(exp_)) |> ignore
  share_mathmldisplay__print("END-EXP")
  terpri()
  Nil
}

///|
fn init_share_mathmldisplay() -> Unit raise {
  displa__redefined.val = Some(share_mathmldisplay__displa)
}

///|
/// share/contrib/maximaMathML/maximaMathML.lisp: loads the MathML display,
/// input, presentation and content packages.
fn init_share_maxima_cm_ath_cm__cl_() -> Unit raise {
  // no saving of expressions under automatically generated labels
  set(q_d_nolabels, t) |> ignore
  // redefines maxima displa
  d_load(Str("mathmldisplay")) |> ignore
  // mathml input to maxima
  d_load(Str("mathml-maxima")) |> ignore
  // generate MathML Presentation encoding
  d_load(Str("PrMathML")) |> ignore
  // generate MathML Content encoding
  d_load(Str("CtMathML")) |> ignore
}
