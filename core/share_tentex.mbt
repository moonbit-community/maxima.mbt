// Port of share/tensor/tentex.lisp: TeX formatting module for itensor.

///|
/// Turn off simplification to avoid meval mangling indices
fn d_tentex(x : Value) -> Value raise {
  with_special(q_d_simp, symval(q_d_simp), () => {
    set(q_d_simp, Nil) |> ignore
    meval(list2(q_d_tex, tenreform(x)))
  })
}

///|
fn tenreform(x : Value) -> Value raise {
  if atom(x) {
    x
  } else if atom(car(x)) {
    cons(car(x), tenreform(cdr(x)))
  } else if rpobj(x).truthy() {
    let y = append(
      if covi(x).truthy() {
        list1(cons(q_quote, list1(cons(list2(q_mtimes, q_simp), covi(x)))))
      } else {
        Nil
      },
      if deri(x).truthy() {
        list1(
          cons(
            q_quote,
            list1(
              cons(
                list2(q_mtimes, q_simp),
                append(
                  if covi(x) is Nil && deri(x).truthy() {
                    list1(Str(","))
                  } else {
                    Nil
                  },
                  deri(x),
                ),
              ),
            ),
          ),
        )
      } else {
        Nil
      },
    )
    let u = if y.truthy() {
      cons(cons(name(x), list2(q_simp, q_array)), y)
    } else {
      name(x)
    }
    let v = if conti(x).truthy() {
      cons(q_quote, list1(cons(list2(q_mtimes, q_simp), conti(x))))
    } else {
      Nil
    }
    if v.truthy() {
      list3(list2(q_mexpt, q_simp), u, v)
    } else {
      u
    }
  } else {
    cons(tenreform(car(x)), tenreform(cdr(x)))
  }
}

///|
/// Top-level forms of tentex.lisp: the TEXWORD properties.
fn init_share_tentex() -> Unit raise {
  let words : Array[(Value, String)] = [
    (q_d_dl, "\\Delta"),
    (q_d_divg, "(\\nabla\\cdot G)"),
    (q_d_og, "(\\Omega\\cdot G)"),
    (q_d_dl_1, "\\Delta^{\\star}"),
    (q_d_dl_c, "\\Delta_{\\chi}"),
    (q_d_omega, "\\Omega"),
    (q_d_om, "\\Omega^{\\star}"),
    (q_d_dlt, "\\delta"),
    (q_d_phi, "\\Phi"),
    (q_d_d_t, "\\frac{\\partial}{\\partial t}"),
    (q_d_kdelta, "\\delta"),
    (q_p_kdelta, "\\delta"),
    (q_d_icurvature, "\\cal{R}"),
    (q_p_icurvature, "\\cal{R}"),
    (q_d_ichr1, "\\Gamma"),
    (q_p_ichr1, "\\Gamma"),
    (q_d_ichr2, "\\Gamma"),
    (q_p_ichr2, "\\Gamma"),
    (q_d_ifc1, "\\gamma"),
    (q_p_ifc1, "\\gamma"),
    (q_d_ifc2, "\\gamma"),
    (q_p_ifc2, "\\gamma"),
    (q_d_ifb, "\\lambda"),
    (q_p_ifb, "\\lambda"),
    (q_d_ifg, "\\nu"),
    (q_d_levi_civita, "\\varepsilon"),
    (q_p_levi_civita, "\\varepsilon"),
  ]
  for w in words {
    putprop(w.0, Str(w.1), q_texword) |> ignore
  }
}
