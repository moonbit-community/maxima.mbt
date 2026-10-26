// Port of share/sym/arite.lisp: passage d'une fonction puissance d'une
// resolvante en p variables a une fonction puissance en n variables gra^ce
// au the'ore`me de l'arite' (un coefficient binomial a chaque partition).

///|
fn arite_init(degre : Value, arite : Value, d_puissances : Value) -> Value raise {
  cons(
    list1(q_mlist),
    mapcar(
      d_pui => cons(list1(q_mlist), n__complete_pui(degre, arite, d_pui)),
      cdr(d_puissances),
    ),
  )
}

///|
fn arite_physique_init(
  degre : Value,
  arite : Value,
  d_puissances : Value,
) -> Value raise {
  mapc(
    d_pui => complete_pui_physique(degre, arite, d_pui) |> ignore,
    cdr(d_puissances),
  )
  |> ignore
  d_puissances
}

///|
/// Ici le remplacement se re'alise physiquement
fn complete_pui_physique(
  n : Value,
  p : Value,
  d_puissance_resolvante : Value,
) -> Value raise {
  mapc(
    d_part => {
      // la longueur de la partition n'est pas en tete : (lg coeff . I)
      let lg = longueur(cddr(d_part))
      rplaca(
        cdr(d_part),
        num_mul(cadr(d_part), binomial(num_sub(n, lg), num_sub(p, lg))),
      )
      |> ignore
    },
    cdr(d_puissance_resolvante),
  )
}

///|
/// attention, il existe une fonction complete_pui dans resolvante
fn n__complete_pui(
  n : Value,
  p : Value,
  d_puissance_resolvante : Value,
) -> Value raise {
  mapcar(
    d_part => {
      // part=(part)(1) comme representation
      let lg = longueur(cddr(d_part))
      list_star([
        list1(q_mlist),
        share_sym__mult(cadr(d_part), binomial(num_sub(n, lg), num_sub(p, lg))),
        cddr(d_part),
      ])
    },
    cdr(d_puissance_resolvante),
  )
}

///|
fn init_share_arite() -> Unit raise {
  share_sym__defmexpr(
    q_d_arite,
    "((lambda ()) ((mlist) $degre $arite $puissances) ((mprog) (($operation)) ((arite_init) $degre $arite $puissances)))",
    item_text="(($arite) $degre $arite $puissances)",
  )
  share_sym__defmexpr(
    q_d_arite_physique,
    "((lambda ()) ((mlist) $degre $arite $puissances) ((mprog) (($operation)) ((arite_physique_init) $degre $arite $puissances)))",
    item_text="(($arite_physique) $degre $arite $puissances)",
  )
}
