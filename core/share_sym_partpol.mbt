// Port of share/sym/partpol.lisp: CHANGEMENTS DE REPRESENTATIONS SUR
// k[y1,..., yn][x1,..., xn]: explose, contract (avec ou sans test),
// partpol, part2cont et cont2part.
// Specials: drapeaux, modele, lvar, permut.

///|
/// `(throw 'rate '|...|)`
fn share_sym_partpol__rate(msg : String) -> Value raise {
  throw_tag(q_rate, sym(invert_case(msg)))
}

// FORME CONTRACTE D'UN POLYNOME SYMETRIQUE
// appels : contract(pol,lvar) ou tcontract(pol,lvar) t pour test

///|
/// AVEC TEST DE SYMETRIE
fn d_tcontract_init(d_pol : Value, d_lvar : Value) -> Value raise {
  if share_sym__is_equal(d_pol, int(0)) {
    int(0)
  } else {
    catch_tag(q_rate, () => n2ecrit(tpartpol(d_pol, d_lvar), cdr(d_lvar)))
  }
}

///|
/// SANS TEST DE SYMETRIE
fn d_contract_init(d_pol : Value, d_lvar : Value) -> Value raise {
  if share_sym__is_equal(d_pol, int(0)) {
    int(0)
  } else {
    meval(
      list3(
        list1(q_d_distri_ecrit),
        meval(list3(list1(q_d_partpol), d_pol, d_lvar)),
        d_lvar,
      ),
    )
  }
}

// PASSAGE D'UN POLYNOME SYMETRIQUE MACSYMA A SA REPRESENTATION
// PARTITIONNEE.

///|
fn d_p_tpartpol_init(d_pol : Value, d_lvar : Value) -> Value raise {
  if share_sym__is_equal(d_pol, int(0)) {
    cons(list1(q_mlist), Nil)
  } else {
    catch_tag(q_rate, () => macsy_list(ch1repol(p__tpartpol(d_pol, d_lvar))))
  }
}

///|
/// appele par pui en drapeau 5 mais si erreur pas de catch !
fn p__tpartpol(d_pol : Value, d_lvar : Value) -> Value raise {
  if share_sym__is_equal(d_pol, int(0)) {
    cons(list1(q_mlist), Nil)
  } else {
    // $ORLONG is not defined by the sym package.
    let lpol = sort_list(
      prep(lect(d_pol, cons(list1(q_mlist), d_lvar))),
      (a, b) => funcall(q_d_orlong, [a, b]).truthy(),
    )
    tpartpol2(lpol, int(length(cdr(d_lvar))))
  }
}

///|
fn d_tpartpol_init(d_pol : Value, d_lvar : Value) -> Value raise {
  if share_sym__is_equal(d_pol, int(0)) {
    cons(list1(q_mlist), Nil)
  } else {
    catch_tag(q_rate, () => macsy_list(ch1repol(tpartpol(d_pol, d_lvar))))
  }
}

///|
/// appele par e_sym (22 ..), pas de catch si erreur;
/// pol est sous la forme((coe .I)...) les +petit part devant
fn tpartpol(d_pol : Value, d_lvar : Value) -> Value raise {
  let pol = sort_list(prep(lect(d_pol, d_lvar)), (a, b) => d_lexic(a, b).truthy())
  tpartpol2(pol, int(length(cdr(d_lvar))))
}

///|
fn d_lexic(p : Value, q : Value) -> Value raise {
  if !equal(cdr(p), cdr(q)) {
    d_lex(cdr(p), cdr(q))
  } else {
    Nil
  }
}

///|
/// LE PARTITIONNEUR: Reunir les partitions identiques, rendre le
/// coefficient de la forme monomiale associee.
fn tpartpol2(lpol : Value, card : Value) -> Value raise {
  tpartpol3(card, lpol, card_orbit(cdar(lpol), card)) |> ignore
  lpol
}

///|
/// partitionnement avec test de symetrie, modification physique sur la
/// forme distribuee.
fn tpartpol3(card : Value, pol : Value, compteur : Value) -> Value raise {
  let mut pol = pol
  let mut compteur = compteur
  while true {
    if cdr(pol) is Nil {
      if eql(int(1), compteur) {
        return t
      }
      return share_sym_partpol__rate("manque des elements de l'orbite")
    }
    let coe1 = caar(pol)
    let coe2 = caadr(pol)
    let exp1 = cdar(pol)
    let exp2 = cdadr(pol)
    if equal(exp1, exp2) {
      if equal(coe1, coe2) {
        pol = rplacd(pol, cddr(pol))
        compteur = one_minus(compteur)
      } else {
        return share_sym_partpol__rate(
          "polynome non symetrique par ses coefficients",
        )
      }
    } else if eql(int(1), compteur) {
      pol = cdr(pol)
      compteur = card_orbit(exp2, card)
    } else {
      return share_sym_partpol__rate("manque des monomes")
    }
  }
  Nil
}

///|
/// PARTITIONNEMENT D'UN POLYNOME; SORTIE : LE POLYNOME PARTITIONNE AVEC
/// COMME REPRESENTATION : REP([pol]) = [ppart](1)
fn d_partpol_init(d_psym : Value, d_lvar : Value) -> Value raise {
  if share_sym__is_equal(d_psym, int(0)) {
    cons(list1(q_mlist), Nil)
  } else {
    cons(
      list1(q_mlist),
      mapcan(
        d_exposant => if share_sym__non_increasing(cddr(d_exposant)) {
          list1(d_exposant)
        } else {
          Nil
        },
        if equal(q_mlist, caar(d_psym)) {
          cdr(d_psym) // $psym est sous forme distribuee
        } else {
          cdr(meval(list3(list1(q_d_distri_lect), d_psym, d_lvar)))
        },
      ),
    )
  }
}

// FORME CONTRACTEE D'UN POLYNOME ==> REP([pol])(i)

///|
/// dans lect on met $polcontrac sous forme expand
fn d_cont2part_init(d_polcontrac : Value, d_lvar : Value) -> Value raise {
  if share_sym__is_equal(d_polcontrac, int(0)) {
    cons(list1(q_mlist), Nil)
  } else {
    macsy_list(cont2part_rep1(d_polcontrac, d_lvar))
  }
}

///|
fn cont2part_rep1(polcontrac : Value, d_lvar : Value) -> Value raise {
  ordonne_expo(lect(polcontrac, d_lvar))
}

///|
/// Rend des partitions de type 2
fn cont2part(polcontrac : Value, lvar : Value) -> Value raise {
  ch2repol(cont2part_rep1(polcontrac, cons(list1(q_mlist), lvar)))
}

///|
/// on le met sous forme rat; rat = (((rat simp)...) . listebase . 1)
fn d_partipol(polycontracte : Value) -> Value raise {
  let rat = d_rat(polycontracte, Nil)
  // LIST2CROCH is not defined by the sym package.
  cons(
    list1(q_mlist),
    mapcar(x => funcall(q_list2croch, [x]), partipol(rat)),
  )
}

///|
fn partipol(rat : Value) -> Value raise {
  partipol1(cadr(rat), cons(Nil, Nil))
}

///|
/// on aura lpart = ( (coe a1 m1 a2 m2 ....) ....) par accrochage de bord
fn partipol1(rat : Value, lpart : Value) -> Value raise {
  partipol2(lpart, cdr(rat), Nil, Nil) |> ignore
  cdr(lpart)
}

///|
/// representation des partitions avec un coe et eventuellement des
/// exposants nuls en tete.
fn partipol2(lpart : Value, rat : Value, part : Value, pile : Value) -> Value raise {
  let mut lpart = lpart
  let mut rat = rat
  let mut part = part
  let mut pile = pile
  while true {
    if rat is Nil {
      if pile is Nil {
        return Nil
      }
      // (apply 'partipol2 (cons lpart pile))
      rat = car(pile)
      part = cadr(pile)
      pile = caddr(pile)
    } else if numberp(cadr(rat)) {
      // $PART0 is not defined by the sym package.
      let p = funcall(q_d_part0, [
        sort_list(cons(car(rat), part), (a, b) => num_lt(a, b)),
        cadr(rat),
      ])
      lpart = cdr(rplacd(lpart, list1(p)))
      rat = cddr(rat)
    } else {
      let npile = if cddr(rat) is Cons(_) {
        list3(cddr(rat), part, pile)
      } else {
        pile
      }
      part = cons(car(rat), part)
      rat = cdadr(rat)
      pile = npile
    }
  }
  Nil
}

///|
fn d_part2cont_init(d_ppart : Value, d_lvar : Value) -> Value raise {
  if cdr(d_ppart) is Nil {
    int(0)
  } else {
    meval(list3(list1(q_d_distri_ecrit), d_ppart, d_lvar))
  }
}

///|
/// RAMENER TOUT LE POLYNOME SYMETRIQUE ASSOCIE A UNE FORME CONTRACTEE
/// appel : explose(polynome,[x1, ... ,xp])
fn d_explose_init(d_pc : Value, d_lvar : Value) -> Value raise {
  if share_sym__is_equal(d_pc, int(0)) {
    return int(0)
  }
  let lcoenuplet = lect(d_pc, d_lvar)
  meval(
    list3(
      list1(q_d_distri_ecrit),
      cons(
        list1(q_mlist),
        mapcan(
          coenuplet => {
            let coe = car(coenuplet)
            mapcar(
              permu => list_star([list1(q_mlist), coe, permu]),
              permut(cdr(coenuplet)),
            )
          },
          lcoenuplet,
        ),
      ),
      d_lvar,
    ),
  )
}

///|
/// ordonne_expo: a partir d'un polynome sous forme distribuee range tout les
/// exposants dans l'ordre decroissant
fn ordonne_expo(pol : Value) -> Value raise {
  mapcar(
    mon => cons(car(mon), sort_list(cdr(mon), (a, b) => num_gt(a, b))),
    pol,
  )
}

///|
/// Avec changement de repre'sentation
fn prep(pol : Value) -> Value raise {
  ch2repol(ordonne_expo(pol))
}

///|
fn init_share_partpol() -> Unit raise {
  let defs = [
    "((mdefine) (($tpartpol) $mpol $lvar) ((mprog) (($operation)) (($tpartpol_init) $mpol $lvar)))",
    "((mdefine) (($p_tpartpol) $mpol $lvar) ((mprog) (($operation)) (($p_tpartpol_init) $mpol $lvar)))",
    "((mdefine) (($partpol) $pol $lvar) ((mprog) (($operation)) (($partpol_init) $pol $lvar)))",
    "((mdefine) (($tcontract) $psym $lvar) ((mprog) (($operation)) (($tcontract_init) $psym $lvar)))",
    "((mdefine) (($contract) $psym $lvar) ((mprog) (($operation)) (($contract_init) $psym $lvar)))",
    "((mdefine) (($cont2part) $pcont $lvar) ((mprog) (($operation)) (($cont2part_init) $pcont $lvar)))",
    "((mdefine) (($part2cont) $ppart $lvar) ((mprog) (($operation)) (($part2cont_init) $ppart $lvar)))",
    "((mdefine) (($explose) $pc $lvar) ((mprog) (($operation)) (($explose_init) $pc $lvar)))",
  ]
  for d in defs {
    meval(lread(d)) |> ignore
  }
}
