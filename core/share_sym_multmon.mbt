// Port of share/sym/multmon.lisp: PRODUIT DE DEUX FORMES MONOMIALES.
// multsym(ppart1,ppart2,card)
// LE CALCUL N'EST ABSOLUMENT PAS SYMETRIQUE, IL FAUT QUE ppart2 soit
// plus creux que ppart1 si l'on desire etre efficace.
// Specials: terparts.

///|
fn d_multsym_init(d_1ppart : Value, d_2ppart : Value, card : Value) -> Value raise {
  macsy_list(
    multsym(
      mapcar(x => cdr(x), cdr(d_1ppart)),
      mapcar(x => cdr(x), cdr(d_2ppart)),
      card,
    ),
  )
}

///|
/// Remarque : multmon restitue des ppart ordones
/// dans l'ordre lexicographique decroissant.
fn multsym(n1ppart : Value, n2ppart : Value, card : Value) -> Value raise {
  let mut solution : Value = Nil
  for term1 in n1ppart.iter() {
    for t2 in n2ppart.iter() {
      solution = somme_coef(
        share_sym__merge(solution, mult_term(term1, t2, card), (a, b) => lex_term(
            a, b,
          ).truthy()),
      )
    }
  }
  solution
}

///|
fn mult_term(term1 : Value, term2 : Value, card : Value) -> Value raise {
  mapcar(
    term => rplaca(
      term,
      share_sym__mult(car(term), share_sym__mult(car(term1), car(term2))),
    ),
    multmon(cdr(term1), cdr(term2), card),
  )
}

///|
/// Produit de deux formes monomiales sous formes contractees
fn d_multmon_init(d_mi : Value, d_mj : Value, card : Value) -> Value raise {
  if equal(int(0), d_mi) || equal(int(0), d_mj) {
    int(0)
  } else {
    let i = fmon2part(d_mi)
    let j = fmon2part(d_mj)
    ecrit_pol(multmon(i, j, card), lvar(card, Nil))
  }
}

///|
/// PASSAGE D'UNE FORME MONOMIALE A SA REPRESENTATION PARTITIONNELLE
/// [forme monomiale] ---> [partition](1)
fn fmon2part(m : Value) -> Value raise {
  let rat = cadr(d_rat(m, Nil))
  sort_list(chexpo(caddr(rat), list1(cadr(rat))), (a, b) => num_gt(a, b))
}

///|
fn chexpo(liste : Value, lexpo : Value) -> Value raise {
  let mut liste = liste
  let mut lexpo = lexpo
  while !numberp(liste) {
    lexpo = cons(cadr(liste), lexpo)
    liste = caddr(liste)
  }
  lexpo
}

///|
/// Produit de deux formes monomiales sous forme de partition , type 1.
/// Rend la plus grande partition en premier.
/// Les partitions ont des zeros a la fin
/// on complete I avec de zeros
fn multmon(i : Value, j : Value, card : Value) -> Value raise {
  let i = fini0(i, card)
  let j = epur0(j)
  let lperm = permut(j)
  // TERPARTS is special: PARTI_SOM reads it
  with_special(q_terparts, cons(Nil, Nil), () => {
    mapc(j => parti_som_init(i, j, symval(q_terparts)) |> ignore, lperm)
    |> ignore
    cdr(nreverse(symval(q_terparts)))
  })
}

///|
/// on rajoute les zeros
fn fini0(i : Value, card : Value) -> Value raise {
  nconc(i, share_sym__make_list(num_sub(card, int(length(i))), int(0)))
}

///|
/// on enleve les zeros
fn epur0(j : Value) -> Value raise {
  mapcan(
    part => if num_lt(int(0), part) {
      list1(part)
    } else {
      Nil
    },
    j,
  )
}

// OBTENTION DE CERTAINES DES PARTITIONS SOLUTION A PARTIR D'UNE
// PERMUTATION DE J
// I=(i1 i2 ... in) avec i1>i2>...>in>=0 n=card
// J est une permutation de Jo (sans les parts nulles)
// on desire faire la somme de I avec toutes les partitions K,
// construites a partir de J par insertion de zeros, et telles
// que IK=((i1,k1),(i2,k2), ... , (in , kn)) soit dans l'ordre
// lexicographique decroissant.
// On associe alors a K+I le quotient des 2 valeurs c1 et c2.
// Ou c1 est le nombre de permutations laissant I+K invariante
// et c2 le nombre de permutations laissant IK invariante.

///|
fn parti_som_init(i : Value, j : Value, terparts : Value) -> Value raise {
  with_special(q_terparts, terparts, () => parti_som(i, j, Nil, Nil))
}

///|
/// I se met au fur et a mesure dans RI, et K dans RK.
/// les solutions IK se rangent dans terparts.
fn parti_som(i : Value, j : Value, ri : Value, rk : Value) -> Value raise {
  if j is Nil {
    share_sym__attach(
      somme_coe(
        nconc(reverse(i), ri),
        append(share_sym__make_list(int(length(i)), int(0)), rk),
      ),
      symval(q_terparts),
    )
  } else {
    // conservation de l'ordre lex sur les couples solutions
    if ri is Nil || num_lt(car(i), car(ri)) || !num_lt(car(rk), car(j)) {
      parti_som(cdr(i), cdr(j), cons(car(i), ri), cons(car(j), rk)) |> ignore
    }
    // si le cardinal le permet, on va pouvoir rajouter des zeros
    if !(length(cdr(i)) < length(j)) {
      parti_som(cdr(i), j, cons(car(i), ri), cons(int(0), rk))
    } else {
      Nil
    }
  }
}

///|
fn somme_coe(i : Value, k : Value) -> Value raise {
  let ipk = sort_list(mapcar2((a, b) => num_add(a, b), i, k), (a, b) => num_gt(
    a, b,
  ))
  let cik = mapcar2((a, b) => cons(a, b), i, k)
  cons(coei_plusk(ipk, cik), ipk)
}

///|
fn coei_plusk(i_plusk : Value, cik : Value) -> Value raise {
  num_div(card_stab(i_plusk, q_eql), card_stab(cik, q_equal))
}

///|
fn init_share_multmon() -> Unit raise {
  share_sym__defmexpr(
    q_d_multmon,
    "((lambda ()) ((mlist) $mi $mj $card) ((mprog) (($operation)) (($multmon_init) $mi $mj $card)))",
    item_text="(($multmon) $mi $mj $card)",
  )
  share_sym__defmexpr(
    q_d_multsym,
    "((lambda ()) ((mlist) $2ppart $1ppart $card) ((mprog) (($operation)) (($multsym_init) $1ppart $2ppart $card)))",
    item_text="(($multsym) $1ppart $2ppart $card)",
  )
}
