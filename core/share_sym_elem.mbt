// Port of share/sym/elem.lisp: DECOMPOSITION D'UN POLYNOME SYMETRIQUE PAR
// LES SYMETRIQUES ELEMENTAIRES.
// appelle avec elem([card,e1, e2, ...],sym(x,y,..,z),[x,y,...,z])
// ou multi_elem pour des polyn\^omes multisym\'etriques.
// Specials: listei, $elem, nb1, lgi, coei, nblib.

///|
/// fonction bidon de chargement
fn d_bidon() -> Value raise {
  Nil
}

// MULTIDECOMPOSITION: Le polynome donne est multi-symetrique sous forme
// contractee

///|
fn d_multi_elem_init(
  d_multi_lelem : Value,
  d_multi_pc : Value,
  d_llvar : Value,
) -> Value raise {
  multi_elem(mapcar(x => cdr(x), cdr(d_multi_lelem)), d_multi_pc, cdr(d_llvar))
}

///|
/// cf. e_red1 plus loin
fn multi_elem(
  multi_lelem : Value,
  d_multi_pc : Value,
  l_dollvar : Value,
) -> Value raise {
  let mut multi_lelem = multi_lelem
  let mut pc = d_multi_pc
  let mut llvar = l_dollvar
  while true {
    if share_sym__is_equal(pc, int(0)) {
      return int(0)
    }
    if llvar is Nil {
      return pc
    }
    let npc = if share_sym__is_equal(pc, int(0)) {
      int(0)
    } else {
      e_red1(
        car(multi_lelem),
        lgparts(
          ch2repol(
            mapcar(
              x => cdr(x),
              cdr(meval(list3(list1(q_d_cont2part), pc, car(llvar)))),
            ),
          ),
        ),
      )
    }
    multi_lelem = cdr(multi_lelem)
    pc = npc
    llvar = cdr(llvar)
  }
  Nil
}

///|
fn d_elem_init(valei : Value, sym_ : Value, d_lvar : Value) -> Value raise {
  let sauvlistei = if boundp(q_listei) { symval(q_listei) } else { Nil }
  let elem = symval(q_d_elem)
  let r = if eql(elem, int(1)) {
    // sym = polynome contracte
    if share_sym__is_equal(sym_, int(0)) {
      int(0)
    } else {
      e_red1(
        cdr(valei),
        lgparts(
          ch2repol(
            mac2lisp(meval(list3(list1(q_d_cont2part), sym_, d_lvar))),
          ),
        ),
      )
    }
  } else if eql(elem, int(2)) {
    // le polynome symetrique en entier ou en partie
    if share_sym__is_equal(sym_, int(0)) {
      int(0)
    } else {
      e_red1(
        cdr(valei),
        lgparts(
          ch2repol(mac2lisp(meval(list3(list1(q_d_partpol), sym_, d_lvar)))),
        ),
      )
    }
  } else if eql(elem, int(3)) {
    // sym=REP([pol])(1) mais pas forcement ordonne'
    // mais les monomes sont tous suppose's distincts
    e_red1(cdr(valei), lgparts(ch2repol(mapcar(x => cdr(x), cdr(sym_)))))
  } else if eql(elem, int(4)) {
    // sym est le polynome symetrique; on test egalement sa symetrie
    let pol = lgparts(
      ch2repol(mac2lisp(meval(list3(list1(q_d_tpartpol), sym_, d_lvar)))),
    )
    e_red2(d_degrep(pol), pol, cdr(valei))
  } else if eql(elem, int(5)) {
    // sym = (REP([pol])(2) + longueurs) retirer les "mlist"
    e_red1(cdr(valei), mapcar(x => cdr(x), cdr(sym_)))
  } else if eql(elem, int(6)) {
    // sym = REP([pol])(2)
    e_red1(cdr(valei), lgparts(mapcar(x => cdr(x), cdr(sym_))))
  } else {
    Str("erreur $elem n'a pas de valeur")
  }
  set(q_listei, sauvlistei) |> ignore
  r
}

///|
fn e_red1(l : Value, ppart : Value) -> Value raise {
  e_red2(
    d_degrep(ppart),
    sort_list(ppart, (a, b) => d_e_lexinv(a, b).truthy()),
    l,
  )
}

///|
fn e_red2(degpol : Value, ppart : Value, l : Value) -> Value raise {
  if eql(int(0), lgi(ppart)) {
    // on n'a qu'une constante
    coei(ppart)
  } else {
    set(
      q_listei,
      rangei(
        l,
        if l is Cons(_) && numberp(car(l)) {
          num_min(car(l), degpol) // le cardinal est impose
        } else {
          degpol
        },
        int(length(l)),
      ),
    )
    |> ignore
    // autant que l'inf du cardinal  et du degre du polynome
    d_reduit(if numberp(car(l)) { car(l) } else { degpol }, ppart)
  }
}

// CREATION DE LA LISTE listei DES VALEURS DES ELEMENTAIRES
// l=(card e1 e2 ... e(lg))  card est le cardinal de l'alphabet.

///|
/// on range les plus grand en premier
fn rangei(l : Value, n : Value, lg : Value) -> Value raise {
  if eql(one_plus(n), lg) {
    l
  } else {
    append(l, rangei2(Nil, lg, n))
  }
}

///|
fn rangei2(lesei : Value, i : Value, n : Value) -> Value raise {
  let mut lesei = lesei
  let mut i = i
  while !num_lt(n, i) {
    lesei = cons(share_sym__concat([q_d_e, i]), lesei)
    i = one_plus(i)
  }
  nreverse(lesei)
}

// LA BOUCLE PRINCIPALE
// sym = [lppart](2) ordonnee dans l'ordre lexicographique decroissant.

///|
fn d_reduit(card : Value, sym_ : Value) -> Value raise {
  let mut sym_ = sym_
  while true {
    let i = moni(sym_)
    if sym_ is Nil || syele(i).truthy() {
      return e_ecrit(sym_)
    }
    sym_ = somme(
      cdr(sym_),
      devel1(factpart(i), coei(sym_), lgi(sym_), card),
      q_d_e_lexinv,
    )
  }
  Nil
}

///|
/// FACTORISATION DE I
fn factpart(i : Value) -> Value raise {
  let mut flag = false
  let mut alt = false
  let j = mapcar(
    puiounb => {
      alt = !alt
      if alt {
        if eql(int(1), puiounb) {
          flag = true
          Nil
        } else {
          one_minus(puiounb)
        }
      } else {
        puiounb
      }
    },
    i,
  )
  if flag {
    set(q_nb1, car(last(j))) |> ignore
    nbutlast(nbutlast(j))
  } else {
    set(q_nb1, int(0)) |> ignore
    j
  }
}

// REECRITURE DE I
// Developpement de ei*J ou i= lgI = nb1 + lgJ
// J=(pui1 n1 pui2 n2 .....) avec puik > pui(k-1)

///|
fn devel1(j : Value, coei_ : Value, lgi_ : Value, card : Value) -> Value raise {
  // COEI and LGI are special: RAMSOLFIN reads them
  with_specials([(q_coei, coei_), (q_lgi, lgi_)], () => {
    let coej = share_sym__mult(coei_, nth(to_int(lgi_), symval(q_listei)))
    let nblib = num_sub(card, lgi_)
    with_special(q_nblib, nblib, () => nconc(
      if plusp(nblib) {
        devel2(j, nblib, cons(Nil, Nil))
      } else {
        Nil
      },
      if !numberp(coej) || !zerop(coej) {
        list1(list_star([num_sub(lgi_, symval(q_nb1)), coej, j]))
      } else {
        Nil
      },
    ))
  })
}

///|
fn devel2(j : Value, nblib : Value, pilesol : Value) -> Value raise {
  with_special(q_nblib, nblib, () => {
    devel3(pilesol, j, int(0), cadr(j), cons(int(-1), Nil), Nil) |> ignore
    cddr(pilesol) // pilesol=(nil I . listparti)
  })
}

// r le nombre d'elements passant a la meme puissance superieure, pui1 + 1.
// r vaut n1 au depart et decroit jusqu'a une valeur inf non negative.
// Ou inf est choisie afin que la forme monomiale representee
// par la partition ramenee soit non nulle relativement au cardinal, card, de
// l'alphabet concidere. En fait il faut que la longueur de cette partition
// qui est de nbpui1 + lgI soit inferieure ou egal a card.
//    solu est la partition partielle d'une partition solution en construction
//    pile contient les partitions en construction mais mise en instance
//    pilesol contient les partition solutions deja construites

///|
fn devel3(
  pilesol : Value,
  j : Value,
  nbpui1 : Value,
  r : Value,
  solu : Value,
  pile : Value,
) -> Value raise {
  let mut pilesol = pilesol
  let mut j = j
  let mut nbpui1 = nbpui1
  let mut r = r
  let mut solu = solu
  let mut pile = pile
  while true {
    if j is Nil {
      rplacd(
        pilesol,
        list1(
          ramsolfin(nbpui1, num_add(nbpui1, symval(q_nb1)), solu),
        ),
      )
      |> ignore
      if pile is Nil {
        return Nil
      }
      // pas apply pour recursivite terminale
      pilesol = cdr(pilesol)
      j = car(pile)
      nbpui1 = cadr(pile)
      r = caddr(pile)
      solu = car(cdddr(pile))
      pile = car(last(pile))
    } else {
      let reste = num_sub(cadr(j), r)
      let nnbpui1 = num_add(nbpui1, reste)
      // on met le cas r --> r-1 en instance (si nnbpui1 + lgI < card) en
      // empilant, et on passe tout de suite a r --> n2 pour continuer a
      // construire une partition solution.
      let npile = if plusp(r) && num_gt(symval(q_nblib), nnbpui1) {
        // ** pour ne pas depasser le cardinal de l'alphabet
        list([j, nbpui1, one_minus(r), solu, pile])
      } else {
        pile
      }
      let nsolu = ramsol(car(j), reste, r, solu)
      let nr = cadr(cddr(j))
      j = cddr(j) // (pui2 n2 .....)
      nbpui1 = nnbpui1 // lg(M) >= nbpui1 + lgI
      r = nr // n2
      solu = nsolu
      pile = npile
    }
  }
  Nil
}

///|
fn ramsol(pj : Value, nbj : Value, r : Value, solu : Value) -> Value raise {
  if eql(int(0), r) {
    list_star([car(solu), nbj, pj, cdr(solu)])
  } else {
    let solu = ramsol2(pj, r, car(solu), cdr(solu))
    if eql(int(0), nbj) {
      solu
    } else {
      list_star([car(solu), nbj, pj, cdr(solu)])
    }
  }
}

///|
fn ramsol2(pj : Value, r : Value, coe : Value, solu : Value) -> Value raise {
  if eql(cadr(solu), one_plus(pj)) {
    list_star([calcoe(coe, car(solu), r), num_add(car(solu), r), cdr(solu)])
  } else {
    list_star([coe, r, one_plus(pj), solu])
  }
}

///|
/// tnb1=0 si sol=I et que nb1=0
fn ramsolfin(nbpui1 : Value, tnb1 : Value, solu : Value) -> Value raise {
  let lgi_ = symval(q_lgi)
  let coei_ = symval(q_coei)
  if eql(int(1), caddr(solu)) {
    list_star([
      num_add(lgi_, nbpui1),
      share_sym__mult(coei_, calcoe(car(solu), tnb1, cadr(solu))),
      reverse(cons(num_add(tnb1, cadr(solu)), cddr(solu))),
    ])
  } else {
    list_star([
      num_add(lgi_, nbpui1),
      share_sym__mult(coei_, car(solu)),
      reverse(list_star([tnb1, int(1), cdr(solu)])),
    ])
  }
}

///|
/// CALCUL DU COEFFICIENT BINOMIAL C(n+c,c)
fn calcoe(coe : Value, c : Value, n : Value) -> Value raise {
  let nc = num_add(n, c)
  num_mul(coe, calcoe2(inferieur(n, c), nc, one_minus(nc), int(2)))
}

///|
fn calcoe2(n : Value, res : Value, nc : Value, i : Value) -> Value raise {
  let mut res = res
  let mut nc = nc
  let mut i = i
  while !eql(one_plus(n), i) {
    res = div(num_mul(res, nc), i)
    nc = one_minus(nc)
    i = one_plus(i)
  }
  res
}

///|
/// syele teste si une partition est celle d'une fonction
/// symetrique elementaire
fn syele(mon : Value) -> Value raise {
  lbool(mon is Cons(_) && eql(int(1), car(mon)) && cddr(mon) is Nil)
}

///|
fn inferieur(a : Value, i : Value) -> Value raise {
  if a is Nil {
    Nil
  } else {
    num_min(a, i)
  }
}

// L'ECRIVAIN

///|
fn e_ecrit(solu : Value) -> Value raise {
  let solu = nreverse(solu)
  if solu is Nil {
    int(0)
  } else if eql(int(0), lgi(solu)) {
    e_ecrit2(cdr(solu), cdr(symval(q_listei)), coei(solu), int(1))
  } else {
    e_ecrit2(solu, cdr(symval(q_listei)), int(0), int(1))
  }
}

///|
fn e_ecrit2(
  solu : Value,
  listei : Value,
  mpol : Value,
  i_init : Value,
) -> Value raise {
  let mut solu = solu
  let mut listei = listei
  let mut mpol = mpol
  let mut i_init = i_init
  while true {
    let i = lgi(solu)
    if solu is Nil {
      return mpol
    }
    if eql(i, i_init) {
      mpol = share_sym__add(mpol, share_sym__mult(coei(solu), car(listei)))
    } else {
      listei = share_sym__nthcdr(num_sub(i, i_init), listei)
      mpol = share_sym__add(mpol, share_sym__mult(coei(solu), car(listei)))
      i_init = i
    }
    solu = cdr(solu)
  }
  Nil
}

///|
fn init_share_elem() -> Unit raise {
  share_sym__defmexpr(
    q_d_elem,
    "((lambda ()) ((mlist) $valei $sym $lvar) ((mprog) (($operation)) (($elem_init) $valei $sym $lvar)))",
    item_text="(($elem) $valei $sym $lvar)",
  )
  share_sym__defmexpr(
    q_d_multi_elem,
    "((lambda ()) ((mlist) $lvalei $pc $llvar) ((mprog) (($operation)) (($multi_elem_init) $lvalei $pc $llvar)))",
    item_text="(($multi_elem) $lvalei $pc $llvar)",
  )
}
