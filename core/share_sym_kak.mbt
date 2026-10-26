// Port of share/sym/kak.lisp: SUR UN PROBLEME DE PIERRE CARTIER.
// Produit k a k ou sommes k a k des racines d'un polynome: le cas des
// resolvantes symetriques lorsque la fonction resolvante est une somme ou
// un produit.
// Specials: listpi, listei, k, coe, $somrac.

///|
/// SOMME K A K DES RACINES D'UN POLYNOME P
fn d_somrac_init(listei : Value, k : Value) -> Value raise {
  with_specials([(q_listei, listei), (q_k, k)], () => if equal(
      q_d_puissances,
      symval(q_d_somrac),
    ) {
    d_p_rac(symval(q_listei), symval(q_k))
  } else {
    d_e_rac(symval(q_listei), symval(q_k))
  })
}

///|
/// DECOMPOSITION DES FORMES MONOMIALES CONSTITUANT CHAQUE FONCTION
/// PUISSANCE DU NOUVEL ALPHABET EN FONCTION DES FONCTIONS PUISSANCE DES
/// RACINES DE P. listei=((mlist) e1 ... en)
fn d_p_rac(listei : Value, k : Value) -> Value raise {
  with_specials([(q_listei, listei), (q_k, k)], () => {
    set(q_listei, cdr(symval(q_listei))) |> ignore
    let n = int(length(symval(q_listei)))
    if num_lt(n, symval(q_k)) {
      Str(" impossible ")
    } else {
      meval(list1(list1(q_d_bidon2))) |> ignore
      let binnk = binomial(n, symval(q_k))
      let listpi1 = cdr(
        meval(
          list3(
            list1(q_d_ele2pui),
            binnk,
            cons(list1(q_mlist), cons(n, symval(q_listei))),
          ),
        ),
      )
      with_special(q_listpi, listpi1, () => {
        let listpi2 = cons(binnk, d_som_pipj(n, binnk, Nil))
        with_special(q_listpi, listpi2, () => pui2polynome(
          q_d_y,
          symval(q_listpi),
        ))
      })
    }
  })
}

///|
/// recherche des Fonctions puissances Pi en fonction des pj
fn d_som_pipj(n : Value, i : Value, nxlistpi : Value) -> Value raise {
  let mut i = i
  let mut nxlistpi = nxlistpi
  while !eql(int(0), i) {
    nxlistpi = cons(
      d_p_reduit(d_init_pi2mon(n, i, num_min(symval(q_k), i))),
      nxlistpi,
    )
    i = one_minus(i)
  }
  nxlistpi
}

///|
/// Recherche de l'expression d'un Pi dans la base des formes monomiales
/// sur S[A]
fn d_init_pi2mon(n : Value, i : Value, infki : Value) -> Value raise {
  if eql(i, infki) {
    d_pi2mon(n, i, infki, Nil, binomial(num_sub(n, i), num_sub(symval(q_k), i)))
  } else {
    d_pi2mon(n, i, infki, Nil, int(1))
  }
}

///|
/// recherche des fonctions monomiales en fonction de leur longueur, var,
/// On les range au fur et a mesure dans sym
fn d_pi2mon(
  n : Value,
  pui : Value,
  var_ : Value,
  sym_ : Value,
  coe : Value,
) -> Value raise {
  let mut var_ = var_
  let mut sym_ = sym_
  let mut coe = coe
  while !eql(int(0), var_) {
    let v = var_
    let c = coe
    // COE is special: $INIT_MONLGFIX reads it
    sym_ = nconc(
      sym_,
      with_special(q_coe, c, () => d_init_monlgfix(pui, v, cons(Nil, Nil))),
    )
    coe = div(
      num_mul(coe, num_sub(n, one_minus(var_))),
      num_sub(symval(q_k), one_minus(var_)),
    )
    var_ = one_minus(var_)
  }
  sym_
}

///|
/// recherche des formes monomiales de S[A], representant Pi (i=pui)
/// et ayant leur longueur egale a var.
fn d_init_monlgfix(pui : Value, var_ : Value, slvarh : Value) -> Value raise {
  d_monlgfix(
    pui,
    one_minus(var_),
    one_minus(var_),
    slvarh,
    cons(int(1), Nil),
    maxote(pui, var_),
  )
  |> ignore
  let mut ppart = cdr(slvarh)
  while ppart is Cons(_) {
    rplaca(
      ppart,
      cons(var_, cons(share_sym__mult(symval(q_coe), caar(ppart)), cdar(ppart))),
    )
    |> ignore
    ppart = cdr(ppart)
  }
  cdr(slvarh)
}

// PAR LES FONCTIONS SYMETRIQUES ELEMENTAIRES ei DU POLYNOME DE DEPART

///|
/// listei=(e1,...,en)=((mlist) e1 ... en)
fn d_e_rac(listei : Value, k : Value) -> Value raise {
  with_specials([(q_listei, listei), (q_k, k)], () => {
    let n = one_minus(int(length(symval(q_listei))))
    if num_lt(n, symval(q_k)) {
      Str(" impossible ")
    } else if meval(list1(list1(q_d_bidon))).truthy() {
      // permet de charger le fichier elem ou pas.
      let binnk = binomial(n, symval(q_k))
      with_special(q_listei, cons(n, cdr(symval(q_listei))), () => pui2polynome(
        q_d_y,
        cons(binnk, d_rac2(binnk, Nil, n)),
      ))
    } else {
      Nil
    }
  })
}

///|
/// Recherche des Pi (i=1 a binnk) en fonction ds ej (j=1 a n)
fn d_rac2(l : Value, nxlistpi : Value, n : Value) -> Value raise {
  let mut l = l
  let mut nxlistpi = nxlistpi
  while !eql(int(0), l) {
    nxlistpi = cons(d_init_piej(l, num_min(symval(q_k), l), n), nxlistpi)
    l = one_minus(l)
  }
  nxlistpi
}

///|
/// recherche d'un Pi dans la base des ej de S[A]
fn d_init_piej(l : Value, infkl : Value, n : Value) -> Value raise {
  if eql(l, infkl) {
    d_piej(
      l,
      infkl,
      int(0),
      binomial(num_sub(n, l), num_sub(symval(q_k), l)),
      n,
    )
  } else {
    d_piej(l, infkl, int(0), int(1), n)
  }
}

///|
/// recherche par les monomiales de S[A], rentrant dans la decomposition
/// de Pi et ayant meme longueur. Que l'on decompose en fonction des ej et
/// que l'on range longueur apres longueur (longueur = var) dans Pi. i=pui
fn d_piej(
  pui : Value,
  var_ : Value,
  d_pi : Value,
  coe : Value,
  n : Value,
) -> Value raise {
  let mut var_ = var_
  let mut pi_ = d_pi
  let mut coe = coe
  while !eql(int(0), var_) {
    let v = var_
    let c = coe
    let p = pi_
    pi_ = with_special(q_coe, c, () => share_sym__add(
      p,
      share_sym__mult(c, d_piej_lgfix(pui, v, cons(Nil, Nil), n)),
    ))
    coe = div(
      num_mul(coe, num_sub(n, one_minus(var_))),
      num_sub(symval(q_k), one_minus(var_)),
    )
    var_ = one_minus(var_)
  }
  pi_
}

///|
/// recherche des formes monomiales a longueur fixe var
fn d_piej_lgfix(
  pui : Value,
  var_ : Value,
  slvarh : Value,
  n : Value,
) -> Value raise {
  d_monlgfix(
    pui,
    one_minus(var_),
    one_minus(var_),
    slvarh,
    cons(int(1), Nil),
    maxote(pui, var_),
  )
  |> ignore
  let mut ppart = cdr(slvarh)
  while ppart is Cons(_) {
    rplaca(ppart, cons(var_, car(ppart))) |> ignore
    ppart = cdr(ppart)
  }
  d_reduit(num_min(pui, n), cdr(slvarh)) // varm
}

///|
/// Calcul des formes monomiales et de leur coefficient intervenant dans Pi
/// a longueur fixe et donc aussi a poids i fixe.
/// recherche proprement dite (non recursive terminale)
fn d_monlgfix(
  pui : Value,
  rvar : Value,
  ote : Value,
  slvar : Value,
  poule : Value,
  maxote_ : Value,
) -> Value raise {
  if num_gt(int(0), rvar) {
    rplacd(slvar, list1(cons(car(poule), reverse(cdr(poule)))))
  } else {
    d_monlgfix(
      ote,
      one_minus(rvar),
      num_max(one_minus(rvar), num_sub(num_mul(int(2), ote), pui)),
      slvar,
      d_met(pui, ote, poule),
      maxote(ote, rvar),
    )
    |> ignore
    if num_lt(ote, maxote_) {
      d_monlgfix(pui, rvar, one_plus(ote), last(slvar), poule, maxote_)
    } else {
      Nil
    }
  }
}

///|
fn d_met(pui : Value, ote : Value, poule : Value) -> Value raise {
  let nxcoe = share_sym__mult(car(poule), binomial(pui, ote))
  let nxpui = num_sub(pui, ote)
  if eq(caddr(poule), nxpui) {
    list_star([nxcoe, one_plus(cadr(poule)), cddr(poule)])
  } else {
    list_star([nxcoe, int(1), nxpui, cdr(poule)])
  }
}

// PRODUIT K A K; listei = ((mlist) e1 .en) sans p0

///|
fn d_prodkak(listei : Value, k : Value) -> Value raise {
  with_specials([(q_listei, listei), (q_k, k)], () => {
    set(q_listei, cdr(symval(q_listei))) |> ignore
    let n = int(length(symval(q_listei)))
    if num_lt(n, symval(q_k)) {
      Str(" impossible ")
    } else {
      meval(list1(list1(q_d_bidon2))) |> ignore
      let binnk = binomial(n, symval(q_k))
      let listpi = cdr(
        meval(
          list3(
            list1(q_d_ele2pui),
            mult(binnk, symval(q_k)),
            cons(list1(q_mlist), cons(n, symval(q_listei))),
          ),
        ),
      )
      with_special(q_listpi, listpi, () => pui2polynome(
        q_d_y,
        cons(binnk, d_listpui(binnk, Nil, symval(q_k))),
      ))
    }
  })
}

///|
/// liste des fonctions puissances dans l'alphabet des racines du polynome
/// cherche.
fn d_listpui(i : Value, listpui : Value, k : Value) -> Value raise {
  let mut i = i
  let mut listpui = listpui
  while !eql(int(0), i) {
    listpui = cons(d_p_reduit(list1(list([k, int(1), i, k]))), listpui)
    i = one_minus(i)
  }
  listpui
}

///|
fn init_share_kak() -> Unit raise {
  share_sym__defmexpr(
    q_d_somrac,
    "((lambda ()) ((mlist) $listei $k) ((mprog) (($operation)) (($somrac_init) $listei $k)))",
    item_text="(($somrac) $listei $k)",
  )
  share_sym__defmexpr(
    q_d_prodrac,
    "((lambda ()) ((mlist) $listei $k) ((mprog) (($operation)) (($prodkak) $listei $k)))",
    item_text="(($prodrac) $listei $k)",
  )
}
