// Port of share/sym/pui.lisp: PASSAGE DES FONCTIONS PUISSANCES AUX FORMES
// MONOMIALES.
// appel avec pui([card,p1,...,pn],sym(x,y,..,z),[x,y,...,z])
// Specials: listpi, $pui, $testpartpol.

///|
/// fonction bidon de chargement
fn d_bidon2() -> Value raise {
  Nil
}

// MULTIDECOMPOSITION

///|
fn d_multi_pui_init(
  d_multi_lpui : Value,
  d_multi_pc : Value,
  d_llvar : Value,
) -> Value raise {
  multi_pui(cdr(d_multi_lpui), d_multi_pc, cdr(d_llvar))
}

///|
/// cf. p_red1
fn multi_pui(
  multi_lpui : Value,
  d_multi_pc : Value,
  l_dollvar : Value,
) -> Value raise {
  let mut multi_lpui = multi_lpui
  let mut pc = d_multi_pc
  let mut llvar = l_dollvar
  while true {
    if share_sym__is_equal(pc, int(0)) {
      return int(0)
    }
    if llvar is Nil {
      return pc
    }
    // on a le polynome multisymetrique sous forme contracte'; on considere
    // qu'il est symetrique en un bloc de variables, les autres intervenant
    // dans les coefficients; on ramene sa forme partitionnee avec les
    // longueurs devant
    let npc = if share_sym__is_equal(pc, int(0)) {
      int(0)
    } else {
      p__red1(
        car(multi_lpui),
        lgparts(
          ch2repol(
            mac2lisp(meval(list3(list1(q_d_cont2part), pc, car(llvar)))),
          ),
        ),
      )
    }
    multi_lpui = cdr(multi_lpui)
    pc = npc
    llvar = cdr(llvar)
  }
  Nil
}

///|
/// valpi = ((mlist) card p1 ....)  ou card est le cardinal;
/// sym est un polynome symetrique pouvant etre represente
/// de plusieurs manieres en entree; lvar = ((mlist) x1 x2 ...).
/// Representation interne : REP([pol]) = [lppart](2); listpi=(card p1 ...)
fn d_pui_init(valpi : Value, sym_ : Value, d_lvar : Value) -> Value raise {
  let sauvlistpi = if boundp(q_listpi) { symval(q_listpi) } else { Nil }
  let pui = symval(q_d_pui)
  let r = if eql(pui, int(1)) {
    // sym = polynome contracte
    if share_sym__is_equal(sym_, int(0)) {
      int(0)
    } else {
      p__red1(
        valpi,
        lgparts(
          ch2repol(
            mac2lisp(meval(list3(list1(q_d_cont2part), sym_, d_lvar))),
          ),
        ),
      )
    }
  } else if eql(pui, int(2)) {
    // le polynome symetrique en entier ou en partie
    if share_sym__is_equal(sym_, int(0)) {
      int(0)
    } else {
      p__red1(
        valpi,
        lgparts(
          ch2repol(mac2lisp(meval(list3(list1(q_d_partpol), sym_, d_lvar)))),
        ),
      )
    }
  } else if eql(pui, int(3)) {
    // sym=REP([pol])(1)
    p__red1(valpi, lgparts(ch2repol(mapcar(x => cdr(x), cdr(sym_)))))
  } else if eql(pui, int(4)) {
    // sym est le polynome symetrique; on test egalement sa symetrie
    let pol = lgparts(
      ch2repol(mac2lisp(meval(list3(list1(q_d_tpartpol), sym_, d_lvar)))),
    )
    p__red2(d_degrep(pol), pol, valpi)
  } else if eql(pui, int(5)) {
    // sym = (REP([pol])(2) + longueurs) retirer les "mlist"
    p__red1(valpi, mapcar(x => cdr(x), cdr(sym_)))
  } else if eql(pui, int(6)) {
    // sym = REP([pol])(2)
    p__red1(valpi, lgparts(mapcar(x => cdr(x), cdr(sym_))))
  } else {
    Str("erreur $pui n'a pas de valeur")
  }
  set(q_listpi, sauvlistpi) |> ignore
  r
}

///|
fn p__red1(d_l : Value, ppart : Value) -> Value raise {
  p__red2(
    d_degrep(ppart),
    sort_list(ppart, (a, b) => orlongsup(a, b).truthy()),
    d_l,
  )
}

///|
/// on n'a qu'une constante; dans fichier chbase
fn p__red2(degpol : Value, ppart : Value, d_l : Value) -> Value raise {
  if eql(int(0), lgi(ppart)) {
    coei(ppart)
  } else {
    set(q_listpi, cdr(meval(list3(list1(q_d_puireduc), degpol, d_l)))) |> ignore
    d_p_reduit(ppart)
  }
}

///|
/// LA BOUCLE PRINCIPALE
fn d_p_reduit(sym_ : Value) -> Value raise {
  let mut sym_ = sym_
  while true {
    if sym_ is Nil || eql(int(1), lgi(sym_)) {
      return p__ecrit(sym_)
    }
    if eql(int(2), lgi(sym_)) {
      return longde2(sym_, int(0))
    }
    sym_ = somme(
      termrest(sym_),
      p__reducpart(moni(sym_), coei(sym_), lgi(sym_)),
      q_orlongsup,
    )
  }
  Nil
}

///|
/// Pour le fichier kak uniquement :
fn d_p_reduit_init(d_sym : Value) -> Value raise {
  d_p_reduit(mapcar(x => cdr(x), cdr(d_sym)))
}

///|
/// Calcul des fonctions puissances pour des partitions de longueur 2
/// m(i)! * \sum x^i y^j = \sum x^i \sum x^j - \sum x^{i+j}
///              = p_i*p_j - p_{i+j}
/// ici la multiplicite m(i) de i dans \sum x^i y^j est de 1 ou 2
fn longde2(sym_ : Value, lg2 : Value) -> Value raise {
  let mut sym_ = sym_
  let mut lg2 = lg2
  while true {
    if sym_ is Nil || eql(int(1), lgi(sym_)) {
      return share_sym__add(lg2, p__ecrit(sym_))
    }
    let partin = moni(sym_)
    let listpi = symval(q_listpi)
    let v = if length(partin) == 4 {
      let i = car(partin)
      let j = caddr(partin)
      share_sym__add(
        share_sym__moins(nth(to_int(num_add(i, j)), listpi)),
        share_sym__mult(nth(to_int(j), listpi), nth(to_int(i), listpi)),
      )
    } else {
      share_sym__divi(
        share_sym__add(
          share_sym__moins(nth(to_int(num_mul(int(2), car(partin))), listpi)),
          share_sym__exp(nth(to_int(car(partin)), listpi), int(2)),
        ),
        int(2),
      )
    }
    lg2 = share_sym__add(lg2, share_sym__mult(coei(sym_), v))
    sym_ = cdr(sym_)
  }
  Nil
}

///|
/// REECRITURE D'UNE FORME MONOMIALE EN FONCTION DE FORMES MONOMIALES
/// INFERIEURES POUR L'ORDRE DES LONGUEURS; CAS r=1 (cf. article)
fn p__reducpart(part : Value, coe : Value, lg : Value) -> Value raise {
  let puim = car(part)
  let m = cadr(part)
  let mm = num_mul(int(-1), m)
  let coef = nth(to_int(puim), symval(q_listpi))
  let partf = p__fact(part, m)
  let prsol = mapc(
    p => share_sym__attach(share_sym__divi(coe, mm), p) |> ignore,
    multpui(partf, puim),
  )
  mapc(
    tpart => share_sym__attach(one_minus(lg), tpart) |> ignore,
    constsol(coef, m, coe, partf, prsol),
  )
}

///|
/// si la puim-ieme fonction puissance est non nulle on rajoute partf
/// aux nouvelles partitions a decomposer.
fn constsol(
  coef : Value,
  m : Value,
  coe : Value,
  partf : Value,
  prsol : Value,
) -> Value raise {
  if numberp(coef) && zerop(coef) {
    prsol
  } else {
    nconc(
      prsol,
      list1(cons(share_sym__divi(share_sym__mult(coef, coe), m), partf)),
    )
  }
}

///|
/// On va eventuellement modifier physiquement part
fn p__fact(part : Value, m : Value) -> Value raise {
  if eql(int(1), m) {
    cddr(part)
  } else {
    rplaca(cdr(part), one_minus(m)) |> ignore
    part
  }
}

///|
/// PRODUIT D'UNE FORME MONOMIALE parf PAR LA FONCTION PUISSANCE DE POIDS
/// puim. partf a pour representation [partition](2)
fn multpui(partf : Value, puim : Value) -> Value raise {
  let k = cons(Nil, Nil)
  multpui2(partf, puim, Nil, k) |> ignore
  cdr(k)
}

///|
/// les partitions sont rangees dans l'ordre lexicographique decroissant
/// dans k. nconc impossible ici
fn multpui2(part : Value, puim : Value, s : Value, k : Value) -> Value raise {
  let mut part = part
  let mut s = s
  let mut k = k
  while part is Cons(_) {
    let pui = car(part)
    let nb = cadr(part)
    let rpart = cddr(part)
    let ns = append(s, list2(pui, nb))
    let nk = cdr(
      rplacd(
        k,
        list1(
          list_star([
            num_add(pui, puim),
            int(1),
            nconc(s, restpart(pui, one_minus(nb), rpart)),
          ]),
        ),
      ),
    )
    part = rpart
    s = ns
    k = nk
  }
  t
}

///|
fn restpart(pui : Value, nb : Value, part : Value) -> Value raise {
  if eql(int(0), nb) {
    part
  } else {
    cons(pui, cons(nb, part))
  }
}

// L'ECRIVAIN

///|
fn p__ecrit(solu : Value) -> Value raise {
  let solu = nreverse(solu)
  if solu is Nil {
    int(0)
  } else if eql(int(0), lgi(solu)) {
    p__ecrit2(cdr(solu), cdr(symval(q_listpi)), coei(solu), int(1))
  } else {
    p__ecrit2(solu, cdr(symval(q_listpi)), int(0), int(1))
  }
}

///|
fn p__ecrit2(
  solu : Value,
  listpi : Value,
  mpol : Value,
  i_init : Value,
) -> Value raise {
  let mut solu = solu
  let mut listpi = listpi
  let mut mpol = mpol
  let mut i_init = i_init
  while true {
    let i = car(moni(solu))
    if solu is Nil {
      return mpol
    }
    if eql(i, i_init) {
      mpol = share_sym__add(mpol, share_sym__mult(coei(solu), car(listpi)))
    } else {
      listpi = share_sym__nthcdr(num_sub(i, i_init), listpi)
      mpol = share_sym__add(mpol, share_sym__mult(coei(solu), car(listpi)))
      i_init = i
    }
    solu = cdr(solu)
  }
  Nil
}

///|
fn init_share_pui() -> Unit raise {
  share_sym__defmexpr(
    q_d_pui,
    "((lambda ()) ((mlist) $valpi $sym $lvar) ((mprog) (($operation)) (($pui_init) $valpi $sym $lvar)))",
    item_text="(($pui) $valpi $sym $lvar)",
  )
  share_sym__defmexpr(
    q_d_multi_pui,
    "((lambda ()) ((mlist) $lvalpi $pc $llvar) ((mprog) (($operation)) (($multi_pui_init) $lvalpi $pc $llvar)))",
    item_text="(($multi_pui) $lvalpi $pc $llvar)",
  )
}
