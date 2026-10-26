// Port of share/sym/chbase.lisp: changes of bases between elementary,
// power and complete symmetric functions (PUI2COMP, PUI2ELE, ELE2PUI,
// ELE2COMP, COMP2PUI, COMP2ELE).
// card le cardinal de l'alphabet; lpui=(card p1 ....);
// lelem=(card e1 ...) et on a e1=p1=h1; lcomp = (card h1 ...)

///|
fn share_sym_chbase__mlist(l : Value) -> Value {
  cons(list1(q_mlist), l)
}

///|
/// `(make-list n :initial-element elt)`
fn share_sym__make_list(n : Value, elt : Value) -> Value raise {
  let c = Collector::new()
  let k = to_int(n)
  for _ in 0..<k {
    c.add(elt)
  }
  c.result()
}

// A PARTIR DES ELEMENTAIRES: OBTENIR LES PREMIERES FONCTIONS PUISSANCES

///|
/// on cherche de 0 a max; $lelem=((mlist) card e1 e2....)
fn d_ele2pui0(max_ : Value, d_lelem : Value) -> Value raise {
  share_sym_chbase__mlist(ele2pui_init(max_, cdr(d_lelem)))
}

///|
/// si il n'y a rien a changer avec card numerique
fn ele2pui(max_ : Value, lelem : Value) -> Value raise {
  d_e_calbasepui(car(lelem), int(2), max_, list2(cadr(lelem), car(lelem)), lelem)
}

///|
fn ele2pui_init(max_ : Value, lelem : Value) -> Value raise {
  let lelem = d_debut(q_d_e, lelem, max_)
  let l = int(length(lelem))
  let card = car(lelem)
  d_e_calbasepui(
    card,
    int(2),
    max_,
    list2(cadr(lelem), card),
    if num_lt(l, one_plus(max_)) {
      nreverse(d_complbase(q_d_e, reverse(lelem), l, one_plus(max_)))
    } else {
      lelem
    },
  )
}

///|
fn d_puireduc_init(max_ : Value, d_lpui : Value) -> Value raise {
  share_sym_chbase__mlist(puireduc_init(max_, cdr(d_lpui)))
}

///|
/// lpui=(card p1 .... p(l-1))
fn puireduc_init(max_ : Value, lpui : Value) -> Value raise {
  let card = car(lpui)
  let l = int(length(lpui))
  if num_lt(max_, l) {
    lpui
  } else if !numberp(card) || !num_lt(card, max_) {
    rangpi2(max_, lpui, l)
  } else if num_lt(card, l) {
    d_e_calbasepui(card, l, max_, reverse(lpui), pui2ele(card, lpui, q_d_girard))
  } else {
    let lpui = rangpi2(card, lpui, l)
    d_e_calbasepui(
      card,
      one_plus(card),
      max_,
      reverse(lpui),
      pui2ele(card, lpui, q_d_girard),
    )
  }
}

///|
/// listpi =(p0,...,pm) et lg = m+1
fn rangpi2(n : Value, listpi : Value, lg : Value) -> Value raise {
  if num_lt(n, lg) {
    listpi
  } else {
    append(listpi, rangpi3(n, lg, Nil))
  }
}

///|
fn rangpi3(n : Value, i : Value, flistpi : Value) -> Value raise {
  let mut i = i
  let mut flistpi = flistpi
  while !num_lt(n, i) {
    flistpi = cons(share_sym__concat([q_d_p, i]), flistpi)
    i = one_plus(i)
  }
  nreverse(flistpi)
}

///|
fn d_puireduc0(
  min_ : Value,
  max_ : Value,
  d_lpui : Value,
  d_lelem : Value,
) -> Value raise {
  share_sym_chbase__mlist(puireduc(min_, max_, cdr(d_lpui), cdr(d_lelem)))
}

///|
fn puireduc(min_ : Value, max_ : Value, lpui : Value, lelem : Value) -> Value raise {
  d_pm_ei2(min_, max_, lpui, d_debut(q_d_e, lelem, max_))
}

///|
fn d_pm_ei2(min_ : Value, max_ : Value, lpui : Value, lelem : Value) -> Value raise {
  let card = car(lelem)
  let l1 = length(lpui)
  let args = if l1 == 0 || l1 == 1 {
    d_pe_rallonge(int(2), min_, max_, list2(car(lelem), cadr(lelem)), lelem)
  } else {
    d_pe_rallonge(int(l1), min_, max_, lpui, lelem)
  }
  share_sym__nthcdr(
    min_,
    d_e_calbasepui(card, car(args), cadr(args), caddr(args), cadddr(args)),
  )
}

// pm = (-1)^{m+1}e_m + somme (-1)^{i+1} e_i p_{m-i} pour i=1 a m-1
// lelem = (e0 e1 ...) rlpui=(e1 e0)
// m>=2 les plus grands pm sont devant

///|
fn d_e_calbasepui(
  card : Value,
  min_ : Value,
  max_ : Value,
  rlpui : Value,
  lelem : Value,
) -> Value raise {
  let lelem = chsigne(lelem)
  let rlpui = rlpui
  let mut m = min_
  while !num_lt(max_, m) {
    share_sym__attach(
      d_e_calpui(
        card,
        rlpui,
        lelem,
        if num_lt(card, m) {
          int(0)
        } else {
          share_sym__mult(m, nth(to_int(m), lelem))
        },
      ),
      rlpui,
    )
    |> ignore
    m = one_plus(m)
  }
  nreverse(rlpui)
}

///|
/// Calcul de la m-ieme fonction puissance
fn d_e_calpui(card : Value, rlpui : Value, lelem : Value, pn : Value) -> Value raise {
  let mut j = int(1)
  let mut base = cdr(lelem)
  let mut rbase = rlpui
  let mut pn = pn
  while !(num_lt(card, j) || cdr(rbase) is Nil) {
    pn = share_sym__add(pn, share_sym__mult(car(base), car(rbase)))
    j = one_plus(j)
    base = cdr(base)
    rbase = cdr(rbase)
  }
  pn
}

///|
/// il manque des ei de i=l2 a max
fn d_pe_rallonge(
  l1 : Value,
  min_ : Value,
  max_ : Value,
  list1 : Value,
  list2 : Value,
) -> Value raise {
  let l2 = int(length(list2))
  list4(
    num_max(min_, l1),
    max_,
    if num_lt(l1, min_) {
      // il manque les pi de i=l1 a min-1
      d_complbase(q_d_p, reverse(list1), l1, min_)
    } else {
      reverse(list1)
    },
    if num_lt(l2, max_) || eql(l2, max_) {
      // il manque des ei de i=l2 a max
      nreverse(d_complbase(q_d_e, reverse(list2), l2, one_plus(max_)))
    } else {
      list2
    },
  )
}

// OBTENIR LES PREMIERES FONCTIONS COMPLETES
// p.14 du Macdonald : h_0 = e_0 = 1
// somme des (-1)^r e_r * h_{n-r} = 0 pour tout n >= 1

///|
fn d_ele2comp_init(max_ : Value, d_lelem : Value) -> Value raise {
  share_sym_chbase__mlist(ele2comp_init(max_, cdr(d_lelem)))
}

///|
fn ele2comp_init(max_ : Value, lelem : Value) -> Value raise {
  let lelem = d_debut(q_d_e, lelem, max_)
  let l = int(length(lelem))
  ele2comp(
    max_,
    if num_lt(l, one_plus(max_)) {
      nreverse(d_complbase(q_d_e, reverse(lelem), l, one_plus(max_)))
    } else {
      lelem
    },
  )
}

///|
/// si il n'y a rien a completer dans lelem
fn ele2comp(max_ : Value, lelem : Value) -> Value raise {
  e_calbasecomp(car(lelem), int(2), max_, list2(cadr(lelem), car(lelem)), lelem)
}

///|
/// on utilise la meme fonction pour le passage des elementaires aux
/// puissances : e_calpui. m>=2 les plus grands pm sont devant
fn e_calbasecomp(
  card : Value,
  min_ : Value,
  max_ : Value,
  rbarrivee : Value,
  badepart : Value,
) -> Value raise {
  let badepart = chsigne(badepart)
  let mut m = min_
  while !num_lt(max_, m) {
    share_sym__attach(
      d_e_calpui(
        card,
        rbarrivee,
        badepart,
        if num_lt(card, m) {
          int(0)
        } else {
          nth(to_int(m), badepart)
        },
      ),
      rbarrivee,
    )
    |> ignore
    m = one_plus(m)
  }
  nreverse(rbarrivee)
}

// A PARTIR DES FONCTIONS PUISSANCES:
// OBTENIR LES PREMIERES FONCTIONS SYMETRIQUES ELEMENTAIRES
// Si on ne cherche qu'une seule fonction symetrique elementaire
// on utilise une formule close. Cela sera specifie par un drapeau
// pour pui2ele . Il sera avec Girard ou close.

///|
/// on cherche de 0 a max
fn d_pui2ele0(max_ : Value, d_lpui : Value) -> Value raise {
  if equal(q_d_girard, symval(q_d_pui2ele)) {
    share_sym_chbase__mlist(pui2ele_init(max_, cdr(d_lpui)))
  } else {
    pui2ele_init(max_, cdr(d_lpui))
  }
}

///|
/// si il y a a rajouter
fn pui2ele_init(max_ : Value, lpui : Value) -> Value raise {
  let lpui = d_debut(q_d_p, lpui, max_)
  let l = int(length(lpui))
  pui2ele(
    max_,
    if num_lt(l, one_plus(max_)) {
      nreverse(d_complbase(q_d_p, reverse(lpui), l, one_plus(max_)))
    } else {
      lpui
    },
    symval(q_d_pui2ele),
  )
}

///|
/// si il n'y a rien a rajouter dans la liste des fonctions puissances.
fn pui2ele(max_ : Value, lpui : Value, d_pui2ele : Value) -> Value raise {
  if equal(q_d_girard, d_pui2ele) {
    girard_pui2ele(max_, lpui)
  } else if num_lt(car(lpui), max_) {
    int(0)
  } else {
    macdonald_pui2ele(max_, cdr(lpui))
  }
}

// AVEC LA FORMULE CLOSE

///|
fn macdonald_pui2ele(n : Value, lpui : Value) -> Value raise {
  with_special(q_en, int(0), () => {
    macdonald2(n, int(0), list2(cons(n, reverse(lpui)), expt(int(-1), n)))
    |> ignore
    symval(q_en)
  })
}

///|
fn macdonald2(exposant : Value, ote : Value, poule : Value) -> Value raise {
  if eql(int(0), exposant) {
    // on a une partition de poids n
    set(q_en, share_sym__add(symval(q_en), termine(poule)))
  } else {
    macdonald2(
      ote,
      num_max(int(0), num_sub(num_mul(int(2), ote), exposant)),
      chbase_met(exposant, ote, poule),
    )
    |> ignore
    let ote = one_plus(ote)
    if num_lt(ote, exposant) {
      macdonald2(exposant, ote, poule)
    } else {
      Nil
    }
  }
}

///|
/// termine ramene epsilon_I*z_I*p_I avec |I|=n
fn termine(poule : Value) -> Value raise {
  let aj1 = cadddr(poule)
  let mj1 = caddr(poule)
  let rlpui = car(poule)
  let puiaj1 = nth(to_int(num_sub(car(rlpui), aj1)), cdr(rlpui))
  share_sym__divi(
    share_sym__mult(share_sym__exp(puiaj1, mj1), car(last(poule))),
    num_mul(num_mul(cadr(poule), expt(aj1, mj1)), factorielle(mj1)),
  )
}

///|
/// chbase-met construit au fur et a mesure epsilon_I*z_I et p_I pour |I|
/// strictement inferieure a n.
/// au depart poule = ( (n  pn ... p1) (-1)^n)
/// poule = (rlpui epsilon_I*z_I*(-1)^{mj+1} mj+1 aj+1 p_I)
/// ou I = (a1 m1 ... aj mj) = [partition](2) avec n >= a1
/// et rlpui = (aj paj pa(j-1) ... p2 p1)
fn chbase_met(exposant : Value, ote : Value, poule : Value) -> Value raise {
  if cddr(poule) is Nil {
    list([
      car(poule),
      num_mul(cadr(poule), int(-1)),
      int(1),
      num_sub(exposant, ote),
      int(1),
    ])
  } else {
    let ak = num_sub(exposant, ote) // nouvelle part obtenue
    let aj1 = nth(3, poule) // part courante
    let rlpui = car(poule)
    // on change la signature a chaque nouvelle part obtenue
    let coe = num_mul(int(-1), cadr(poule))
    if eql(ak, aj1) {
      cons(rlpui, cons(coe, cons(one_plus(caddr(poule)), cdddr(poule))))
    } else {
      // on doit calculer epsilon_J et z_J ou J= aj+1^{mj+1} U I
      // et p_J = paj+1^{mj+1}*p_I :
      let nxrlpui = share_sym__nthcdr(num_sub(car(rlpui), aj1), cdr(rlpui))
      let mj1 = nth(2, poule)
      list([
        cons(aj1, nxrlpui),
        num_mul(num_mul(coe, expt(aj1, mj1)), factorielle(mj1)),
        int(1),
        ak,
        share_sym__mult(share_sym__exp(car(nxrlpui), mj1), car(last(poule))),
      ])
    }
  }
}

// AVEC LA FORMULE DE GIRARD

///|
fn girard_pui2ele(max_ : Value, lpui : Value) -> Value raise {
  let card = car(lpui)
  let rlelem = list2(cadr(lpui), car(lpui))
  if num_lt(card, max_) {
    // forcement numerique (cf $debut)
    nconc(
      d_p_calbaselem(int(2), card, rlelem, lpui),
      share_sym__make_list(num_sub(max_, card), int(0)),
    )
  } else {
    d_p_calbaselem(int(2), max_, rlelem, lpui)
  }
}

///|
fn d_elereduc0(min_ : Value, max_ : Value, lelem : Value, lpui : Value) -> Value raise {
  share_sym_chbase__mlist(elereduc(min_, max_, cdr(lelem), cdr(lpui)))
}

///|
fn elereduc(min_ : Value, max_ : Value, lelem : Value, lpui : Value) -> Value raise {
  d_troncelem(min_, max_, lelem, d_debut(q_d_p, lpui, max_))
}

///|
fn d_troncelem(min_ : Value, max_ : Value, lelem : Value, lpui : Value) -> Value raise {
  let card = car(lpui)
  if num_lt(card, max_) {
    if num_lt(card, min_) {
      nconc(
        lelem,
        share_sym__make_list(one_plus(num_sub(max_, min_)), int(0)),
      )
    } else {
      nconc(
        d_p_baselem(min_, card, lelem, lpui),
        share_sym__make_list(num_sub(max_, card), int(0)),
      )
    }
  } else {
    d_p_baselem(min_, max_, cons(car(lpui), cdr(lelem)), lpui)
  }
}

///|
fn d_p_baselem(min_ : Value, max_ : Value, lelem : Value, lpui : Value) -> Value raise {
  let l1 = length(lelem)
  let args = if l1 == 0 || l1 == 1 {
    d_ep_rallonge(int(2), min_, max_, list2(car(lpui), cadr(lpui)), lpui)
  } else {
    d_ep_rallonge(int(l1), min_, max_, lelem, lpui)
  }
  share_sym__nthcdr(
    min_,
    d_p_calbaselem(car(args), cadr(args), caddr(args), cadddr(args)),
  )
}

///|
/// m>=2
fn d_p_calbaselem(
  min_ : Value,
  max_ : Value,
  rlelem : Value,
  lpui : Value,
) -> Value raise {
  let lpui = chsigne(lpui)
  let mut m = min_
  while !num_lt(max_, m) {
    share_sym__attach(
      share_sym__divi(d_p_calelem(rlelem, lpui, nth(to_int(m), lpui)), m),
      rlelem,
    )
    |> ignore
    m = one_plus(m)
  }
  nreverse(rlelem)
}

///|
fn d_p_calelem(rlelem : Value, lpui : Value, en : Value) -> Value raise {
  let mut base = cdr(lpui)
  let mut rbase = rlelem
  let mut en = en
  while cdr(rbase) is Cons(_) {
    en = share_sym__add(en, share_sym__mult(car(base), car(rbase)))
    base = cdr(base)
    rbase = cdr(rbase)
  }
  en
}

///|
/// il manque des ei de i=l2 a max
fn d_ep_rallonge(
  l1 : Value,
  min_ : Value,
  max_ : Value,
  list1 : Value,
  list2 : Value,
) -> Value raise {
  let l2 = int(length(list2))
  list4(
    num_max(min_, l1),
    max_,
    if num_lt(l1, min_) {
      // il manque les pi de i=l1 a min-1
      d_complbase(q_d_e, reverse(list1), l1, min_)
    } else {
      reverse(list1)
    },
    if num_lt(l2, max_) || eql(l2, max_) {
      // il manque des ei de i=l2 a max
      nreverse(d_complbase(q_d_p, reverse(list2), l2, one_plus(max_)))
    } else {
      list2
    },
  )
}

// OBTENIR LES PREMIERES FONCTIONS COMPLETES
// p.16 du Macdonald : h_0 = e_0 = 1  ,
// n*h_n = somme des  p_r * h_{n-r} pour tout r = 1 a n

///|
fn d_pui2comp_init(max_ : Value, d_lpui : Value) -> Value raise {
  share_sym_chbase__mlist(pui2comp_init(max_, cdr(d_lpui)))
}

///|
fn pui2comp_init(max_ : Value, lpui : Value) -> Value raise {
  let lpui = d_debut(q_d_p, lpui, max_)
  let l = int(length(lpui))
  pui2comp(
    max_,
    if num_lt(l, one_plus(max_)) {
      nreverse(d_complbase(q_d_p, reverse(lpui), l, one_plus(max_)))
    } else {
      lpui
    },
  )
}

///|
/// si il n'y a rien a completer dans lpui
fn pui2comp(max_ : Value, lpui : Value) -> Value raise {
  p__calbasecomp(car(lpui), int(2), max_, list2(cadr(lpui), car(lpui)), lpui)
}

///|
/// on utilise la meme fonction pour le passage des puissances aux
/// elementaires : p_calelem. m>=2 les plus grands pm sont devant
fn p__calbasecomp(
  card : Value,
  min_ : Value,
  max_ : Value,
  rlcomp : Value,
  lpui : Value,
) -> Value raise {
  ignore(card)
  let mut m = min_
  while !num_lt(max_, m) {
    share_sym__attach(
      share_sym__divi(d_p_calelem(rlcomp, lpui, nth(to_int(m), lpui)), m),
      rlcomp,
    )
    |> ignore
    m = one_plus(m)
  }
  nreverse(rlcomp)
}

// A PARTIR DES FONCTIONS SYMETRIQUES COMPLETES

///|
fn d_comp2ele_init(max_ : Value, d_lcomp : Value) -> Value raise {
  share_sym_chbase__mlist(comp2ele_init(max_, cdr(d_lcomp)))
}

///|
fn comp2ele_init(max_ : Value, lcomp : Value) -> Value raise {
  let lcomp = d_debut(q_d_h, lcomp, max_)
  let l = int(length(lcomp))
  comp2ele(
    max_,
    if num_lt(l, one_plus(max_)) {
      nreverse(d_complbase(q_d_h, reverse(lcomp), l, one_plus(max_)))
    } else {
      lcomp
    },
  )
}

///|
fn comp2ele(max_ : Value, lcomp : Value) -> Value raise {
  let card = car(lcomp)
  let rlelem = list2(cadr(lcomp), car(lcomp))
  if num_lt(card, max_) {
    // forcement numerique (cf $debut)
    nconc(
      c_calbaselem(int(2), card, rlelem, lcomp),
      share_sym__make_list(num_sub(max_, card), int(0)),
    )
  } else {
    c_calbaselem(int(2), max_, rlelem, lcomp)
  }
}

///|
/// On utilise la fonction $p_calelem du passage des elementaires
/// aux puissances. m>=2
fn c_calbaselem(
  min_ : Value,
  max_ : Value,
  rlelem : Value,
  lcomp : Value,
) -> Value raise {
  let lcomp = chsigne(lcomp)
  let mut m = min_
  while !num_lt(max_, m) {
    share_sym__attach(d_p_calelem(rlelem, lcomp, nth(to_int(m), lcomp)), rlelem)
    |> ignore
    m = one_plus(m)
  }
  nreverse(rlelem)
}

// OBTENIR LES PREMIERES FONCTIONS PUISSANCES

///|
fn d_comp2pui_init(max_ : Value, d_lcomp : Value) -> Value raise {
  share_sym_chbase__mlist(comp2pui_init(max_, cdr(d_lcomp)))
}

///|
fn comp2pui_init(max_ : Value, lcomp : Value) -> Value raise {
  let lcomp = d_debut(q_d_h, lcomp, max_)
  let l = int(length(lcomp))
  comp2pui(
    max_,
    if num_lt(l, one_plus(max_)) {
      nreverse(d_complbase(q_d_h, reverse(lcomp), l, one_plus(max_)))
    } else {
      lcomp
    },
  )
}

///|
fn comp2pui(max_ : Value, lcomp : Value) -> Value raise {
  let rlpui = list2(cadr(lcomp), car(lcomp))
  c_calbasepui(int(2), max_, rlpui, lcomp)
}

///|
/// On utilise la fonction $p_calelem du passage des puissances
/// aux elementaires. m>=2
fn c_calbasepui(
  min_ : Value,
  max_ : Value,
  rlpui : Value,
  lcomp : Value,
) -> Value raise {
  let mrlpui = mapcar(x => share_sym__moins(x), rlpui)
  let mut m = min_
  while !num_lt(max_, m) {
    share_sym__attach(
      share_sym__moins(
        d_p_calelem(mrlpui, lcomp, share_sym__mult(m, nth(to_int(m), lcomp))),
      ),
      mrlpui,
    )
    |> ignore
    m = one_plus(m)
  }
  nreverse(mapcar(x => share_sym__moins(x), mrlpui))
}

// Fonctions en commun
// tenir compte du cardinal de l'alphabet lorsque l'on doit completer
// sur les elementaires on ne completera que jusqu'a ce cardinal.

///|
fn d_complbase(base : Value, rlist : Value, i : Value, sup : Value) -> Value raise {
  let card = car(last(rlist))
  if equal(q_d_e, base) && num_lt(card, one_minus(sup)) {
    // forcement numerique
    d_complbase2(base, rlist, i, one_plus(card))
  } else {
    d_complbase2(base, rlist, i, sup)
  }
}

///|
fn d_complbase2(base : Value, rlist : Value, i : Value, sup : Value) -> Value raise {
  if eql(i, sup) {
    rlist
  } else {
    d_complbase(base, cons(share_sym__concat([base, i]), rlist), one_plus(i), sup)
  }
}

///|
fn d_debut(base : Value, list_ : Value, max_ : Value) -> Value raise {
  let card = if numberp(car(list_)) { car(list_) } else { max_ }
  if list_ is Nil || cdr(list_) is Nil {
    list2(card, share_sym__concat([base, int(1)]))
  } else {
    cons(card, cdr(list_))
  }
}

///|
fn chsigne(liste : Value) -> Value raise {
  let mut flag = true
  mapcar(
    b => {
      flag = !flag
      if flag {
        b
      } else {
        share_sym__mult(int(-1), b)
      }
    },
    liste,
  )
}

///|
fn init_share_chbase() -> Unit raise {
  share_sym__defmexpr(
    q_d_ele2pui,
    "((lambda ()) ((mlist) $max $listei) ((mprog) (($operation)) (($ele2pui0) $max $listei)))",
    item_text="(($ele2pui) $max $listei)",
  )
  share_sym__defmexpr(
    q_d_ele2comp,
    "((lambda ()) ((mlist) $max $listei) ((mprog) (($operation)) (($ele2comp_init) $max $listei)))",
    item_text="(($ele2comp) $max $listei)",
  )
  share_sym__defmexpr(
    q_d_puireduc,
    "((lambda ()) ((mlist) $max $listpi) ((mprog) (($operation)) (($puireduc_init) $max $listpi)))",
    item_text="(($puireduc) $max $listpi)",
  )
  share_sym__defmexpr(
    q_d_pui2ele,
    "((lambda ()) ((mlist) $max $listpi) ((mprog) (($operation)) (($pui2ele0) $max $listpi)))",
    item_text="(($pui2ele) $max $listpi)",
  )
  share_sym__defmexpr(
    q_d_pui2comp,
    "((lambda ()) ((mlist) $max $listpi) ((mprog) (($operation)) (($pui2comp_init) $max $listpi)))",
    item_text="(($pui2comp) $max $listpi)",
  )
  share_sym__defmexpr(
    q_d_elereduc,
    "((lambda ()) ((mlist) $min $max $listei $listpi) ((mprog) (($operation)) (($elereduc0) $min $max $listei $listpi)))",
  )
  share_sym__defmexpr(
    q_d_comp2ele,
    "((lambda ()) ((mlist) $max $listhi) ((mprog) (($operation)) (($comp2ele_init) $max $listhi)))",
    item_text="(($comp2ele) $max $listhi)",
  )
  share_sym__defmexpr(
    q_d_comp2pui,
    "((lambda ()) ((mlist) $max $listhi) ((mprog) (($operation)) (($comp2pui_init) $max $listhi)))",
    item_text="(($comp2pui) $max $listhi)",
  )
}
