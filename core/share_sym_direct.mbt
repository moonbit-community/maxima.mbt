// Port of share/sym/direct.lisp: CALCULS D'IMAGES DIRECTES, D'ORBITES ...
// DANS LE CAS LE PLUS GENERAL.
// Specials: $direct, $pui, $elem, sauvedrapeau.

// Orbite d'un polynome dans k[y1,...,yn] sous S_n
// On fait permuter ses variables et on l'applique a chacune
// de ces permutations. Puis on elimine les egaux au fur et a mesure

///|
fn d_orbit_init(d_p : Value, d_lvar : Value) -> Value raise {
  cons(list1(q_mlist), orbit(d_p, d_lvar))
}

///|
fn orbit(d_p : Value, d_lvar : Value) -> Value raise {
  let p_dist = lect(d_p, d_lvar)
  let list_dolpol = list1(d_p)
  orbit2(list_dolpol, p_dist, cdr(d_lvar), Nil) |> ignore
  list_dolpol
}

///|
/// les permutations circulaires ne changeraient rien
fn orbit2(
  list_dolpol : Value,
  p__dist : Value,
  f_lvar : Value,
  d__lvar : Value,
) -> Value raise {
  if cdr(f_lvar) is Nil {
    return Nil
  }
  mapc(
    f_lvar2 => {
      let pol = ecrit_pol(p__dist, append(d__lvar, f_lvar2))
      if !contient(list_dolpol, pol).truthy() {
        share_sym__attach(pol, list_dolpol) |> ignore
      }
      orbit2(
        list_dolpol,
        p__dist,
        cdr(f_lvar2),
        append(d__lvar, list1(car(f_lvar2))),
      )
      |> ignore
    },
    permut_circu(cdr(f_lvar), list1(car(f_lvar))),
  )
  |> ignore
  orbit2(list_dolpol, p__dist, cdr(f_lvar), append(d__lvar, list1(car(f_lvar))))
}

///|
/// on ne ramene pas l'identite
fn permut_circu(debut : Value, fin : Value) -> Value raise {
  if cdr(debut) is Nil {
    list1(cons(car(debut), fin))
  } else {
    cons(append(debut, fin), permut_circu(cdr(debut), cons(car(debut), fin)))
  }
}

///|
fn contient(list_dolpol : Value, d_pol : Value) -> Value raise {
  for pol2 in list_dolpol.iter() {
    if share_sym__is_equal(d_pol, pol2) {
      return t
    }
  }
  Nil
}

// CALCUL DE L'ORBITE DU POLYNOME P SOUS S_d1xS_d2x...xS_dp

///|
fn d_multi_orbit_init(d_p : Value, d_llvar : Value) -> Value raise {
  cons(list1(q_mlist), multi_orbit_init(d_p, cdr(d_llvar)))
}

///|
/// sous S_0
fn multi_orbit_init(d_p : Value, llvar : Value) -> Value raise {
  if llvar is Nil {
    list1(d_p)
  } else {
    multi_orbit(orbit(d_p, car(llvar)), Nil, cdr(llvar))
  }
}

///|
/// On se deplace en largeur dans l'arbre ie. on fait agir tout S_i avant
/// de passer a S_(i+1). On calcul l'orbite du polynome P sous
/// S_1 x ... x S_i et on en deduit son orbite sous S_1 x ... x S_(i+1).
fn multi_orbit(lpoli : Value, lpoli_plus1 : Value, llvar : Value) -> Value raise {
  let mut lpoli = lpoli
  let mut lpoli_plus1 = lpoli_plus1
  let mut llvar = llvar
  while true {
    if lpoli is Nil {
      if cdr(llvar) is Nil {
        return lpoli_plus1
      }
      lpoli = lpoli_plus1
      lpoli_plus1 = Nil
      llvar = cdr(llvar)
    } else {
      let orb = orbit(car(lpoli), car(llvar))
      epure(lpoli, cons(Nil, copy_tree(orb))) |> ignore
      lpoli = cdr(lpoli)
      lpoli_plus1 = nconc(orb, lpoli_plus1)
    }
  }
  Nil
}

///|
/// Que fait epure? He bien il enleve physiquement de (cdr l1) tout
/// les polynomes se trouvant eventuellement dans (cdr l2) en les diminuant
/// toutes deux physiquement.
fn epure(l1 : Value, l2 : Value) -> Value raise {
  let mut l1 = l1
  while cdr(l1) is Cons(_) {
    if catch_tag(q_trouve, () => dans(l2, cadr(l1))).truthy() {
      // on l'a retire de l2 (ne reviendra pas)
      l1 = rplacd(l1, cddr(l1)) // allez! oust!
    } else {
      l1 = cdr(l1)
    }
  }
  Nil
}

///|
/// on regarde si l'oppose de $-pol est dans l2
/// si oui on le retire de l2 et on repond : t sinon : nil
fn dans(l2 : Value, d_pol : Value) -> Value raise {
  let mut l2 = l2
  while cdr(l2) is Cons(_) {
    if share_sym__is_equal(cadr(l2), d_pol) {
      // on en profite pour le retirer de l2
      rplacd(l2, cddr(l2)) |> ignore
      return throw_tag(q_trouve, t)
    }
    l2 = cdr(l2)
  }
  Nil
}

// CALCUL DES FONCTIONS PUISSANCES SOUS FORME CONTRACTE SOUS
// S_d1 x ... x S_dp = S_D
// 1_ l'appel et la boucle principale; on retire le degre en tete

///|
fn d_pui_direct_init(d_or : Value, d_llvar : Value, d_ldegre : Value) -> Value raise {
  cons(
    list1(q_mlist),
    cdr(
      pui_direct(
        cdr(d_or),
        mapcar(x => cdr(x), cdr(d_llvar)),
        cdr(d_ldegre),
      ),
    ),
  )
}

///|
/// ldegre_arite = ((degre arite) ...) and the degree of P_*(P1,...,Pp)
fn share_sym_direct__degre_resol(
  n : Int,
  ldegre : Value,
  llvar : Value,
) -> (Value, Value) raise {
  let ldegre_arite = mapcar2(
    (d, lv) => list2(d, int(length(lv))),
    ldegre,
    llvar,
  )
  let mut prod = int(1)
  for nb in ldegre_arite.iter() {
    prod = num_mul(prod, binomial(car(nb), cadr(nb)))
  }
  (ldegre_arite, num_mul(int(n), prod))
}

///|
fn pui_direct(or : Value, llvar : Value, ldegre : Value) -> Value raise {
  let (ldegre_arite, degre_resol) = share_sym_direct__degre_resol(
    length(or),
    ldegre,
    llvar,
  )
  print(degre_resol) |> ignore
  let mut o = one_minus(degre_resol)
  let mut listpui = list1(
    pui_contract(int(0), or, llvar, degre_resol, ldegre_arite),
  )
  while !eql(int(0), o) {
    print(o) |> ignore
    let no = one_minus(o)
    listpui = cons(pui_contract(int(0), or, llvar, o, ldegre_arite), listpui)
    o = no
  }
  cons(degre_resol, listpui)
}

///|
/// 2_ Obtention de la rieme fonction puissance; dans Or on a des polynomes
/// macsyma; on ne conserve que les monomes dont les exposants correspondent
/// a des multipartitions. Ramene un polynome macsyma
fn pui_contract(
  d_pui_cont : Value,
  or : Value,
  llvar : Value,
  r : Value,
  ldegre_arite : Value,
) -> Value raise {
  let mut acc = d_pui_cont
  let mut or = or
  while or is Cons(_) {
    acc = share_sym__add(
      multi_partitions(share_sym__exp(car(or), r), llvar, ldegre_arite),
      acc,
    )
    or = cdr(or)
  }
  acc
}

///|
/// on jette les momones a exposants non multi_partitionne dans $pol.
fn multi_partitions(
  d_pol : Value,
  llvar : Value,
  ldegre_arite : Value,
) -> Value raise {
  let mut rllvar = cdr(reverse(llvar))
  let mut rldegre_arite = cdr(reverse(ldegre_arite))
  let mut pol_multipartitionne = garde_que_partition_init(
    cons(Nil, lect(d_pol, cons(list1(q_mlist), car(last(llvar))))),
    car(last(ldegre_arite)),
  )
  while rllvar is Cons(_) {
    let lv = car(rllvar)
    let da = car(rldegre_arite)
    let mut p_m = pol_multipartitionne
    while p_m is Cons(_) {
      rplaca(
        p_m,
        distribu(
          cdar(p_m),
          garde_que_partition(
            cons(Nil, lect(caar(p_m), cons(list1(q_mlist), lv))),
            da,
          ),
        ),
      )
      |> ignore
      p_m = cdr(p_m)
    }
    let mut r : Value = Nil
    for x in reverse(pol_multipartitionne).iter() {
      r = nconc(x, r)
    }
    pol_multipartitionne = r
    rllvar = cdr(rllvar)
    rldegre_arite = cdr(rldegre_arite)
  }
  if pol_multipartitionne is Cons(_) {
    multi_ecrit(pol_multipartitionne, llvar)
  } else {
    int(0)
  }
}

///|
/// le coefficient binomial permet de tenir compte de l'arite'
/// de la fonction resolvante.
fn garde_que_partition_init(
  d_pol_dist : Value,
  degre_arite : Value,
) -> Value raise {
  let mut pol = d_pol_dist
  let degre = car(degre_arite)
  let arite = cadr(degre_arite)
  while cdr(pol) is Cons(_) {
    let exposants = cdadr(pol)
    if share_sym__non_increasing(exposants) {
      pol = cdr(pol)
      let lg = longueur(exposants)
      rplaca(
        pol,
        list2(
          share_sym__mult(
            caar(pol),
            binomial(num_sub(degre, lg), num_sub(arite, lg)),
          ),
          exposants,
        ),
      )
      |> ignore
    } else {
      rplacd(pol, cddr(pol)) |> ignore
    }
  }
  cdr(d_pol_dist)
}

///|
fn garde_que_partition(d_pol_dist : Value, degre_arite : Value) -> Value raise {
  let mut pol = d_pol_dist
  let degre = car(degre_arite)
  let arite = cadr(degre_arite)
  while cdr(pol) is Cons(_) {
    let exposants = cdadr(pol)
    if share_sym__non_increasing(exposants) {
      pol = cdr(pol)
      let lg = longueur(exposants)
      rplaca(
        car(pol),
        share_sym__mult(
          caar(pol),
          binomial(num_sub(degre, lg), num_sub(arite, lg)),
        ),
      )
      |> ignore
    } else {
      rplacd(pol, cddr(pol)) |> ignore
    }
  }
  cdr(d_pol_dist)
}

///|
fn distribu(multipartition : Value, pol_part : Value) -> Value raise {
  mapcar(
    coe_partition => cons(
      car(coe_partition),
      cons(cdr(coe_partition), multipartition),
    ),
    pol_part,
  )
}

// BOUCLE PINCIPALE DE L'IMAGE DIRECTE

///|
fn d_direct_init(
  d_lpol : Value,
  d_x : Value,
  d_p : Value,
  d_llvar : Value,
) -> Value raise {
  direct(cdr(d_lpol), d_x, d_p, d_llvar)
}

///|
fn direct(
  l_dolpol : Value,
  d_x : Value,
  d_p : Value,
  d_llvar : Value,
) -> Value raise {
  if equal(q_d_parallele, symval(q_d_directnew)) {
    return direct_parallele(l_dolpol, d_x, d_p, d_llvar)
  }
  let multi_base = if equal(q_d_elementaire, symval(q_d_direct)) {
    macsy_list(multi_polynome2ele(l_dolpol, d_x))
  } else {
    multi_ele2pui(multi_polynome2ele(l_dolpol, d_x))
  }
  let pui_star = pui_direct(
    multi_orbit_init(d_p, cdr(d_llvar)),
    mapcar(x => cdr(x), cdr(d_llvar)),
    mapcar(x => cadr(x), cdr(multi_base)),
  )
  let degre = car(pui_star)
  pui2polynome(
    q_d_y,
    cons(
      degre,
      mapcar(
        d_pi => multi_decomp_init(d_pi, multi_base, d_llvar),
        cdr(pui_star),
      ),
    ),
  )
}

///|
/// Ici on calcule les fonctions puissances des racines de la resolvante
/// au fur et a mesure.
fn direct_parallele(
  l_dolpol : Value,
  d_x : Value,
  d_p : Value,
  d_llvar : Value,
) -> Value raise {
  let llvar = mapcar(x => cdr(x), cdr(d_llvar))
  let multi_base = if equal(q_d_elementaire, symval(q_d_direct)) {
    macsy_list(multi_polynome2ele(l_dolpol, d_x))
  } else {
    multi_ele2pui(multi_polynome2ele(l_dolpol, d_x))
  }
  let multi_orbite = multi_orbit_init(d_p, cdr(d_llvar))
  let ldegre = mapcar(x => cadr(x), cdr(multi_base)) // degres des polynomes
  let (ldegre_arite, degre_resol) = share_sym_direct__degre_resol(
    length(multi_orbite),
    ldegre,
    llvar,
  )
  print(degre_resol) |> ignore
  let mut r = one_minus(degre_resol)
  let mut listpui = list1(
    multi_decomp_init(
      pui_contract(int(0), multi_orbite, llvar, degre_resol, ldegre_arite),
      multi_base,
      d_llvar,
    ),
  )
  while !eql(int(0), r) {
    print(r) |> ignore
    let nr = one_minus(r)
    listpui = cons(
      multi_decomp_init(
        pui_contract(int(0), multi_orbite, llvar, r, ldegre_arite),
        multi_base,
        d_llvar,
      ),
      listpui,
    )
    r = nr
  }
  pui2polynome(q_d_y, cons(degre_resol, listpui))
}

///|
/// FONCTIONS SYMETRIQUES ELEMENTAIRES DES RACINES DES POLYNOMES DE
/// l$pol EN LA VARIABLE $y.
fn multi_polynome2ele(l_dolpol : Value, d_y : Value) -> Value raise {
  mapcar(pol => polynome2ele(pol, d_y), l_dolpol)
}

///|
/// DECOMPOSITION D'UN POLYNOME SYMETRIQUE CONTRACTE EN PLUSIEURS PAQUETS DE
/// VARIABLES DONT LES FONCTIONS SYMETRIQUES ELEMENTAIRES RESPECTIVES SONT
/// DONNEES
fn multi_decomp_init(
  d_multi_pc : Value,
  d_multi_base : Value,
  d_llvar : Value,
) -> Value raise {
  if equal(q_d_elementaires, symval(q_d_direct)) {
    meval(list([list1(q_d_multi_elem), d_multi_base, d_multi_pc, d_llvar]))
  } else {
    meval(list([list1(q_d_multi_pui), d_multi_base, d_multi_pc, d_llvar]))
  }
}

///|
/// on a les fonctions symetriques elementaires des racines des differents
/// polynomes. On recupere en fonction d'elles leurs fonctions puissances.
fn multi_ele2pui(multi_lelem : Value) -> Value raise {
  cons(
    list1(q_mlist),
    mapcar(
      lelem => meval(
        list3(list1(q_d_ele2pui), car(lelem), cons(list1(q_mlist), lelem)),
      ),
      multi_lelem,
    ),
  )
}

///|
fn init_share_direct() -> Unit raise {
  share_sym__defmexpr(
    q_d_direct,
    "((lambda ()) ((mlist) $list_pol $x $fonction $list_list_var) ((mprog) (($operation)) (($direct_init) $list_pol $x $fonction $list_list_var)))",
    item_text="(($direct) $list_pol $x $fonction $list_list_var)",
  )
  share_sym__defmexpr(
    q_d_orbit,
    "((lambda ()) ((mlist) $fonction $list_var) ((mprog) (($operation)) (($orbit_init) $fonction $list_var)))",
    item_text="(($orbit) $fonction $list_var)",
  )
  share_sym__defmexpr(
    q_d_multi_orbit,
    "((lambda ()) ((mlist) $fonction $list_var) ((mprog) (($operation)) (($multi_orbit_init) $fonction $list_var)))",
    item_text="(($multi_orbit) $fonction $list_var)",
  )
  share_sym__defmexpr(
    q_d_pui_direct,
    "((lambda ()) ((mlist) $multi_orbit $list_list_var $ldegre) ((mprog) (($operation)) (($pui_direct_init) $multi_orbit $list_list_var $ldegre)))",
    item_text="(($pui_direct) $multi_orbit $list_list_var $ldegre)",
  )
}
