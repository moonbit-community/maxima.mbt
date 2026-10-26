// Port of share/sym/resolv1.lisp: CALCUL DE RESOLVANTES.
// ON TRANSFORME UN POLYNOME $pol DE LA VARIABLE $var AVEC UNE FONCTION
// RESOLVANTE $fonction_resolvante DONT LES VARIABLES $list_var.

///|
fn resolvante(
  d_pol : Value,
  d_var : Value,
  d_fonction_resolvante : Value,
  d_list_var : Value,
) -> Value raise {
  let r = symval(q_d_resolvante)
  if equal(q_d_cayley, r) {
    print(Str(" resolvante de Cayley ")) |> ignore
    let subs = Collector::new()
    let mut vals = cdr(polynome2ele(d_pol, d_var))
    let mut eis = list([q_d_e1, q_d_e2, q_d_e3, q_d_e4, q_d_e5])
    while vals is Cons(_) && eis is Cons(_) {
      subs.add(list3(list1(q_mequal), car(eis), car(vals)))
      vals = cdr(vals)
      eis = cdr(eis)
    }
    meval(
      list3(
        list1(q_d_substitute),
        cons(list1(q_mlist), subs.result()),
        symval(q_d_resolcayley),
      ),
    )
  } else if equal(q_d_unitaire, r) || length(d_list_var) == 2 {
    print(Str(" resolvante unitaire ")) |> ignore
    meval(
      list([
        list1(q_d_resolvante_unitaire),
        d_pol,
        meval(
          list3(
            list1(q_d_ev),
            d_fonction_resolvante,
            meval(list3(list1(q_mequal), cadr(d_list_var), d_var)),
          ),
        ),
        d_var,
      ]),
    )
  } else if equal(q_d_produit, r) {
    // a`optimiser svp
    print(Str(" resolvante produit ")) |> ignore
    meval(
      list3(
        list1(q_d_prodrac),
        cons(list1(q_mlist), cdr(polynome2ele(d_pol, d_var))),
        int(length(d_list_var) - 1),
      ),
    )
  } else if equal(q_d_somme, r) {
    print(Str(" resolvante somme ")) |> ignore
    meval(
      list3(
        list1(q_d_somrac),
        cons(list1(q_mlist), cdr(polynome2ele(d_pol, d_var))),
        int(length(d_list_var) - 1),
      ),
    )
  } else if equal(q_d_lineaire, r) {
    print(Str(" resolvante lineaire ")) |> ignore
    linear_resolvante(
      mapcar(v => d_coeff(d_fonction_resolvante, v, n=int(1)), cdr(d_list_var)),
      polynome2ele(d_pol, d_var),
    )
  } else if equal(q_d_alternee, r) {
    print(Str(" resolvante alternee ")) |> ignore
    linear_resolvante(
      mapcar(v => d_coeff(d_fonction_resolvante, v, n=int(1)), cdr(d_list_var)),
      polynome2ele(d_pol, d_var),
      alternee=t,
    )
  } else if equal(q_d_symetrique, r) {
    print(Str(" resolvante symetrique ")) |> ignore
    // ce n'est pas a resolvante de tester la symetrie
    symetrique_resolvante(
      d_fonction_resolvante,
      d_list_var,
      polynome2ele(d_pol, d_var),
    )
  } else if equal(q_d_groupe, r) {
    print(Str(" resolvante groupe ")) |> ignore
    print(share_sym_resolv1__q_non_implante) |> ignore
    // GROUPE_RESOLVANTE is not defined by the sym package.
    funcall(share_sym_resolv1__q_groupe_resolvante, [
      d_fonction_resolvante,
      d_list_var,
      polynome2ele(d_pol, d_var),
    ])
  } else {
    // ici on peut eventuellement rajouter des tests :
    // symetrique ou lineaire
    print(Str(" resolvante generale ")) |> ignore
    if !(cadr(d_list_var) is Cons(_)) {
      meval(
        list([
          list1(q_d_direct),
          list2(list1(q_mlist), d_pol),
          d_var,
          d_fonction_resolvante,
          list2(list1(q_mlist), d_list_var),
        ]),
      )
    } else {
      meval(
        list([
          list1(q_d_direct),
          d_pol,
          d_var,
          d_fonction_resolvante,
          d_list_var,
        ]),
      )
    }
  }
}

///|
let share_sym_resolv1__q_non_implante : Value = sym("NON IMPLANTE")

///|
let share_sym_resolv1__q_groupe_resolvante : Value = sym("groupe_resolvante")

///|
/// cette fonction semble inutile
fn cree_subs(val : Value, d_ei : Value) -> Value raise {
  list3(list1(q_mequal), d_ei, val)
}

// RESOLVANTES SYMETRIQUES
// i.e. LA FONCTION RESOLVANTE EST SYMETRIQUE EN p VARIABLES.
// COMME L'ORBITE DE LA FONCTION RESOLVANTE SOUS S_p EST LA FONCTION
// RESOLVANTE, LES FONCTIONS PUISSANCES DE CETTE ORBITE SE CALCULENT EN
// CALCULANT LES PUISSANCES DE LA FONCTION RESOLVANTE. ENSUITE ON PASSE A
// S_n (n LE DEGRE DU POLYNOME INITIAL) EN RAJOUTANT A CHAQUE PARTITION I LE
// COEFFICIENT BINOMIAL BIN(n-lg(I),p-lg(I)).

///|
fn symetrique_resolvante(
  d_fct_resolvante : Value,
  d_list_var : Value,
  elementaires : Value,
) -> Value raise {
  meval(list1(list1(q_d_bidon2))) |> ignore // charger pui.lisp et multmon.lisp
  meval(list([list1(q_d_multsym), list1(q_mlist), list1(q_mlist), int(0)]))
  |> ignore
  with_special(q_d_pui, int(3), () => {
    let degre = car(elementaires)
    let longueur = int(length(cdr(d_list_var)))
    // recherche de la fonction resolvante sous la forme
    // d'un polynome partitionne
    let fct_resolvante = cont2part_rep1(
      d_expand(
        meval(list3(list1(q_d_contract), d_fct_resolvante, d_list_var)),
      ),
      d_list_var,
    )
    let degre_resol = binomial(degre, longueur)
    pui2polynome(
      q_d_y,
      cons(
        degre_resol,
        puissances_symetrique_resolvante(
          degre_resol,
          longueur,
          fct_resolvante,
          fct_resolvante,
          meval(
            list3(
              list1(q_d_ele2pui),
              degre_resol,
              cons(list1(q_mlist), elementaires),
            ),
          ),
        ),
      ),
    )
  })
}

///|
/// la fonction multsym realise le produit de deux polynomes symetriques.
/// il faut mettre le polynome f plus creux que puif en deuxieme argument
fn puissances_symetrique_resolvante(
  ind : Value,
  arite_f : Value,
  f : Value,
  puif : Value,
  d_puissances : Value,
) -> Value raise {
  if !num_lt(int(0), ind) {
    return Nil
  }
  print(num_sub(num_sub(int(length(d_puissances)), int(1)), ind)) |> ignore
  let head = p__red1(
    d_puissances,
    complete_pui(cadr(d_puissances), arite_f, puif),
  )
  cons(
    head,
    puissances_symetrique_resolvante(
      one_minus(ind),
      arite_f,
      f,
      if num_lt(int(1), ind) {
        multsym(puif, f, arite_f)
      } else {
        Nil
      },
      d_puissances,
    ),
  )
}

///|
/// Pour le cas qui nous interesse, il est indispensable de ne pas faire
/// de remplacement physique sur la liste.
fn complete_pui(n : Value, p : Value, puissance_resolvante : Value) -> Value raise {
  mapcar(
    part => {
      // part=(part)(1) comme representation
      let lg = longueur(cdr(part))
      list_star([
        lg,
        share_sym__mult(car(part), binomial(num_sub(n, lg), num_sub(p, lg))),
        ch2rep(cdr(part)),
      ])
    },
    puissance_resolvante,
  )
}

// ALGORITHMES POUR CALCULER DES RESOLVANTES LINEAIRES
// I.E LA FONCTION RESOLVANTE EST UNE FORME LINEAIRE DANS $K[x_1,...,x_n]$
// SES COEFFICIENTS SONT DANS $coeff.
// ON SUPPOSE DANS UN PREMIER TEMPS QUE $coeff NE COMPORTE QUE DES VALEURS
// NON NULLES

///|
fn linear_resolvante_init(
  d_pol : Value,
  d_var : Value,
  d_coeff : Value,
  alternee? : Value = Nil,
) -> Value raise {
  linear_resolvante(cdr(d_coeff), polynome2ele(d_pol, d_var), alternee~)
}

///|
/// $bidon2 SERT A CHARGER LE FICHIER PUI.LISP SI CE N'EST DEJA FAIT
fn linear_resolvante(
  coeff : Value,
  elementaires : Value,
  alternee? : Value = Nil,
) -> Value raise {
  meval(list1(list1(q_d_bidon2))) |> ignore
  let degre = car(elementaires)
  // on enleve les coefficients nuls
  let coeff = retirezero(coeff)
  // il faut que les coefficients soient non nuls:
  let longueur = int(length(coeff))
  let permut_coeff = {
    let p = permut(coeff)
    if alternee.truthy() {
      permut_alterne(p)
    } else {
      p
    }
  }
  let degre_resol = num_mul(binomial(degre, longueur), {
    let d = int(length(permut_coeff))
    if alternee.truthy() {
      num_mul(int(2), d)
    } else {
      d
    }
  })
  pui2polynome(
    q_d_y,
    cons(
      degre_resol,
      puissances_linear_resolvante(
        degre_resol,
        longueur,
        permut_coeff,
        meval(
          list3(
            list1(q_d_ele2pui),
            degre_resol,
            cons(list1(q_mlist), elementaires),
          ),
        ),
        alternee,
      ),
    ),
  )
}

///|
/// on utilise directement, p_red1, une fonction interne au fichier
/// pui.lisp evitant ainsi un interfacage inutile et couteux.
fn puissances_linear_resolvante(
  poids : Value,
  longueur : Value,
  permut_coeff : Value,
  d_puissances : Value,
  alternee : Value,
) -> Value raise {
  let mut i = poids
  let mut sol : Value = Nil
  while !num_eq(int(0), i) {
    let v = if alternee.truthy() && oddp(i) {
      int(0)
    } else {
      let pui = p__red1(
        d_puissances,
        pui_linear_resolvante(permut_coeff, i, longueur, cadr(d_puissances)),
      )
      if alternee.truthy() {
        share_sym__mult(int(2), pui)
      } else {
        pui
      }
    }
    sol = cons(v, sol)
    i = one_minus(i)
  }
  sol
}

///|
/// recherche de la r-ieme fonction puissance generique sur la base des
/// formes monomiales en n variables (n=degre(pol)): LES PARTITIONS DE POIDS
/// FIXE ET DE LONGUEUR BORNEE AVEC EN PLUS COMME COEFFICIENTS :
/// BIN(n-lg(I),p-lg(I))*MULTINOMIAL(POIDS(I),I)*SUM(c^I,c \in ORBIT(coeff,S_p))
fn pui_linear_resolvante(
  permut_coeff : Value,
  poids : Value,
  longueur : Value,
  n : Value,
) -> Value raise {
  let lpart = cons(Nil, Nil)
  somme_orbitale(
    poids,
    num_sub(longueur, int(1)),
    int(0),
    maxote(poids, longueur),
    Nil,
    lpart,
    permut_coeff,
    poids,
    n,
    longueur,
  )
  |> ignore
  print(poids) |> ignore
  cdr(lpart)
}

///|
fn somme_orbitale(
  poids : Value,
  rlongueur : Value,
  ote : Value,
  maxote_ : Value,
  partition : Value,
  lpart : Value,
  permut_coeff : Value,
  poids_init : Value,
  n : Value,
  p : Value,
) -> Value raise {
  if minusp(rlongueur) {
    // les partitions obtenues ne sont pas sous la forme [partition](2) avec
    // la longueur en tete; de plus on passe d'une fonction p-aire a une
    // n-aire => (bin (- n lg) (- p lg)) sans oublier le coefficient
    // multinomial de la partition
    let partition = sanszero(partition)
    let lg = int(length(partition))
    let orbit_mon = ev_forme_monomiale(permut_coeff, partition)
    if !equal(int(0), orbit_mon) {
      rplacd(
        lpart,
        list1(
          list_star([
            lg, // passer de $S_p$ a $S_n$
            m_star(
              list2(
                num_mul(
                  binomial(num_sub(n, lg), num_sub(p, lg)),
                  d_multinomial(
                    poids_init,
                    cons(list1(q_mlist), reverse(partition)),
                  ),
                ),
                orbit_mon,
              ),
            ),
            ch2rep(reverse(partition)),
          ]),
        ),
      )
    } else {
      Nil
    }
  } else {
    somme_orbitale(
      ote,
      num_sub(rlongueur, int(1)),
      num_max(int(0), num_sub(num_mul(int(2), ote), poids)),
      maxote(ote, rlongueur),
      cons(num_sub(poids, ote), partition),
      lpart,
      permut_coeff,
      poids_init,
      n,
      p,
    )
    |> ignore
    if num_lt(ote, maxote_) {
      somme_orbitale(
        poids,
        rlongueur,
        one_plus(ote),
        maxote_,
        partition,
        last(lpart),
        permut_coeff,
        poids_init,
        n,
        p,
      )
    } else {
      Nil
    }
  }
}

///|
/// A PARTIR DES PERMUTATIONS D'UN p-UPLET CONSTRUIRE L'ALPHABET DES MONOMES
/// CONSTITUE' AVEC LES PERMUTATIONS COMME VARIABLES ET LA PARTITION part
/// COMME EXPOSANT. ON CALCULE ICI LA SOMME DES ELEMENT DE CET ALPHABET.
/// The Lisp file defines this function twice; the second definition (for
/// numerical coefficients of the transformation) is the one in effect.
fn ev_forme_monomiale(permut_coeff : Value, part : Value) -> Value raise {
  add(
    mapcar(
      coeff => {
        let factors = Collector::new()
        let mut a = coeff
        let mut b = part
        while a is Cons(_) && b is Cons(_) {
          factors.add(expt(car(a), car(b)))
          a = cdr(a)
          b = cdr(b)
        }
        m_star(factors.result())
      },
      permut_coeff,
    ),
  )
}

///|
fn sanszero(rpartition : Value) -> Value raise {
  let mut r = rpartition
  while num_eq(int(0), car(r)) {
    r = cdr(r)
  }
  r
}

///|
/// liste de coefficients formels ou numerique a laquelle
/// on desire retirer les zeros.
fn retirezero(coeff : Value) -> Value raise {
  let c = Collector::new()
  for x in coeff.iter() {
    if !equal(int(0), x) {
      c.add(x)
    }
  }
  c.result()
}

// ALGORITHMES POUR CALCULER DES RESOLVANTES LINEAIRES-ALTERNEE
// LE PB EST DE CHANGER (PERMUT COEFF ) (LES PERMUTATIONS SOUS LE GROUPE
// SYMETRIQUE ) PAR (PERMUT-ALTERNEE COEFF) OU L'ON QUOTIENTE PAR
// <(1 2)(3 4)...(P-1 P)>

///|
fn permut_alterne(permut_coeff : Value) -> Value raise {
  let mut sol = list1(car(permut_coeff))
  let mut p = cdr(permut_coeff)
  let mut c = cadr(permut_coeff)
  while p is Cons(_) {
    if pas_dans(mapcar(x => num_neg(x), c), sol).truthy() {
      sol = cons(c, sol)
    }
    p = cdr(p)
    c = cadr(p)
  }
  sol
}

///|
/// ATTENTION ICI TOUT DOIT-ETRE NUMERIQUE:
fn pas_dans(u : Value, list_ : Value) -> Value raise {
  for x in list_.iter() {
    if equal(u, x) {
      return Nil
    }
  }
  t
}

///|
fn resol_carre(degre : Value, puissances : Value) -> Value raise {
  un_sur_deux(
    cdr(puireduc_init(degre, cons(num_div(degre, int(2)), puissances))),
  )
}

///|
/// liste =(p1,p2,p3,....)
fn un_sur_deux(liste : Value) -> Value raise {
  let c = Collector::new()
  let mut l = liste
  while l is Cons(_) {
    c.add(cadr(l))
    l = cddr(l)
  }
  c.result()
}

///|
fn init_share_resolv1() -> Unit raise {
  share_sym__defmexpr(
    q_d_linear_resolvante,
    "((lambda ()) ((mlist) $pol $var $coeff) ((mprog) (($operation)) ((linear_resolvante_init) $pol $var $coeff)))",
    item_text="(($linear_resolvante) $pol $var $coeff)",
  )
  share_sym__defmexpr(
    q_d_resolvante,
    "((lambda ()) ((mlist) $pol $var $fonction_resolvante $lvar) ((mprog) (($operation)) ((resolvante) $pol $var $fonction_resolvante $lvar)))",
    item_text="(($resolvante) $pol $var $fonction_resolvante $lvar)",
  )
  share_sym__defmexpr(
    q_d_somme_orbitale,
    "((lambda ()) ((mlist) $coeff poids) ((mprog) (($operation)) ((somme_orbitale_init) $coeff poids)))",
    item_text="(($somme_orbitale) $coeff poids)",
  )
}
