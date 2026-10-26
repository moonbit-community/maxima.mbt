// Port of share/sym/util.lisp: utilities of the sym package.
// On a des coefficients dans k[y1, ...,yn];
// p=(t1 t2 ... tn)  t1 > t2 > ... ; t = (longueur coe . partition)

///|
fn d_estpartition(l : Value) -> Value raise {
  lbool(share_sym__non_increasing(cdr(l)))
}

// MERGE PHYSIQUE AVEC SOMME SUR LES GRANDS ENTIERS
// ON UTILISE LE PREDICAT SUR LES TERMES ET NON SUR LES MONOMES (comme merge)

///|
fn somme(l1 : Value, l2 : Value, pr : Value) -> Value raise {
  if l1 is Nil {
    return l2
  }
  if l2 is Nil {
    return l1
  }
  let t1 = termi(l1)
  let t2 = termi(l2)
  if equal(tmon(t1), tmon(t2)) {
    chcoeterm(t1, share_sym__add(tcoe(t1), tcoe(t2))) |> ignore
    if numberp(tcoe(t1)) && zerop(tcoe(t1)) {
      somme(cdr(l1), cdr(l2), pr)
    } else {
      somme2(cdr(l2), l1, pr) |> ignore
      l1
    }
  } else if funcall(pr, [t1, t2]).truthy() {
    somme2(l2, l1, pr) |> ignore
    l1
  } else {
    somme2(l1, l2, pr) |> ignore
    l2
  }
}

///|
fn somme2(l2 : Value, l1 : Value, pr : Value) -> Value raise {
  let mut l1 = l1
  let mut l2 = l2
  let mut ll2 : Value = Nil
  let mut t1 = termi(cdr(l1))
  let mut t2 = termi(l2)
  ignore(ll2)
  while true {
    // end test: (or (null l2) (and (null (cdr l1)) (nconc l1 l2)))
    if l2 is Nil {
      break
    }
    if cdr(l1) is Nil {
      nconc(l1, l2) |> ignore
      break
    }
    if equal(tmon(t1), tmon(t2)) {
      chcoeterm(t1, share_sym__add(tcoe(t1), tcoe(t2))) |> ignore
      l2 = cdr(l2)
      t2 = termi(l2)
      if numberp(tcoe(t1)) && zerop(tcoe(t1)) {
        l1 = rplacd(l1, cddr(l1))
      } else {
        l1 = cdr(l1)
      }
    } else if funcall(pr, [t1, t2]).truthy() {
      l1 = cdr(l1)
    } else {
      ll2 = cdr(l1)
      l1 = cdr(rplacd(l1, l2))
      l2 = ll2
      t2 = termi(l2)
    }
    t1 = termi(cdr(l1))
  }
  Nil
}

// CREATION D'UNE LISTE LISP DE nb VARIABLES GENERIQUES : ($x1 ... $x(nb))
// (lvar 2 '(r)) = ; ($X1 $X2 R)

///|
fn lvar(nb : Value, lvar : Value) -> Value raise {
  let mut nb = nb
  let mut lvar = lvar
  while !eql(int(0), nb) {
    lvar = cons(share_sym__concat([q_d_x, nb]), lvar)
    nb = one_minus(nb)
  }
  lvar
}

///|
/// (lvar_lettre 2 '(r) 'x) = (X1 X2 R)
fn lvar_lettre(nb : Value, lvar : Value, lettre : Value) -> Value raise {
  let mut nb = nb
  let mut lvar = lvar
  while !eql(int(0), nb) {
    lvar = cons(share_sym__concat([lettre, nb]), lvar)
    nb = one_minus(nb)
  }
  lvar
}

///|
/// Calcul du degre d'un polynome symetrique avec REP([pol]) = [lppart](2)
fn d_degrep(pol : Value) -> Value raise {
  set(q_d, int(0)) |> ignore
  let degs = mapcar(mon => d_degre(cddr(mon)), pol)
  mapc(
    di => if num_lt(symval(q_d), di) { set(q_d, di) |> ignore },
    degs,
  )
  |> ignore
  symval(q_d)
}

///|
/// Calcul du degre d'une forme monomiale avec REP([forme mon])=[partition](2)
/// mon = (lgI coeI . I)
fn d_degre(mon : Value) -> Value raise {
  // (constantp mon): MON is a list, NIL or a self-evaluating atom
  if !(mon is Cons(_)) || mon is Nil {
    int(0)
  } else {
    num_add(num_mul(car(mon), cadr(mon)), d_degre(cddr(mon)))
  }
}

///|
/// TESTE SI ON A AFFAIRE A UNE CONSTANTE APRES LE LECTEUR
/// termpart = REP([somme orbitale]) avec [somme orbitale] = (coe.[partition])
fn constante(termpart : Value) -> Value raise {
  if cdr(termpart) is Nil {
    return t
  }
  lbool(every(exposant => eql(int(0), exposant), cdr(termpart)))
}

///|
/// avec [somme orbitale] = (longueur coe.[partition])
/// il suffit de tester si la longueur est nulle
fn lconstante(ltermpart : Value) -> Value raise {
  lbool(eql(int(0), car(ltermpart)))
}

///|
/// Calcul des longueurs de chaque partition contenue dans la liste listparts
/// sous forme [partition](2)
fn lgparts(ppart : Value) -> Value raise {
  mapcar(mon => cons(d_calculvar(cdr(mon)), mon), ppart)
}

///|
/// Calcul de la longueur d'une partition I. Pour [partition](1)
fn longueur(i : Value) -> Value raise {
  let mut n = 0
  let mut i = i
  while !(i is Nil || eql(int(0), car(i))) {
    n += 1
    i = cdr(i)
  }
  int(n)
}

///|
/// Pour [partition](2), pouvant se terminer par des 0.
fn d_calculvar(i : Value) -> Value raise {
  if i is Nil || eql(int(0), car(i)) {
    int(0)
  } else {
    num_add(cadr(i), d_calculvar(cddr(i)))
  }
}

// PREDICATS
// term est un [partition](2) c'est a dire sous la forme :
// dans la forme (a1 m1 a2 m2...) ou mi est la multiplicite' de ai (> a(i+1))
// (2 1 ...) < (2 2 ...) < (3 1 2 1 ...) < (3 1 2 2 ...)

///|
fn d_lex(term1 : Value, term2 : Value) -> Value raise {
  let mut term1 = term1
  let mut term2 = term2
  while true {
    if term1 is Nil {
      return t
    }
    if term2 is Nil {
      return Nil
    }
    let pui1 = car(term1)
    let nb1 = cadr(term1)
    let pui2 = car(term2)
    let nb2 = cadr(term2)
    if num_lt(pui1, pui2) || (eql(pui1, pui2) && num_lt(nb1, nb2)) {
      return t
    }
    if num_lt(pui2, pui1) || num_lt(nb2, nb1) {
      return Nil
    }
    term1 = cddr(term1)
    term2 = cddr(term2)
  }
  Nil
}

///|
/// q inferieur a p pour l'ordre des longueurs ou p et q sont des
/// sommes orbitales represente'es par des [terme partionne](2) avec
/// la longueur en plus en tete
fn orlongsup(p : Value, q : Value) -> Value raise {
  if equal(cddr(p), cddr(q)) {
    Nil
  } else if num_gt(car(p), car(q)) {
    t
  } else if eql(car(p), car(q)) {
    d_lex(cddr(q), cddr(p))
  } else {
    Nil
  }
}

///|
/// le vrai ordre des longueurs q inferieur a p pour cet ordre
fn orlong(p : Value, q : Value) -> Value raise {
  if equal(cddr(p), cddr(q)) {
    Nil
  } else if num_lt(car(p), car(q)) {
    t
  } else if eql(car(p), car(q)) {
    d_lex(cddr(p), cddr(q))
  } else {
    Nil
  }
}

///|
fn d_orlong_cst(p : Value, q : Value) -> Value raise {
  let c = lconstante(p)
  if c.truthy() {
    c
  } else if lconstante(q).truthy() {
    Nil
  } else {
    orlong(p, q)
  }
}

///|
/// p > q
fn d_e_lexinv_cst(mon1 : Value, mon2 : Value) -> Value raise {
  let c = constante(mon1)
  if c.truthy() {
    c
  } else if constante(mon2).truthy() {
    Nil
  } else {
    d_e_lexinv(mon1, mon2)
  }
}

///|
/// p=(lg(I) coeI .I)
fn d_e_lexinv(p : Value, q : Value) -> Value raise {
  if !equal(cddr(p), cddr(q)) {
    d_lex(cddr(q), cddr(p))
  } else {
    Nil
  }
}

///|
/// p < q; les constantes sont les + petites
fn d_e_lex_cst(p : Value, q : Value) -> Value raise {
  let c = constante(p)
  if c.truthy() {
    c
  } else if constante(q).truthy() {
    Nil
  } else {
    d_e_lex(p, q)
  }
}

///|
fn d_e_lex(p : Value, q : Value) -> Value raise {
  if !equal(cddr(p), cddr(q)) {
    d_lex(cddr(p), cddr(q))
  } else {
    Nil
  }
}

///|
/// teste sur deux monomes en representation distribuee (i1 i2 ...)
fn lex_term(term1 : Value, term2 : Value) -> Value raise {
  lex_mon(cdr(term1), cdr(term2))
}

///|
fn lex_mon(m1 : Value, m2 : Value) -> Value raise {
  if equal(m1, m2) {
    return Nil
  }
  let mut a = m1
  let mut b = m2
  while a is Cons(_) && b is Cons(_) {
    let e1 = car(a)
    let e2 = car(b)
    if !eql(e1, e2) {
      return lbool(num_gt(e1, e2))
    }
    a = cdr(a)
    b = cdr(b)
  }
  // mapc returns its first list argument
  m1
}

// INTERFACE
// Le lecteur utilise la fonction $distri_lect qui appelle distri_lecteur

///|
fn lect(d_pol : Value, d_lvar : Value) -> Value raise {
  mapcar(
    x => cdr(x),
    cdr(meval(list3(list1(q_d_distri_lect), d_pol, d_lvar))),
  )
}

///|
/// [ppart](i) lisp ==> [ppart](i) macsyma
fn macsy_list(llist : Value) -> Value raise {
  cons(list1(q_mlist), mapcar(l => cons(list1(q_mlist), l), llist))
}

///|
/// sa recipropque :
fn mac2lisp(list_ : Value) -> Value raise {
  // CDR of a non-list (e.g. a symbol thrown by TPARTPOL3) is a Lisp error
  mapcar(x => cdr(x), cdr_strict(list_))
}

///|
/// Si REP([pol]) =[ppart](1). Pour une liste de polynomes.
fn ecrit_listpol(listpol : Value, lvar : Value) -> Value raise {
  mapcar(pol => ecrit_pol(pol, lvar), listpol)
}

///|
/// Pour un polynome de plusieurs groupes de variables
/// en representation distribuee : (c m1 m2 ... mp) ou mi est un monome
/// en X^(i). llvar = (X^(1), ..., X^(p)) est une liste de listes de variables
fn multi_ecrit(pol : Value, llvar : Value) -> Value raise {
  if cdr(pol) is Nil {
    multi_ecrit_mon(caar(pol), cdr(car(pol)), llvar)
  } else {
    share_sym__fadd(
      mapcar(terme => multi_ecrit_mon(car(terme), cdr(terme), llvar), pol),
    )
  }
}

///|
fn multi_ecrit_mon(coe : Value, llexposants : Value, llvar : Value) -> Value raise {
  if llvar is Nil {
    return coe
  }
  let mut coe = coe
  let mut a = llexposants
  let mut b = llvar
  while a is Cons(_) && b is Cons(_) {
    coe = ecrit_mon(car(a), car(b), coe)
    a = cdr(a)
    b = cdr(b)
  }
  coe
}

///|
/// Pour un polynome a un groupe de variables dont le representaion
/// partitionnee est de type 1, on se sert de l'ecrivain.
fn ecrit_pol(ppart : Value, lvar : Value) -> Value raise {
  meval(
    list3(
      list1(q_d_distri_ecrit),
      macsy_list(ppart),
      cons(list1(q_mlist), lvar),
    ),
  )
}

///|
/// Si REP([pol]) = [ppart](2) on se ramene au cas precedent
fn n2ecrit(ppart : Value, lvar : Value) -> Value raise {
  ecrit_pol(ch1repol(ppart), lvar)
}

// CHANGEMENTS DES REPRESENTATIONS DE PARTITIONS

///|
/// Fonction passant de [partition](1) a [partition](2)
fn ch2rep(partition1 : Value) -> Value raise {
  if partition1 is Cons(_) && !eql(int(0), car(partition1)) {
    ch2rep2(cdr(partition1), list2(int(1), car(partition1)))
  } else {
    Nil
  }
}

///|
fn ch2rep2(partition1 : Value, partition2 : Value) -> Value raise {
  let mut partition1 = partition1
  let mut partition2 = partition2
  while !(partition1 is Nil || eql(int(0), car(partition1))) {
    if eql(car(partition1), cadr(partition2)) {
      partition2 = rplaca(partition2, one_plus(car(partition2)))
    } else {
      partition2 = cons(int(1), cons(car(partition1), partition2))
    }
    partition1 = cdr(partition1)
  }
  nreverse(partition2)
}

///|
/// Passer d'un polynome partitionne avec [partition](1) a [partition](2)
fn ch2repol(ppart : Value) -> Value raise {
  mapcar(tpart => cons(car(tpart), ch2rep(cdr(tpart))), ppart)
}

///|
/// PASSAGE DE [partition](2) a [partition](1)
fn ch1rep(partition2 : Value) -> Value raise {
  if partition2 is Nil {
    Nil
  } else {
    ch1rep2(
      cddr(partition2),
      share_sym__make_list(cadr(partition2), car(partition2)),
    )
  }
}

///|
fn ch1rep2(partition2 : Value, partition1 : Value) -> Value raise {
  let mut partition2 = partition2
  let mut partition1 = partition1
  while partition2 is Cons(_) {
    partition1 = nconc(
      share_sym__make_list(cadr(partition2), car(partition2)),
      partition1,
    )
    partition2 = cddr(partition2)
  }
  nreverse(partition1)
}

///|
/// Maintenant passer d'un polynome partitionne avec [partition](2)
/// a un polynome partitionne avec [partition](1)
fn ch1repol(ppart : Value) -> Value raise {
  mapcar(tpart => cons(car(tpart), ch1rep(cdr(tpart))), ppart)
}

///|
/// Passage de la premiere represensentation des partitions a la seconde;
/// listM =(i1 i2 i3 ...ip) avec 0< i1 <= i2 <= ... <=ip
fn part(listm : Value) -> Value raise {
  d_part2(cdr(listm), cons(car(listm), cons(int(1), Nil)))
}

///|
fn d_part2(listm : Value, lpartm : Value) -> Value raise {
  let mut listm = listm
  let mut lpartm = lpartm
  while listm is Cons(_) {
    lpartm = if eql(car(listm), car(lpartm)) {
      rplaca(cdr(lpartm), one_plus(cadr(lpartm))) |> ignore
      lpartm
    } else {
      cons(car(listm), cons(int(1), lpartm))
    }
    listm = cdr(listm)
  }
  lpartm
}

///|
fn d_cherchepui(mmon : Value) -> Value raise {
  if atom(mmon) {
    int(1)
  } else {
    car(last(mmon))
  }
}

// CALCUL DU CARDINAL DE L' ORBITE D'UN MONOME DONT LA LISTE DES EXPOSANTS
// EST DONNE PAR UNE PARTITION [partition](2)=(a1 m1 a2 m2...)
// qui est n!/(m0!m1!...) ou n=somme_{i=0} mi
// Ou du coefficient multinomial associe a une partition type [partition](1)
// qui est |I|!/(i1!i2!....)

///|
fn d_card_orbit(d_partition : Value, d_card : Value) -> Value raise {
  card_orbit(cdr(d_partition), d_card)
}

///|
fn card_orbit(partition : Value, card : Value) -> Value raise {
  // le nombre a la puissance 0
  nbperm0(card, num_sub(card, d_calculvar(partition)), partition)
}

///|
fn d_multinomial(poids : Value, d_partition : Value) -> Value raise {
  multinomial(
    nbperm2(int(1), poids, int(1), cadr(d_partition)),
    cddr(d_partition),
  )
}

///|
fn multinomial(prec_multinomial : Value, partition : Value) -> Value raise {
  let mut prec = prec_multinomial
  let mut partition = partition
  while !(partition is Nil || num_eq(int(0), car(partition))) {
    prec = nbperm2(car(prec), cadr(prec), int(1), car(partition))
    partition = cdr(partition)
  }
  car(prec)
}

///|
fn nbperm0(card : Value, m0 : Value, part : Value) -> Value raise {
  nbperm(nbperm2(int(1), card, int(1), m0), part)
}

///|
fn nbperm(lpermn : Value, part : Value) -> Value raise {
  let mut lpermn = lpermn
  let mut part = part
  while part is Cons(_) {
    lpermn = nbperm2(car(lpermn), cadr(lpermn), int(1), cadr(part))
    part = cddr(part)
  }
  car(lpermn)
}

///|
fn nbperm2(perm : Value, n : Value, i : Value, mi : Value) -> Value raise {
  let mut perm = perm
  let mut n = n
  let mut i = i
  while !num_lt(mi, i) {
    perm = num_div(mult(perm, n), i)
    n = one_minus(n)
    i = one_plus(i)
  }
  list2(perm, n)
}

// Calcul du cardinal du stabilisateur d'une liste ordonnee
// de paires ou de nombres dans l'ordre lexicographique croissant.

///|
fn d_card_stab(d_part : Value, d_egal : Value) -> Value raise {
  d_card_stab_init(d_part, d_egal)
}

///|
fn d_card_stab_init(d_part : Value, d_egal : Value) -> Value raise {
  // (find-symbol (string $egal))
  let name = match d_egal {
    Str(s) => s
    _ => symbol_name(d_egal)
  }
  let egal = find_symbol(name)
  card_stab(cdr(d_part), if egal is Nil { sym(name) } else { egal })
}

///|
fn card_stab(s : Value, egal : Value) -> Value raise {
  let lmultip = sort_list(multiplicites(s, egal), (a, b) => num_lt(a, b))
  prod_factor(lmultip)
}

///|
fn multiplicites(s : Value, egal : Value) -> Value raise {
  multiplicites2(cdr(s), car(s), int(1), Nil, egal)
}

///|
fn multiplicites2(
  s : Value,
  ai : Value,
  mi : Value,
  lmultip : Value,
  egal : Value,
) -> Value raise {
  let mut s = s
  let mut ai = ai
  let mut mi = mi
  let mut lmultip = lmultip
  while s is Cons(_) {
    if share_sym__egal(egal, car(s), ai) {
      mi = one_plus(mi)
    } else {
      lmultip = cons(mi, lmultip)
      ai = car(s)
      mi = int(1)
    }
    s = cdr(s)
  }
  cons(mi, lmultip)
}

///|
/// l = (m1 m2 ... mp) croissante , on veut m1!m2!...mp!
fn prod_factor(l : Value) -> Value raise {
  let mut p = int(1)
  for x in list_factor(l, list1(factorielle(car(l)))).iter() {
    p = num_mul(p, x)
  }
  p
}

///|
/// l = (mi m(i+1) ... mp) et lfactor = (mi!, ..., m2!, m1!)
fn list_factor(l : Value, lfactor : Value) -> Value raise {
  let mut l = l
  let mut lfactor = lfactor
  while cdr(l) is Cons(_) {
    lfactor = cons(fact_recur(car(l), cadr(l), car(lfactor)), lfactor)
    l = cdr(l)
  }
  lfactor
}

///|
fn fact_recur(m1 : Value, m2 : Value, factm1 : Value) -> Value raise {
  if eql(m1, m2) {
    factm1
  } else {
    num_mul(finfact(one_plus(m1), m2, one_plus(m1)), factm1)
  }
}

///|
fn finfact(i : Value, m2 : Value, finfactm2 : Value) -> Value raise {
  let mut i = i
  let mut f = finfactm2
  while !eql(i, m2) {
    f = num_mul(one_plus(i), f)
    i = one_plus(i)
  }
  f
}

///|
fn factorielle(n : Value) -> Value raise {
  if eql(int(0), n) {
    int(1)
  } else {
    num_mul(n, factorielle(one_minus(n)))
  }
}

///|
/// OBTENIR TOUTES LES PERMUTATIONS D'UN NUPLET D'ENTIER (Philippe Esperet)
fn d_lpermut(nuplet : Value) -> Value raise {
  cons(
    list1(q_mlist),
    mapcar(permu => cons(list1(q_mlist), permu), permut(cdr(nuplet))),
  )
}

// EXPRESSION D'UN POLYNOME DONT ON CONNAIT LES FONCTIONS SYMETRIQUES
// ELEMENTAIRES DES RACINES
// $fct_elem =[cardinal, e_1,e_2,...,e_cardinal,...]

///|
fn d_ele2polynome(d_fct_elem : Value, d_z : Value) -> Value raise {
  ele2polynome(cdr(d_fct_elem), d_z)
}

///|
fn ele2polynome(l_degre__dolelem : Value, d_z : Value) -> Value raise {
  genpoly2(
    one_minus(car(l_degre__dolelem)),
    int(-1),
    share_sym__exp(d_z, car(l_degre__dolelem)),
    cdr(l_degre__dolelem),
    d_z,
  )
}

///|
fn genpoly2(
  exp_ : Value,
  sign : Value,
  d_pol : Value,
  l__dolelem : Value,
  d_z : Value,
) -> Value raise {
  // SIGN is a special variable
  let mut exp_ = exp_
  let mut sign = sign
  let mut pol = d_pol
  let mut l = l__dolelem
  while l is Cons(_) {
    let s = sign
    let e = exp_
    let p = pol
    let el = car(l)
    pol = with_special(q_sign, s, () => share_sym__add(
      p,
      share_sym__mult(share_sym__mult(s, el), share_sym__exp(d_z, e)),
    ))
    exp_ = one_minus(exp_)
    sign = num_mul(int(-1), sign)
    l = cdr(l)
  }
  pol
}

// OBTENIR UN POLYNOME A PARTIR DES FONCTIONS PUISSANCES DE SES RACINES
// fct_pui = (card p1 p2 ...)

///|
fn d_pui2polynome(d_var : Value, d_fct_pui : Value) -> Value raise {
  pui2polynome(d_var, cdr(d_fct_pui))
}

///|
fn pui2polynome(variable : Value, fct_pui : Value) -> Value raise {
  with_special(q_d_pui2ele, q_d_girard, () => ele2polynome(
    cdr(
      meval(
        list3(list1(q_d_pui2ele), car(fct_pui), cons(list1(q_mlist), fct_pui)),
      ),
    ),
    variable,
  ))
}

// CALCUL DES FONCTIONS SYMETRIQUES ELEMENTAIRES DES RACINES D'UN POLYNOME
// entrees : $p un polynome en la variable $var
// sortie  :  [d , e1, ...,ed] ou d est le degre du polynome

///|
fn d_polynome2ele(d_p : Value, d_var : Value) -> Value raise {
  cons(list1(q_mlist), polynome2ele(d_p, d_var))
}

///|
fn polynome2ele(d_p : Value, d_var : Value) -> Value raise {
  let alt = int(-1)
  let n = meval(list3(list1(q_d_hipow), d_p, d_var))
  let an = meval(list([list1(q_d_coeff), d_p, d_var, n]))
  let mut alt = alt
  let mut i = int(1)
  let mut elem : Value = Nil
  while !num_eq(one_plus(n), i) {
    let new_elem = cons(
      share_sym__divi(
        share_sym__mult(
          alt,
          meval(list([list1(q_d_coeff), d_p, d_var, num_sub(n, i)])),
        ),
        an,
      ),
      elem,
    )
    alt = num_mul(int(-1), alt)
    i = one_plus(i)
    elem = new_elem
  }
  cons(n, nreverse(elem))
}

///|
/// Obtenir tout les coefficients, meme les nuls,
/// (cn c(n-1)...c0) ou ci coefficient de x**i.
fn lcoe2(precedexp : Value, p : Value, lcoe : Value) -> Value raise {
  if p is Nil {
    if eql(int(0), precedexp) {
      t
    } else {
      rplacd(lcoe, share_sym__make_list(precedexp, int(0)))
    }
  } else {
    let exp_ = car(p)
    let coe = cadr(p)
    if eql(precedexp, one_plus(exp_)) {
      lcoe2(exp_, cddr(p), cdr(rplacd(lcoe, list1(coe))))
    } else {
      lcoe2(
        exp_,
        cddr(p),
        last(
          rplacd(
            lcoe,
            append(
              share_sym__make_list(num_sub(precedexp, one_plus(exp_)), int(0)),
              list1(coe),
            ),
          ),
        ),
      )
    }
  }
}

///|
fn binomial(n : Value, p : Value) -> Value raise {
  meval(list3(list1(q_p_binomial), n, p))
}

///|
/// la fonction maxote est commune a : treillis.lsp , resolvante.lsp, kak.lsp
fn maxote(a : Value, b : Value) -> Value raise {
  if !plusp(b) {
    Nil
  } else if eql(int(1), b) {
    int(0)
  } else if eql(int(0), num_rem(a, b)) {
    num_sub(a, div(a, b))
  } else {
    num_sub(a, one_plus(num_div(a, b)))
  }
}

///|
fn init_share_util() -> Unit raise {
  share_sym__defmexpr(
    q_d_card_stab,
    "((lambda ()) ((mlist) $part $egal) ((mprog) (($operation)) (($card_stab_init) $part $egal)))",
    item_text="(($card_stab) $part $egal)",
  )
}
