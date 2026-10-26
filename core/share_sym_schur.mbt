// Port of share/sym/schur.lisp: FONCTIONS DE SCHUR et CHANGEMENTS DE BASES.

// PASSAGE DES FONCTIONS DE SCHUR AUX FONCTIONS COMPLETES
// On se donne un polyno^me en h1, h2, ... repre'sentant un polyno^me
// en les fonctions comple`tes. On recupere une liste dont chaque element
// est une liste dont le premier terme est un entier et le reste une
// partition renversee representant la fonction de Schur associ\'ee.
// REP(partition) = [partition](1)

///|
fn d_schur2comp_init(d_comp : Value, d_listofvars : Value) -> Value raise {
  if eql(q_d_pol, symval(q_d_schur2comp)) {
    schur2comp_pol(d_comp, cdr(d_listofvars))
  } else {
    cons(
      list1(q_mlist),
      schur2comp(ch2rep(sort_list(cdr(d_comp), (a, b) => num_gt(a, b)))),
    )
  }
}

///|
/// Si la donnee est un polynome en les fonctions completes.
/// schur2comp rend '(mlist) en tete de chaque terme partitionne
/// le coefficient est donc en cadr
fn schur2comp_pol(d_pol : Value, listofvars : Value) -> Value raise {
  let mut polpart = pol2part(d_pol, listofvars)
  let mut sol = int(0)
  while polpart is Cons(_) {
    let pp = polpart
    sol = share_sym__add(
      share_sym__fadd(
        mapcar(
          l => {
            let coef = caar(pp)
            share_sym__fmult(
              list3(cadr(l), coef, cons(list2(q_d_s, q_array), cddr(l))),
            )
          },
          schur2comp(cdar(pp)),
        ),
      ),
      sol,
    )
    polpart = cdr(polpart)
  }
  sol
}

///|
/// Ordre Lexicographique pour des polynomes partitionnes de type 1.
/// l'egalite ne nous importe pas.
fn lexinv_type1(terme1 : Value, terme2 : Value) -> Value raise {
  n2lexinv_type1(cddr(terme1), cddr(terme2))
}

///|
fn n2lexinv_type1(n1part : Value, n2part : Value) -> Value raise {
  let mut a = n1part
  let mut b = n2part
  while true {
    if car(a) is Nil {
      return Nil
    }
    if car(b) is Nil {
      return t
    }
    if num_lt(car(a), car(b)) {
      return Nil
    }
    if num_gt(car(a), car(b)) {
      return t
    }
    a = cdr(a)
    b = cdr(b)
  }
  Nil
}

///|
/// pol2part permet a` partir d'un polynome en les monomes
/// h^a = h1^a1 ... hn^an
/// de recuperer la partition [1,a1,2,a2,...,n,an] sous type 2 (cf. structure)
/// en representation creuse ,i.e. si hi=0 on ne retrouve par le couple (i,ai).
fn pol2part(d_pol : Value, listofvar : Value) -> Value raise {
  let mut i = int(0)
  let varetdegre = chvaretdegre(listofvar)
  mapcar(
    l => {
      i = one_plus(cdr(varetdegre))
      cons(
        car(l),
        mapcan(
          nb => {
            i = one_minus(i)
            if !eql(nb, int(0)) {
              list2(i, nb)
            } else {
              Nil
            }
          },
          nreverse(cdr(l)),
        ),
      )
    },
    lect(
      d_pol,
      cons(
        q_aa,
        lvar_lettre(
          cdr(varetdegre),
          Nil,
          share_sym__concat([Str("$"), car(varetdegre)]),
        ),
      ),
    ),
  )
}

///|
/// The letter and the largest index of the variables (h1 ... hn) of
/// LISTOFVAR: (h . n).
fn chvaretdegre(listofvar : Value) -> Value raise {
  // (franz.exploden (car (last (sort listofvar 'string-lessp)))): the
  // characters of the printed name of the greatest variable; its first
  // character (the "$") is dropped.
  let sorted = sort_list(listofvar, (a, b) => string_compare(
      string_upcase(symbol_name(a)),
      string_upcase(symbol_name(b)),
    ) <
    0)
  let chars = string_chars(symbol_name(car(last(sorted))))
  let hj = chars[1:].to_owned()
  let mut i = int(1)
  let mut s = int(0)
  for k = hj.length() - 1; k >= 1; k = k - 1 {
    s = num_add(s, num_mul(i, int(hj[k].to_int() - 48)))
    i = num_mul(i, int(10))
  }
  cons(sym(hj[0].to_string()), s)
}

///|
/// si au depart on a REP[part]=[partition](2), en sortie
/// REP[part]=[partition](1) mais sous forme ( ((mlist).termpart) ...)
fn schur2comp(part : Value) -> Value raise {
  let part1 = ch1rep(part)
  mapcar(
    n2part => cons(list1(q_mlist), cons(kostka(n2part, part1), reverse(n2part))),
    mapcar(x => ch1rep(x), treinat(part)),
  )
}

// PASSAGE DES FORMES MONOMIALES AUX FONCTIONS DE SCHUR
// On donne une partition renversee repre'sentant une fonction de Schur
// on recupere un polynome symetrique contracte.

///|
fn d_mon2schur_init(d_rpart : Value) -> Value raise {
  let part = reverse(cdr(d_rpart))
  let mut s = int(0)
  for x in cdr(d_rpart).iter() {
    s = num_add(s, x)
  }
  let lvar_ = lvar(s, Nil)
  share_sym__fadd(
    cons(
      int(0),
      mapcar(
        n2part => ecrit_mon(n2part, lvar_, kostka(part, n2part)),
        mapcar(x => duale21(x), treinat(duale12(part))),
      ),
    ),
  )
}

///|
/// etant donne un partition de representation [partition](1), on
/// recupere sa forme duale sous forme [partition](2)
fn duale12(partition : Value) -> Value raise {
  let mut ai = int(0)
  let c = Collector::new()
  let mut restpart = partition
  while restpart is Cons(_) {
    ai = one_plus(ai)
    let piece = if cdr(restpart) is Nil {
      append(restpart, list1(ai))
    } else {
      let mi = num_sub(car(restpart), cadr(restpart))
      if num_lt(int(0), mi) {
        list2(mi, ai)
      } else {
        Nil
      }
    }
    c.append_list(piece)
    restpart = cdr(restpart)
  }
  nreverse(c.result())
}

///|
/// etant donne un partition de representation [partition](2), on
/// recupere sa forme duale sous forme [partition](1)
fn duale21(partition : Value) -> Value raise {
  let lmultiplicites_lparts = chmultiplicites_parts(partition, Nil, Nil)
  n2duale21(
    car(lmultiplicites_lparts),
    cons(int(0), cdr(lmultiplicites_lparts)),
    Nil,
  )
}

///|
fn n2duale21(
  lmulti : Value,
  lpart : Value,
  partition1_duale : Value,
) -> Value raise {
  let mut lmulti = lmulti
  let mut lpart = lpart
  let mut acc = partition1_duale
  while cdr(lmulti) is Cons(_) {
    acc = nconc(
      acc,
      share_sym__make_list(
        num_sub(cadr(lpart), car(lpart)),
        share_sym__fadd(lmulti),
      ),
    )
    lmulti = cdr(lmulti)
    lpart = cdr(lpart)
  }
  nconc(
    acc,
    share_sym__make_list(num_sub(cadr(lpart), car(lpart)), car(lmulti)),
  )
}

///|
fn chmultiplicites_parts(
  partition : Value,
  lmulti : Value,
  lpart : Value,
) -> Value raise {
  let mut partition = partition
  let mut lmulti = lmulti
  let mut lpart = lpart
  while partition is Cons(_) {
    lmulti = cons(cadr(partition), lmulti)
    lpart = cons(car(partition), lpart)
    partition = cddr(partition)
  }
  cons(lmulti, lpart)
}

// NOMBRES DE KOSTKA (Algorithme : Philippe ESPERET)
// REP(partition) = [part](1)

///|
fn d_kostka_init(d_1part : Value, d_2part : Value) -> Value raise {
  kostka(cdr(d_1part), cdr(d_2part))
}

///|
fn kostka(l : Value, m : Value) -> Value raise {
  let mut s = int(0)
  for x in l.iter() {
    s = num_add(s, x)
  }
  int(length(good_tab0(l, share_sym__make_list(s, int(0)), m)))
}

///|
fn schur_firstn(n : Value, l : Value) -> Value raise {
  let c = Collector::new()
  let mut n = n
  let mut l = l
  while l is Cons(_) && plusp(n) {
    c.add(car(l))
    n = one_minus(n)
    l = cdr(l)
  }
  c.result()
}

///|
/// normalement cette fonction existe en Common  sous le nom de "last"
fn lastn(l : Value, n : Value) -> Value raise {
  nreverse(schur_firstn(n, reverse(l)))
}

///|
fn good_tab0(l : Value, lcont : Value, ltas : Value) -> Value raise {
  if length(l) == 1 {
    mapcar(x => list1(x), good_line(car(l), lcont, ltas))
  } else {
    let mut l1 = good_line(car(l), lcont, ltas)
    let mut rep : Value = Nil
    while l1 is Cons(_) {
      let relais = good_tab0(cdr(l), car(l1), new_tas0(car(l1), ltas))
      if relais is Nil {
        l1 = cdr(l1)
      } else {
        rep = nconc(rep, insert_tete(car(l1), relais))
        l1 = cdr(l1)
      }
    }
    rep
  }
}

///|
/// L liste de listes : retourne la meme liste ou les listes ont ete
/// modifiees par insertion de i en tete
fn insert_tete(i : Value, l : Value) -> Value raise {
  if l is Nil {
    list1(list1(i))
  } else {
    mapcar(z => cons(i, z), l)
  }
}

///|
/// ote du tas Ltas les elts de L1, Ltas=(3 2 1) cad 3 "1", 2 "2" et 1 "3"
fn new_tas0(l1 : Value, ltas : Value) -> Value raise {
  let mut l1 = l1
  let mut ltas = ltas
  while l1 is Cons(_) {
    let a = car(l1)
    ltas = append_n([
      schur_firstn(one_minus(a), ltas),
      list1(one_minus(nth(to_int(one_minus(a)), ltas))),
      lastn(ltas, num_sub(int(length(ltas)), a)),
    ])
    l1 = cdr(l1)
  }
  ltas
}

///|
fn good_line(taille : Value, lcontrainte : Value, ltas : Value) -> Value raise {
  good_length(taille, good_line0(taille, lcontrainte, ltas))
}

///|
fn good_line0(taille : Value, lcontrainte : Value, ltas : Value) -> Value raise {
  let lotas = int(length(ltas))
  let mut avanti = false
  let mut rep : Value = Nil
  if lcontrainte is Nil || zerop(taille) {
    return Nil
  }
  let mut i = one_plus(car(lcontrainte))
  while !num_lt(lotas, i) {
    if zerop(nth(to_int(one_minus(i)), ltas)) {
      i = one_plus(i)
    } else {
      rep = append(
        rep,
        insert_tete(
          i,
          good_line0(
            one_minus(taille),
            cdr(lcontrainte),
            append_n([
              share_sym__make_list(one_minus(i), int(0)),
              list1(one_minus(nth(to_int(one_minus(i)), ltas))),
              lastn(ltas, num_sub(lotas, i)),
            ]),
          ),
        ),
      )
      i = one_plus(i)
      avanti = true
    }
  }
  if avanti {
    rep
  } else {
    Nil
  }
}

///|
fn good_length(taille : Value, l : Value) -> Value raise {
  let c = Collector::new()
  for x in l.iter() {
    if eql(taille, int(length(x))) {
      c.add(x)
    }
  }
  c.result()
}

// TREILLIS DES PARTITIONS DANS L'ORDRE NATUREL
// ETANT DONNE UNE PARTITION I ON RAMENE LES PARTITIONS DE MEME
// POIDS INFERIEURES A I.
// REP(partition) = [part](1) en entree et en sortie

///|
fn d_treinat_init(d_partition1 : Value) -> Value raise {
  cons(
    list1(q_mlist),
    mapcar(
      part => cons(list1(q_mlist), ch1rep(part)),
      treinat(ch2rep(cdr(d_partition1))),
    ),
  )
}

///|
/// REP(partition) = [part](2) en entree et en sortie
fn treinat(part2 : Value) -> Value raise {
  soustreillisnat(list1(part2), Nil)
}

///|
/// prendre a chaque fois la plus petite dans l'ordre lexicographique
fn soustreillisnat(lpartnt : Value, lpartt : Value) -> Value raise {
  let mut lpartnt = lpartnt
  let mut lpartt = lpartt
  while lpartnt is Cons(_) {
    let nt = union_sym(
      cdr(lpartnt),
      sort_list(crefils_init(car(lpartnt)), (a, b) => d_lex(a, b).truthy()),
    )
    lpartt = cons(car(lpartnt), lpartt)
    lpartnt = nt
  }
  lpartt
}

///|
/// deux listes identiquement ordonnees par lex
fn union_sym(l1 : Value, l2 : Value) -> Value raise {
  let mut l2 = l2
  while true {
    if l2 is Nil {
      return l1
    }
    if l1 is Nil {
      return l2
    }
    if equal(car(l1), car(l2)) {
      l2 = cdr(l2)
      continue
    }
    if d_lex(car(l1), car(l2)).truthy() {
      union2(l1, l2) |> ignore
      return l1
    }
    union2(l2, l1) |> ignore
    return l2
  }
  Nil
}

///|
fn union2(l1 : Value, l2 : Value) -> Value raise {
  let mut l1 = l1
  let mut l2 = l2
  while true {
    if l2 is Nil {
      return Nil
    }
    if cdr(l1) is Nil {
      return rplacd(l1, l2)
    }
    let part1 = cadr(l1)
    let part2 = car(l2)
    if equal(part1, part2) {
      l2 = cdr(l2)
    } else if d_lex(part1, part2).truthy() {
      l1 = cdr(l1)
    } else {
      let ll1 = cdr(l1)
      l1 = cdr(rplacd(l1, l2))
      l2 = ll1
    }
  }
  Nil
}

///|
fn crefils_init(part : Value) -> Value raise {
  crefils(reverse(part), Nil, Nil)
}

///|
/// part = (an mn ... a2 m2 a1 m1) an > ... > a2 > a1
/// debut = (a(i-1) m(i-1) ... a1 m1)
/// rfin = (mi ai m(i+1) a(i+1) ...)
/// evite l'identite
fn crefils(rfin : Value, debut : Value, lfils : Value) -> Value raise {
  let mut rfin = rfin
  let mut debut = debut
  let mut lfils = lfils
  while rfin is Cons(_) {
    let ai = cadr(rfin)
    let mi = car(rfin)
    let rest = cddr(rfin)
    if rest is Nil && eql(int(1), mi) {
      return lfils
    }
    let nfils = cons(tombecube(rest, ai, mi, debut), lfils)
    debut = cons(ai, cons(mi, debut))
    rfin = rest
    lfils = nfils
  }
  lfils
}

///|
/// ai --> ai-1 et mi reste si ai > 1; disparition ai --> ai-1 = 0;
/// ai --> ai + 1 = 2; il en reste mi-2 egales a 1
fn tombecube(rfin : Value, ai : Value, mi : Value, debut : Value) -> Value raise {
  if eql(int(1), mi) {
    if eql(int(1), ai) {
      reverse(arrivecube(rfin))
    } else {
      nconc(reverse(arrivecube(rfin)), schur_met(one_minus(ai), debut))
    }
  } else if eql(int(1), ai) {
    if eql(int(2), mi) {
      reverse(rmet(int(2), rfin))
    } else {
      reverse(cons(num_sub(mi, int(2)), cons(int(1), rmet(int(2), rfin))))
    }
  } else if eql(int(2), mi) {
    nconc(reverse(rmet(one_plus(ai), rfin)), schur_met(one_minus(ai), debut))
  } else {
    nconc(
      reverse(cons(num_sub(mi, int(2)), cons(ai, rmet(one_plus(ai), rfin)))),
      schur_met(one_minus(ai), debut),
    )
  }
}

///|
/// rpart = (m a ...); aj = a(i-1) ==> m(i-1) --> m(i-1) +1
fn rmet(aj : Value, rpart : Value) -> Value raise {
  if rpart is Nil {
    list2(int(1), aj)
  } else if eql(aj, cadr(rpart)) {
    cons(one_plus(car(rpart)), cdr(rpart))
  } else {
    cons(int(1), cons(aj, rpart))
  }
}

///|
/// part = part2 sens croissant des parts
fn schur_met(aj : Value, part : Value) -> Value raise {
  if part is Nil {
    list2(aj, int(1))
  } else if eql(aj, car(part)) {
    cons(aj, cons(one_plus(cadr(part)), cddr(part)))
  } else {
    cons(aj, cons(int(1), part))
  }
}

///|
/// part = (mj aj ...) un aj passe a  aj+1; mj = 1
fn arrivecube(rpart : Value) -> Value raise {
  if eql(int(1), car(rpart)) {
    rmet(one_plus(cadr(rpart)), cddr(rpart))
  } else {
    cons(
      one_minus(car(rpart)),
      cons(cadr(rpart), rmet(one_plus(cadr(rpart)), cddr(rpart))),
    )
  }
}

///|
fn init_share_schur() -> Unit raise {
  share_sym__defmexpr(
    q_d_mon2schur,
    "((lambda ()) ((mlist) $part) ((mprog) (($operation)) (($mon2schur_init) $part)))",
    item_text="(($mon2schur) $part)",
  )
  share_sym__defmexpr(
    q_d_kostka,
    "((lambda ()) ((mlist) $part1 $part2) ((mprog) (($operation)) (($kostka_init) $part1 $part2)))",
    item_text="(($kostka) $part1 $part2)",
  )
  share_sym__defmexpr(
    q_d_treinat,
    "((lambda ()) ((mlist) $part) ((mprog) (($operation)) (($treinat_init) $part)))",
    item_text="(($treinat) $part)",
  )
  share_sym__defmexpr(
    q_d_schur2comp,
    "((lambda ()) ((mlist) $comp $listofvars) ((mprog) (($operation)) (($schur2comp_init) $comp $listofvars)))",
    item_text="(($schur2comp) $comp $listofvars)",
  )
}
