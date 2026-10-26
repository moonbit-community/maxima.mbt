// Port of share/sym/permut.lisp: OBTENIR TOUTES LES PERMUTATIONS D'UN
// NUPLET D'ENTIER.

///|
fn d_permut(nuplet : Value) -> Value raise {
  cons(
    list1(q_mlist),
    mapcar(permu => cons(list1(q_mlist), permu), permut(cdr(nuplet))),
  )
}

///|
/// On place le car dans toutes les positions possibles; des () viennent
/// la'-dedans a' cause de insert : je les ote avec vire_nil; des
/// re'pe'titions malgre_tout: je vais les e'liminer par un_de_chaque
fn insertion(a : Value, l : Value, i : Value) -> Value raise {
  if l is Nil {
    list1(a)
  } else if equal(nth(to_int(i), l), a) {
    Nil
  } else {
    append_n([schur_firstn(i, l), list1(a), share_sym__nthcdr(i, l)])
  }
}

///|
/// dans la liste L il y a peut - etre des () au top niveau : je les vire
fn vire_nil(l : Value) -> Value raise {
  let c = Collector::new()
  for x in l.iter() {
    if x is Cons(_) {
      c.add(x)
    }
  }
  c.result()
}

///|
/// ne garde que les e'le'ments de L 2 a' 2 distincts au top niveau
fn un_de_chaque(l : Value) -> Value raise {
  let c = Collector::new()
  let mut p = l
  while p is Cons(_) {
    if member_equal(car(p), cdr(p)) is Nil {
      c.add(car(p))
    }
    p = cdr(p)
  }
  c.result()
}

///|
/// retourne la liste de toutes les permutations de L
/// ex : ( permut '(1 1 2 2 3 3)) donne la liste des 90 positions concerne'es
fn permut(l : Value) -> Value raise {
  if length(l) <= 1 {
    return list1(l)
  }
  let relais = permut(cdr(l))
  let a = car(l)
  let mut reponse : Value = Nil
  let n = length(l)
  for i in 0..<n {
    reponse = append(reponse, mapcar(z => insertion(a, z, int(i)), relais))
  }
  un_de_chaque(vire_nil(reponse))
}

///|
fn init_share_permut() -> Unit raise {
  ()
}
