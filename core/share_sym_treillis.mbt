// Port of share/sym/treillis.lisp: ALGORITHMES SUR LES PARTITIONS.

// TREILLIS DES PARTITIONS DE POIDS n dans l'ordre lexicographique

///|
fn d_treillis_init(n : Value) -> Value raise {
  macsy_list(treillis(n))
}

///|
fn treillis(n : Value) -> Value raise {
  let ltreillis = cons(Nil, Nil)
  treillis2(n, int(0), ltreillis, Nil) |> ignore
  cdr(ltreillis)
}

///|
/// p(i+1)^m=max(0,2pi-p(i+1)); p(i+1)^M = pi-1
fn treillis2(pui : Value, ote : Value, ltreillis : Value, poule : Value) -> Value raise {
  if eql(int(0), pui) {
    rplacd(ltreillis, list1(reverse(poule)))
  } else {
    treillis2(
      ote,
      num_max(int(0), num_sub(num_mul(int(2), ote), pui)),
      ltreillis,
      cons(num_sub(pui, ote), poule),
    )
    |> ignore
    let ote = one_plus(ote)
    if num_lt(ote, pui) {
      treillis2(pui, ote, last(ltreillis), poule)
    } else {
      Nil
    }
  }
}

// TREILLIS DES PARTITIONS DE POIDS ET LONGUEUR FIXE
// dans l'ordre lexicographique

///|
fn d_lgtreillis_init(p : Value, l : Value) -> Value raise {
  macsy_list(lgtreillis(p, l))
}

///|
fn lgtreillis(poids : Value, longueur : Value) -> Value raise {
  let lpart = cons(Nil, Nil)
  lgtreillis2(
    poids,
    num_sub(longueur, int(1)),
    num_sub(longueur, int(1)),
    maxote(poids, longueur),
    Nil,
    lpart,
  )
  |> ignore
  cdr(lpart)
}

///|
fn lgtreillis2(
  poids : Value,
  rlongueur : Value,
  ote : Value,
  maxote_ : Value,
  partition : Value,
  lpart : Value,
) -> Value raise {
  if minusp(rlongueur) {
    rplacd(lpart, list1(reverse(partition)))
  } else {
    lgtreillis2(
      ote,
      num_sub(rlongueur, int(1)),
      num_max(num_sub(rlongueur, int(1)), num_sub(num_mul(int(2), ote), poids)),
      maxote(ote, rlongueur),
      cons(num_sub(poids, ote), partition),
      lpart,
    )
    |> ignore
    if num_lt(ote, maxote_) {
      lgtreillis2(poids, rlongueur, one_plus(ote), maxote_, partition, last(lpart))
    } else {
      Nil
    }
  }
}

// PARTITIONS DE POIDS FIXE ET DE LONGUEUR BORNEE

///|
fn d_ltreillis_init(p : Value, l : Value) -> Value raise {
  macsy_list(ltreillis(p, l))
}

///|
fn ltreillis(poids : Value, longueur : Value) -> Value raise {
  let lpart = cons(Nil, Nil)
  ltreillis2(
    poids,
    num_sub(longueur, int(1)),
    int(0),
    maxote(poids, longueur),
    Nil,
    lpart,
  )
  |> ignore
  cdr(lpart)
}

///|
fn ltreillis2(
  poids : Value,
  rlongueur : Value,
  ote : Value,
  maxote_ : Value,
  partition : Value,
  lpart : Value,
) -> Value raise {
  if minusp(rlongueur) {
    rplacd(lpart, list1(reverse(partition)))
  } else {
    ltreillis2(
      ote,
      num_sub(rlongueur, int(1)),
      num_max(int(0), num_sub(num_mul(int(2), ote), poids)),
      maxote(ote, rlongueur),
      cons(num_sub(poids, ote), partition),
      lpart,
    )
    |> ignore
    if num_lt(ote, maxote_) {
      ltreillis2(poids, rlongueur, one_plus(ote), maxote_, partition, last(lpart))
    } else {
      Nil
    }
  }
}

///|
fn init_share_treillis() -> Unit raise {
  share_sym__defmexpr(
    q_d_treillis,
    "((lambda ()) ((mlist) $poids) ((mprog) (($operation)) (($treillis_init) $poids)))",
    item_text="(($treillis) $poids)",
  )
  share_sym__defmexpr(
    q_d_lgtreillis,
    "((lambda ()) ((mlist) $poids $longueur) ((mprog) (($operation)) (($lgtreillis_init) $poids $longueur)))",
    item_text="(($lgtreillis) $poids $longueur)",
  )
  share_sym__defmexpr(
    q_d_ltreillis,
    "((lambda ()) ((mlist) $poids $longueur) ((mprog) (($operation)) (($ltreillis_init) $poids $longueur)))",
    item_text="(($ltreillis) $poids $longueur)",
  )
}
