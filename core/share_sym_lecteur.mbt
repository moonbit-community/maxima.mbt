// Port of share/sym/lecteur.lisp: LE LECTEUR DANS k[y1, ... ,yn][x1, ... ,xp]
// rendant la forme distribuee du polynome pol.
// constante = [constante, 0, ...,0] avec p exposants nuls

///|
fn d_distri_lect(d_pol : Value, d_lvar : Value) -> Value raise {
  if share_sym__is_equal(d_pol, int(0)) {
    cons(list1(q_mlist), Nil)
  } else {
    cons(
      list1(q_mlist),
      mapcar(mon => cons(list1(q_mlist), mon), distri_lect(d_pol, cdr(d_lvar))),
    )
  }
}

///|
/// lvar =(x1 x2 .... xp) les yi inconnus.
/// on prend uniquement le cdr pour trier car le car est le coefficient;
/// on ordonne dans l'ordre lexicographique decroissant.
fn distri_lect(d_pol : Value, lvar : Value) -> Value raise {
  // LVAR is special: EXPOMON reads it
  with_special(q_lvar, lvar, () => somme_coef(
    sort_list(exposants(d_expand(d_pol), lvar), (a, b) => lex_mon(cdr(a), cdr(b)).truthy()),
  ))
}

///|
fn somme_coef(pol_dist : Value) -> Value raise {
  if pol_dist is Cons(_) {
    somme_coef2(
      caar(pol_dist), // le coefficient initial
      cdar(pol_dist), // le monome initial
      pol_dist,
    )
    |> ignore
  }
  pol_dist
}

///|
fn somme_coef2(c : Value, m : Value, pol_dist : Value) -> Value raise {
  let mut c = c
  let mut m = m
  let mut pol_dist = pol_dist
  while cdr(pol_dist) is Cons(_) {
    let c2 = caar(cdr(pol_dist))
    let m2 = cdar(cdr(pol_dist))
    if equal(m, m2) {
      c = share_sym__add(c, c2)
      pol_dist = rplacd(pol_dist, cddr(pol_dist))
    } else {
      rplaca(car(pol_dist), c) |> ignore
      c = c2
      m = m2
      pol_dist = cdr(pol_dist)
    }
  }
  rplaca(car(pol_dist), c)
}

///|
fn exposants(pol : Value, lvar : Value) -> Value raise {
  with_special(q_lvar, lvar, () => if listp(pol) && equal(q_mplus, caar(pol)) {
    mapcar(x => expomon(x), cdr(pol))
  } else {
    list1(expomon(pol))
  })
}

///|
/// Franz Lisp REMPROP: remove the property and return the tail of the
/// plist starting at it (or NIL).
fn share_sym_lecteur__remprop(s : Value, indic : Value) -> Value raise {
  let mut pl = symbol_plist(s)
  let mut result : Value = Nil
  while pl is Cons(_) {
    if eq(car(pl), indic) {
      result = pl
      break
    }
    pl = cddr(pl)
  }
  remprop(s, indic) |> ignore
  result
}

///|
/// lecture d'un mono^me : Soit un mono^me dans k[x1,...,xn] ou` k est
/// e'ventuellement un anneau de polyno^mes sur un corps. On construit une
/// plist 'var_coe : si c'est un e'le'ment du corps on le met a l'indicateur
/// : coe; si c'est un variable on met l'exposant avec comme indicateur la
/// variable. Ensuite cre'e' la liste des valeurs lie'es aux variables xi
/// dans la pliste et on fait le produit des autres valeurs de cette plist.
/// Si on a une constante C sur k on la represente par [C,0,0,...,0].
fn expomon(mon : Value) -> Value raise {
  let lvar = symval(q_lvar)
  if numberp(mon) {
    // on a une cste de k uniquement
    if !zerop(mon) {
      cons(mon, share_sym__make_list(int(length(lvar)), int(0)))
    } else {
      Nil
    }
  } else {
    if listp(mon) && equal(q_mtimes, caar(mon)) {
      if !(
          (listp(cadr(mon)) && equal(q_mexpt, caar(cadr(mon)))) ||
          member_equal(cadr(mon), lvar).truthy()
        ) {
        // le coefficient, eventuellement rationnel, est different de 1
        mapc(x => lvarexpo(x) |> ignore, cddr(mon)) |> ignore
        setf_get(q_var_expo, q_coe, cadr(mon)) |> ignore
      } else {
        // le coefficient est e'gal a 1
        mapc(x => lvarexpo(x) |> ignore, cdr(mon)) |> ignore
        setf_get(q_var_expo, q_coe, int(1)) |> ignore
      }
    } else {
      // on a ((mexpt) x 4) ou x:
      lvarexpo(mon) |> ignore
      setf_get(q_var_expo, q_coe, int(1)) |> ignore
    }
    // maintenant toutes les donnees sont dans la plist
    // reste a bien recoller les morceaux
    let ncoe = cadr(share_sym_lecteur__remprop(q_var_expo, q_coe))
    let exposant = expomon2(lvar)
    // on n'a retire que les exposants des xi et le coefficient
    // numerique de la plist, reste les yi et leur exposants
    // a remettre en coefficients.
    cons(recupcoef(symbol_plist(q_var_expo), ncoe), exposant)
  }
}

///|
fn recupcoef(plist : Value, coef : Value) -> Value raise {
  let mut plist = plist
  let mut coef = coef
  while plist is Cons(_) {
    let yi = car(plist)
    let next = cddr(plist)
    coef = share_sym__mult(
      share_sym__exp(yi, cadr(share_sym_lecteur__remprop(q_var_expo, yi))),
      coef,
    )
    plist = next
  }
  coef
}

///|
/// Representation MACSYMA, mmon, de x**i : x si i=1, ((mexpt) x i) sinon;
/// on veut recuperer (x i) et mettre la valeur i pour l'indicateur x
/// dans la plist var_expo.
fn lvarexpo(mmon : Value) -> Value raise {
  if atom(mmon) {
    setf_get(q_var_expo, mmon, int(1))
  } else {
    setf_get(q_var_expo, cadr(mmon), caddr(mmon))
  }
}

///|
/// recuperation de la liste des exposants associee aux variables de lvar :
fn expomon2(lvar : Value) -> Value raise {
  mapcar(
    var_ => chercheexpo(cdr(share_sym_lecteur__remprop(q_var_expo, var_))),
    lvar,
  )
}

///|
fn chercheexpo(expo : Value) -> Value raise {
  if expo is Nil {
    int(0)
  } else {
    car(expo)
  }
}

///|
fn init_share_lecteur() -> Unit raise {
  ()
}
