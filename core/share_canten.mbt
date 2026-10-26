// Port of share/tensor/canten.lisp: canonical simplification for itensor
// (CANTEN, CONCAN, IRPMON).

///|
/// `(when (eq t (brek n)) (break "n"))`: the debugging breakpoints of this
/// file. BREAK enters the Lisp debugger; the port raises a Lisp error.
fn canten__brk(n : Int) -> Unit raise {
  if eq(brek(int(n)), t) {
    lisp_error(n.to_string()) |> ignore
  }
}

///|
fn ndown(x : Value) -> Value raise {
  putprop(x, t, q_nodown)
}

///|
fn ndownl(l : Value) -> Value raise {
  mapcar(x => ndown(x), l)
}

///|
fn brek(i : Value) -> Value raise {
  if member_equal(i, symval(q_breaklist)).truthy() {
    t
  } else {
    Nil
  }
}

// This package blindly rearranges the indices of RPOBJs, even those for
// which such index mangling is forbidden, like our special tensors. To
// avoid this, we use a private version of RPOBJ that excludes special
// tensors like the Levi-Civita or Christoffel symbols

///|
fn specialrpobj(e : Value) -> Value raise {
  if atom(e) || atom(car(e)) {
    Nil
  } else {
    let m = member(caar(e), symval(q_christoffels))
    if m.truthy() {
      m
    } else {
      lbool(
        eq(caar(e), q_d_kdelta) ||
        eq(caar(e), q_p_kdelta) ||
        eq(caar(e), q_d_levi_civita) ||
        eq(caar(e), q_p_levi_civita),
      )
    }
  }
}

///|
fn reallyrpobj(e : Value) -> Value raise {
  if specialrpobj(e).truthy() {
    Nil
  } else {
    rpobj(e)
  }
}

///|
/// L IS A LIST OF FACTORS WHICH RPOBS SEPARATES INTO A LIST OF TWO LISTS.
/// THE FIRST IS A LIST OF THE RPOBECTS IN L. THE SECOND IS A LIST OF NON-RP
/// OBJECTS
fn rpobs(l : Value) -> Value raise {
  let mut y : Value = Nil
  let mut z : Value = Nil
  for x in l.iter() {
    // DO steps Y and Z in parallel from the old values
    let r = reallyrpobj(x).truthy()
    let ny = if r { append(list1(x), y) } else { y }
    let nz = if r { z } else { append(list1(x), z) }
    y = ny
    z = nz
  }
  cons(y, list1(z))
}

///|
fn fre(l : Value) -> Value raise {
  intersect(l, symval(q_frei))
}

///|
fn boun(l : Value) -> Value raise {
  intersect(l, symval(q_bouni))
}

///|
fn grade(rp : Value) -> Value raise {
  int(length(covi(rp)) + length(conti(rp)) + length(deri(rp)))
}

///|
/// MON IS A MONOMIAL WHOSE "APPARENT" RANK IS ARANK
fn arank(mon : Value) -> Value raise {
  let mut i = 0
  for x in cdr(mon).iter() {
    i = length(allind(x)) + i
  }
  int(i)
}

///|
fn eqarank(m1 : Value, m2 : Value) -> Value raise {
  lbool(num_eq(arank(m1), arank(m2)))
}

///|
/// RP1 AND RP2 ARE RPOBJECTS WITH THE SAME GRADE
fn alphadi(rp1 : Value, rp2 : Value) -> Value raise {
  alphalessp(catenate(indlis(rp1)), catenate(indlis(rp2)))
}

///|
fn catenate(lis : Value) -> Value raise {
  implode(exploden(lis))
}

///|
fn indlis(rp : Value) -> Value raise {
  append_n([
    sort_list(
      append_n([fre(covi(rp)), fre(conti(rp)), fre(deri(rp))]),
      (a, b) => alphalessp(a, b).truthy(),
    ),
    list1(caar(rp)),
    sort_list(
      append_n([boun(covi(rp)), boun(conti(rp)), boun(deri(rp))]),
      (a, b) => alphalessp(a, b).truthy(),
    ),
  ])
}

///|
fn asort(l : Value, p : Value) -> Value raise {
  if length(l) < 2 {
    return l
  }
  let mut i = 0
  let mut j = 0
  let k = length(l)
  let az = make_array([k])
  fillarray(az, l) |> ignore
  while true {
    if j == k - 1 {
      return listarray(az)
    } else if i == k - 1 {
      i = 0
    } else if apply(p, list2(aref1(az, i), aref1(az, i + 1))).truthy() {
      i = i + 1
      j = j + 1
    } else if apply(p, list2(aref1(az, i + 1), aref1(az, i))).truthy() {
      permute(az, int(i), int(i + 1)) |> ignore
      i = i + 1
      j = 0
    } else {
      // the COND falls through: the PROG returns NIL
      return Nil
    }
  }
  Nil
}

///|
fn permute(arra : Value, i : Value, j : Value) -> Value raise {
  let x = aref1(arra, to_int(i))
  aset1(arra, to_int(i), aref1(arra, to_int(j))) |> ignore
  aset1(arra, to_int(j), x) |> ignore
  Nil
}

///|
fn prank(rp1 : Value, rp2 : Value) -> Value raise {
  if num_gt(grade(rp1), grade(rp2)) {
    t
  } else if equal(grade(rp1), grade(rp2)) {
    alphadi(rp1, rp2)
  } else {
    Nil
  }
}

///|
fn sa(x : Value) -> Value raise {
  sort_list(copy_list(x), (a, b) => alphalessp(a, b).truthy())
}

///|
fn top(rp : Value) -> Value raise {
  cdaddr(rp)
}

///|
fn bot(rp : Value) -> Value raise {
  append(cdadr(rp), cdddr(rp))
}

///|
fn allind(rp : Value) -> Value raise {
  if reallyrpobj(rp) is Nil {
    Nil
  } else {
    append_n([cdadr(rp), cdaddr(rp), cdddr(rp)])
  }
}

///|
/// MON IS A MONOMIAL WHOSE FACTORS ARE ANYBODY
/// $IRPMON AND IRPMON RETURN LIST IS FREE AND DUMMY INDICES
fn d_irpmon(mon : Value) -> Value raise {
  let mut l = cdr(mon)
  let mut cf = car(l)
  let mut dum : Value = Nil
  let mut free : Value = Nil
  let mut cl = allind(cf)
  let smlist = symval(q_smlist)
  while true {
    if l is Nil {
      canten__brk(19)
      return append_n([list1(smlist), la(list1(smlist), free), la(list1(smlist), dum)])
    } else if cl is Nil {
      canten__brk(18)
      l = cdr(l)
      cf = car(l)
      cl = allind(cf)
    } else {
      let ci = car(cl)
      if memq(ci, free) is Nil {
        canten__brk(17)
        free = endcons(ci, free)
        cl = cdr(cl)
      } else {
        canten__brk(16)
        free = comp(free, list1(ci))
        dum = endcons(ci, dum)
        cl = cdr(cl)
      }
    }
  }
  Nil
}

///|
fn irpmon(mon : Value) -> Value raise {
  let mut l = cdr(mon)
  let mut cf = car(l)
  let mut dum : Value = Nil
  let mut free : Value = Nil
  let mut unio : Value = Nil
  let mut cl = allind(cf)
  while true {
    if l is Nil {
      canten__brk(15)
      free = comp(unio, dum)
      dum = comp(unio, free)
      return append(list1(free), list1(dum))
    } else if cl is Nil {
      canten__brk(14)
      l = cdr(l)
      cf = car(l)
      cl = allind(cf)
    } else {
      let ci = car(cl)
      if memq(ci, unio) is Nil {
        canten__brk(13)
        unio = endcons(ci, unio)
        cl = cdr(cl)
      } else {
        canten__brk(12)
        dum = endcons(ci, dum)
        cl = cdr(cl)
      }
    }
  }
  Nil
}

///|
/// THE ARGUMENT E IS A PRODUCT OF FACTORS SOME OF WHICH ARE NOT RPOBJECTS.
/// THE FUNCTION RPOBS SEPARATES THESE AND PUTS THEM INTO NRPFACT. THE
/// RPFACTORS ARE SORTED AND PUT IN A
fn redcan(e : Value) -> Value raise {
  canten__brk(6)
  let nrpfact = cadr(rpobs(cdr(e)))
  let d = irpmon(e)
  set(q_frei, car(d)) |> ignore
  set(q_bouni, cadr(d)) |> ignore
  let a = sort_list(append(car(rpobs(cdr(e))), Nil), (x, y) => prank(x, y).truthy())
  let l = length(a)
  let b = make_array([l])
  let c = make_array([l, 4])
  fillarray(b, a) |> ignore
  canten__brk(7)
  for i in 0..<l {
    aset(c, [i, 0], name(aref1(b, i))) |> ignore
    aset(c, [i, 1], conti(aref1(b, i))) |> ignore
    aset(c, [i, 2], covi(aref1(b, i))) |> ignore
    aset(c, [i, 3], deri(aref1(b, i))) |> ignore
  }
  let mut ocil : Value = Nil
  for i in 0..<l {
    ocil = append(aref(c, [i, 3]), ocil)
  }
  ocil = append_n([ocil, aref(c, [0, 2]), car(d)])
  let mut ct = 0
  let mut cil = aref(c, [ct, 1])
  let mut cci = car(cil)
  aset(c, [ct, 1], Nil) |> ignore
  while true {
    if ct == l - 1 {
      canten__brk(1)
      aset(c, [ct, 1], cil) |> ignore
      let mut lis = apdval(c, Fix(0L))
      let mut i = 0
      while i != l - 1 {
        lis = append(lis, apdval(c, int(i + 1)))
        i = i + 1
      }
      return append(nrpfact, lis)
    } else if zl_get(aref(c, [ct, 0]), q_nodown).truthy() {
      aset(c, [ct, 1], cil) |> ignore
      ct = ct + 1
      cil = aref(c, [ct, 1])
      ocil = append(aref(c, [ct, 2]), ocil)
      aset(c, [ct, 1], Nil) |> ignore
    } else if cil is Nil {
      canten__brk(2)
      ct = ct + 1
      cil = aref(c, [ct, 1])
      ocil = append(aref(c, [ct, 2]), ocil)
      aset(c, [ct, 1], Nil) |> ignore
    } else {
      cci = car(cil)
      canten__brk(5)
      if memq(cci, ocil) is Nil {
        canten__brk(3)
        let mut coi = ct + 1
        while memq(cci, aref(c, [coi, 2])) is Nil {
          coi = coi + 1
        }
        aset(c, [ct, 2], cons(cci, aref(c, [ct, 2]))) |> ignore
        aset(c, [coi, 1], cons(cci, aref(c, [coi, 1]))) |> ignore
        aset(c, [coi, 2], comp(aref(c, [coi, 2]), list1(cci))) |> ignore
        ocil = cons(cci, ocil)
        cil = cdr(cil)
      } else {
        canten__brk(4)
        aset(c, [ct, 1], cons(cci, aref(c, [ct, 1]))) |> ignore
        cil = cdr(cil)
      }
    }
  }
  Nil
}

///|
fn la(x : Value, y : Value) -> Value raise {
  list1(append(x, y))
}

///|
fn apdval(c : Value, i : Value) -> Value raise {
  let i = to_int(i)
  let smlist = symval(q_smlist)
  list1(
    append_n([
      list1(cons(aref(c, [i, 0]), list1(q_simp))),
      la(list1(smlist), sa(aref(c, [i, 2]))),
      la(list1(smlist), sa(aref(c, [i, 1]))),
      sa(aref(c, [i, 3])),
    ]),
  )
}

///|
fn canform(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if rpobj(e).truthy() {
    e
  } else if eq(caar(e), q_mtimes) && length(car(rpobs(cdr(e)))) == 0 {
    e
  } else if eq(caar(e), q_mtimes) {
    cons(list1(q_mtimes), redcan(e))
  } else if eq(caar(e), q_mplus) {
    mysubst0(
      simplus(
        cons(
          list1(q_mplus),
          mapcar(
            v => cons(list1(q_mplus), canarank(v)),
            strata(cdr(e), q_eqarank),
          ),
        ),
        Fix(1L),
        Nil,
      ),
      e,
    )
  } else {
    e
  }
}

///|
fn endcons(x : Value, l : Value) -> Value raise {
  reverse(cons(x, reverse(l)))
}

///|
fn comp(x : Value, y : Value) -> Value raise {
  // patch for case when Y is not a list
  let z = if atom(y) { list1(y) } else { y }
  let mut a : Value = Nil
  for v in x.iter() {
    if member_equal(v, z) is Nil {
      a = endcons(v, a)
    }
  }
  a
}

///|
fn apdunion(x : Value, y : Value) -> Value raise {
  let mut a = x
  for v in y.iter() {
    if member_equal(v, a) is Nil {
      a = endcons(v, a)
    }
  }
  a
}

///|
/// LIST IS A LIST OF CANFORMED MONOMIALS OF THE SAME ARANK
/// CANARANK FINDS THE EQUIVALENT ONES
fn canarank(lis : Value) -> Value raise {
  let mut a = lis
  let mut b : Value = Nil
  let mut c = cdr(a)
  let mut d = make_array([length(a)])
  let mut ct = canform(car(a))
  let mut cnt = canform(car(c))
  let mut i = 1
  fillarray(d, a) |> ignore
  while true {
    if a is Nil {
      return b
    } else if cdr(a) is Nil && c is Nil {
      b = cons(ct, b)
      return b
    } else if c is Nil {
      canten__brk(9)
      b = cons(ct, b)
      aset1(d, 0, Nil) |> ignore
      a = comp(listarray(d), list1(Nil))
      c = cdr(a)
      i = 1
      ct = canform(car(a))
      cnt = canform(car(c))
      if a is Nil {
        return b
      } else {
        d = make_array([length(a)])
        fillarray(d, a) |> ignore
      }
    } else if samestruc(ct, cnt).truthy() {
      canten__brk(10)
      b = cons(canform(transform(cnt, ct)), b)
      aset1(d, i, Nil) |> ignore
      c = cdr(c)
      cnt = canform(car(c))
      i = i + 1
    } else {
      canten__brk(11)
      c = cdr(c)
      cnt = canform(car(c))
      i = i + 1
    }
  }
  Nil
}

///|
/// M1,M2 ARE (CANFORMED) MONOMIALS WHOSE INDEX STRUCTURE MAY BE THE SAME
fn samestruc(m1 : Value, m2 : Value) -> Value raise {
  lbool(equal(indstruc(m1), indstruc(m2)))
}

///|
/// MON IS (MTIMES) A LIST OF RP AND NON-RP FACTORS IN A MONOMIAL. THE NEXT
/// FUNCTION RETURNS A LIST WHOSE ELEMENTS ARE 4-ELEMENT LISTS GIVING THE
/// NAME (MON) AND THE LENGTHS OF THE COVARIANT,CONTRAVARIANT,DERIVATIVE
/// INDICES.
fn indstruc(mon : Value) -> Value raise {
  let mut b : Value = Nil
  for x in cdr(mon).iter() {
    if reallyrpobj(x).truthy() {
      b = append(b, list1(findstruc(x)))
    }
  }
  b
}

///|
/// FACT IS AN RP FACTOR IN MON. HERE WE FIND ITS INDEX STRUCTURE
fn findstruc(fact : Value) -> Value raise {
  list4(
    caar(fact),
    int(length(cdadr(fact))),
    int(length(cdaddr(fact))),
    int(length(cdddr(fact))),
  )
}

///|
/// M1,M2 ARE MONOMIALS WITH THE SAMESTRUC TURE. THE NEXT FUNCTION
/// TRANSFORMS (PERMUTES) THE FORM OF M1 INTO M2.
fn transform(m1 : Value, m2 : Value) -> Value raise {
  sublis(findperm(m1, m2), m1)
}

///|
fn strata(lis : Value, p : Value) -> Value raise {
  if lis is Nil || cdr(lis) is Nil {
    return list1(lis)
  }
  let mut l = lis
  let mut cs : Value = Nil
  let mut bl : Value = Nil
  while true {
    if l is Nil {
      canten__brk(1)
      return if cs is Nil { bl } else { endcons(cs, bl) }
    } else if cdr(l) is Nil && cs is Nil {
      canten__brk(2)
      bl = endcons(list1(car(l)), bl)
      return bl
    } else if cdr(l) is Nil && cs.truthy() {
      canten__brk(3)
      return if funcall(p, [car(l), car(cs)]).truthy() {
        cs = cons(car(l), cs)
        bl = endcons(cs, bl)
        bl
      } else {
        bl = endcons(list1(car(l)), endcons(cs, bl))
        bl
      }
    } else if cs is Nil {
      canten__brk(4)
      cs = list1(car(l))
      l = cdr(l)
    } else if funcall(p, [car(l), car(cs)]).truthy() {
      canten__brk(5)
      cs = cons(car(l), cs)
      l = cdr(l)
    } else {
      canten__brk(6)
      bl = endcons(cs, bl)
      cs = list1(car(l))
      l = cdr(l)
    }
  }
  Nil
}

///|
fn tindstruc(mon : Value) -> Value raise {
  let mut b : Value = Nil
  for x in cdr(mon).iter() {
    if reallyrpobj(x).truthy() {
      b = append(b, tfindstruc(x))
    }
  }
  b
}

///|
fn tfindstruc(fact : Value) -> Value raise {
  append_n([cdadr(fact), cdaddr(fact), cdddr(fact)])
}

///|
fn dumm(x : Value) -> Value raise {
  lbool(equal(cadr(explodec(x)), symval(q_d_idummyx)))
}

///|
fn findpermut(i1 : Value, i2 : Value) -> Value raise {
  // (mapcar 'pij i1 i2) stops at the shorter list
  let c = Collector::new()
  let mut a = i1
  let mut b = i2
  while a.truthy() && b.truthy() {
    c.add(pij(car(a), car(b)))
    a = cdr(a)
    b = cdr(b)
  }
  comp(c.result(), list1(Nil))
}

///|
fn pij(x : Value, y : Value) -> Value raise {
  if dumm(x).truthy() && dumm(y).truthy() && !eq(x, y) {
    cons(x, y)
  } else {
    Nil
  }
}

///|
/// (SAMESTRUC M1 M2) IS T FOR THE ARGUMENTS BELOW
/// THE RESULTING PERMUTATION IS GIVEN TO TRANSFORM
fn findperm(m1 : Value, m2 : Value) -> Value raise {
  let d1 = cadr(irpmon(m1))
  let d2 = cadr(irpmon(m2))
  let mut i1 = tindstruc(m1)
  let mut i2 = tindstruc(m2)
  let mut l : Value = Nil
  while i1.truthy() {
    if memq(car(i1), d1).truthy() &&
      memq(car(i2), d2).truthy() &&
      !eq(car(i1), car(i2)) &&
      memq(car(i1), car(l)) is Nil &&
      memq(car(i2), cadr(l)) is Nil {
      l = cons(endcons(car(i1), car(l)), list1(endcons(car(i2), cadr(l))))
    }
    i1 = cdr(i1)
    i2 = cdr(i2)
  }
  // (mapcar 'cons a b) stops at the shorter list
  let c = Collector::new()
  let mut a = append(car(l), comp(d1, car(l)))
  let mut b = append(cadr(l), comp(d2, cadr(l)))
  while a.truthy() && b.truthy() {
    c.add(cons(car(a), car(b)))
    a = cdr(a)
    b = cdr(b)
  }
  c.result()
}

///|
fn d_canten(x : Value) -> Value raise {
  if symval(q_d_allsym) is Nil {
    merr("canten works only if allsym:true has been set", [])
  } else {
    let mut i = d_nterms(x)
    let mut l = canform(x)
    while !num_eq(i, d_nterms(l)) {
      if eq(symval(q_d_canterm), t) {
        print(i) |> ignore
      }
      i = d_nterms(l)
      l = canform(l)
    }
    l
  }
}

///|
fn d_concan(x : Value) -> Value raise {
  if symval(q_d_allsym) is Nil {
    merr("concan works only if allsym:true has been set", [])
  } else {
    let mut i = d_nterms(x)
    let mut l = canform(x)
    while !num_eq(i, d_nterms(l)) {
      if eq(symval(q_d_canterm), t) {
        print(i) |> ignore
      }
      i = d_nterms(l)
      l = d_contract(canform(l))
    }
    l
  }
}

///|
/// Top-level forms of canten.lisp.
fn init_share_canten() -> Unit raise {
  ndownl(symval(q_nodown)) |> ignore
  set(q_breaklist, Nil) |> ignore
  set(q_d_canterm, Nil) |> ignore
}
