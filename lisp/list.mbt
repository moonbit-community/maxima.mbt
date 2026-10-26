///|
pub fn cons(a : Value, b : Value) -> Value {
  Cons({ car: a, cdr: b })
}

///|
/// `(consp x)`
pub fn consp(x : Value) -> Bool {
  x is Cons(_)
}

///|
/// `(atom x)`
pub fn atom(x : Value) -> Bool {
  !(x is Cons(_))
}

///|
/// `(listp x)`
pub fn listp(x : Value) -> Bool {
  x is (Nil | Cons(_))
}

///|
/// `(car x)`; car of nil is nil. Non-list arguments yield nil rather than an
/// error, which matches what Maxima code effectively relies on far more often
/// than it relies on the error.
pub fn car(x : Value) -> Value {
  match x {
    Cons(c) => c.car
    _ => Nil
  }
}

///|
pub fn cdr(x : Value) -> Value {
  match x {
    Cons(c) => c.cdr
    _ => Nil
  }
}

///|
/// Strict `car`: raises on non-lists.
pub fn car_strict(x : Value) -> Value raise LispError {
  match x {
    Cons(c) => c.car
    Nil => Nil
    _ => raise Condition(intern("type-error"), "\{x} is not a list", x)
  }
}

///|
pub fn cdr_strict(x : Value) -> Value raise LispError {
  match x {
    Cons(c) => c.cdr
    Nil => Nil
    _ => raise Condition(intern("type-error"), "\{x} is not a list", x)
  }
}

///|
pub fn caar(x : Value) -> Value {
  car(car(x))
}

///|
pub fn cadr(x : Value) -> Value {
  car(cdr(x))
}

///|
pub fn cdar(x : Value) -> Value {
  cdr(car(x))
}

///|
pub fn cddr(x : Value) -> Value {
  cdr(cdr(x))
}

///|
pub fn caddr(x : Value) -> Value {
  car(cdr(cdr(x)))
}

///|
pub fn cdddr(x : Value) -> Value {
  cdr(cdr(cdr(x)))
}

///|
pub fn cadddr(x : Value) -> Value {
  car(cdr(cdr(cdr(x))))
}

///|
pub fn cddddr(x : Value) -> Value {
  cdr(cdr(cdr(cdr(x))))
}

///|
pub fn caadr(x : Value) -> Value {
  car(car(cdr(x)))
}

///|
pub fn cadar(x : Value) -> Value {
  car(cdr(car(x)))
}

///|
pub fn cdadr(x : Value) -> Value {
  cdr(car(cdr(x)))
}

///|
pub fn cddar(x : Value) -> Value {
  cdr(cdr(car(x)))
}

///|
pub fn caaar(x : Value) -> Value {
  car(car(car(x)))
}

///|
pub fn cdaar(x : Value) -> Value {
  cdr(car(car(x)))
}

///|
pub fn caddar(x : Value) -> Value {
  car(cdr(cdr(car(x))))
}

///|
pub fn cadadr(x : Value) -> Value {
  car(cdr(car(cdr(x))))
}

///|
pub fn caaddr(x : Value) -> Value {
  car(car(cdr(cdr(x))))
}

///|
pub fn cdaddr(x : Value) -> Value {
  cdr(car(cdr(cdr(x))))
}

///|
pub fn caaadr(x : Value) -> Value {
  car(car(car(cdr(x))))
}

///|
pub fn first(x : Value) -> Value {
  car(x)
}

///|
pub fn second(x : Value) -> Value {
  cadr(x)
}

///|
pub fn third(x : Value) -> Value {
  caddr(x)
}

///|
pub fn fourth(x : Value) -> Value {
  cadddr(x)
}

///|
pub fn fifth(x : Value) -> Value {
  car(cddddr(x))
}

///|
pub fn rest(x : Value) -> Value {
  cdr(x)
}

///|
/// `(rplaca c v)`; returns c.
pub fn rplaca(c : Value, v : Value) -> Value {
  match c {
    Cons(cc) => cc.car = v
    _ => ()
  }
  c
}

///|
/// `(rplacd c v)`; returns c.
pub fn rplacd(c : Value, v : Value) -> Value {
  match c {
    Cons(cc) => cc.cdr = v
    _ => ()
  }
  c
}

///|
/// `(setf (car c) v)`; returns v.
pub fn setf_car(c : Value, v : Value) -> Value {
  rplaca(c, v) |> ignore
  v
}

///|
/// `(setf (cdr c) v)`; returns v.
pub fn setf_cdr(c : Value, v : Value) -> Value {
  rplacd(c, v) |> ignore
  v
}

///|
/// Build a proper list from an array.
pub fn list(xs : Array[Value]) -> Value {
  let mut r = Nil
  for i = xs.length() - 1; i >= 0; i = i - 1 {
    r = Cons({ car: xs[i], cdr: r })
  }
  r
}

///|
/// Build a list from an array view.
pub fn list_view(xs : ArrayView[Value]) -> Value {
  let mut r = Nil
  for i = xs.length() - 1; i >= 0; i = i - 1 {
    r = Cons({ car: xs[i], cdr: r })
  }
  r
}

///|
pub fn list1(a : Value) -> Value {
  cons(a, Nil)
}

///|
pub fn list2(a : Value, b : Value) -> Value {
  cons(a, cons(b, Nil))
}

///|
pub fn list3(a : Value, b : Value, c : Value) -> Value {
  cons(a, cons(b, cons(c, Nil)))
}

///|
pub fn list4(a : Value, b : Value, c : Value, d : Value) -> Value {
  cons(a, cons(b, cons(c, cons(d, Nil))))
}

///|
/// `(list* a b ... tail)`: the last element is the tail.
pub fn list_star(xs : Array[Value]) -> Value {
  if xs.is_empty() {
    return Nil
  }
  let mut r = xs[xs.length() - 1]
  for i = xs.length() - 2; i >= 0; i = i - 1 {
    r = Cons({ car: xs[i], cdr: r })
  }
  r
}

///|
/// Convert a list to an array (ignores a dotted tail).
pub fn list_to_array(l : Value) -> Array[Value] {
  let r = []
  let mut p = l
  while p is Cons(c) {
    r.push(c.car)
    p = c.cdr
  }
  r
}

///|
/// Iterate over the elements of a list.
pub fn Value::iter(self : Value) -> Iter[Value] {
  Iter::new(fn() {
    let mut p = self
    fn() -> Value? {
      match p {
        Cons(c) => {
          p = c.cdr
          Some(c.car)
        }
        _ => None
      }
    }
  }())
}

///|
/// `(length l)` for lists, strings and vectors.
pub fn length(l : Value) -> Int {
  match l {
    Str(s) => s.length()
    Vec(a) =>
      match a.fill {
        Some(f) => f
        None => a.data.length()
      }
    _ => {
      let mut n = 0
      let mut p = l
      while p is Cons(c) {
        n += 1
        p = c.cdr
      }
      n
    }
  }
}

///|
/// `(length l)` as a Lisp integer.
pub fn llength(l : Value) -> Value {
  Fix(length(l).to_int64())
}

///|
/// `(nthcdr n l)`
pub fn nthcdr(n : Int, l : Value) -> Value {
  let mut p = l
  for _ in 0..<n {
    p = cdr(p)
  }
  p
}

///|
/// `(nth n l)`
pub fn nth(n : Int, l : Value) -> Value {
  car(nthcdr(n, l))
}

///|
/// `(last l)`: the last cons.
pub fn last(l : Value) -> Value {
  let mut p = l
  while p is Cons(c) {
    match c.cdr {
      Cons(_) => p = c.cdr
      _ => return p
    }
  }
  p
}

///|
/// `(car (last l))`
pub fn last_elem(l : Value) -> Value {
  car(last(l))
}

///|
/// `(append a b)`
pub fn append(a : Value, b : Value) -> Value {
  match a {
    Nil => b
    Cons(_) => {
      let head = Cons({ car: Nil, cdr: Nil })
      let mut tail = head
      let mut p = a
      while p is Cons(c) {
        let n = Cons({ car: c.car, cdr: Nil })
        rplacd(tail, n) |> ignore
        tail = n
        p = c.cdr
      }
      rplacd(tail, b) |> ignore
      cdr(head)
    }
    _ => b
  }
}

///|
/// `(append l1 l2 ...)`
pub fn append_n(ls : Array[Value]) -> Value {
  if ls.is_empty() {
    return Nil
  }
  let mut r = ls[ls.length() - 1]
  for i = ls.length() - 2; i >= 0; i = i - 1 {
    r = append(ls[i], r)
  }
  r
}

///|
/// `(nconc a b)`
pub fn nconc(a : Value, b : Value) -> Value {
  match a {
    Cons(_) => {
      rplacd(last(a), b) |> ignore
      a
    }
    _ => b
  }
}

///|
/// `(nconc l1 l2 ...)`
pub fn nconc_n(ls : Array[Value]) -> Value {
  let mut r = Nil
  for i = ls.length() - 1; i >= 0; i = i - 1 {
    r = nconc(ls[i], r)
  }
  r
}

///|
/// `(reverse l)`
pub fn reverse(l : Value) -> Value {
  match l {
    Str(s) => Str(s.rev())
    _ => {
      let mut r = Nil
      let mut p = l
      while p is Cons(c) {
        r = Cons({ car: c.car, cdr: r })
        p = c.cdr
      }
      r
    }
  }
}

///|
/// `(nreverse l)` — implemented non-destructively-equivalent but in place.
pub fn nreverse(l : Value) -> Value {
  let mut prev = Nil
  let mut p = l
  while p is Cons(c) {
    let next = c.cdr
    c.cdr = prev
    prev = p
    p = next
  }
  prev
}

///|
/// `(revappend a b)`
pub fn revappend(a : Value, b : Value) -> Value {
  let mut r = b
  let mut p = a
  while p is Cons(c) {
    r = Cons({ car: c.car, cdr: r })
    p = c.cdr
  }
  r
}

///|
/// `(nreconc a b)`
pub fn nreconc(a : Value, b : Value) -> Value {
  let mut prev = b
  let mut p = a
  while p is Cons(c) {
    let next = c.cdr
    c.cdr = prev
    prev = p
    p = next
  }
  prev
}

///|
/// `(copy-list l)`
pub fn copy_list(l : Value) -> Value {
  match l {
    Cons(_) => {
      let head = Cons({ car: Nil, cdr: Nil })
      let mut tail = head
      let mut p = l
      while p is Cons(c) {
        let n = Cons({ car: c.car, cdr: Nil })
        rplacd(tail, n) |> ignore
        tail = n
        p = c.cdr
      }
      rplacd(tail, p) |> ignore
      cdr(head)
    }
    _ => l
  }
}

///|
/// `(copy-tree x)`
pub fn copy_tree(x : Value) -> Value {
  match x {
    Cons(c) => Cons({ car: copy_tree(c.car), cdr: copy_tree(c.cdr) })
    _ => x
  }
}

///|
/// `(butlast l &optional n)`
pub fn butlast(l : Value, n? : Int = 1) -> Value {
  let arr = list_to_array(l)
  if arr.length() <= n {
    Nil
  } else {
    list_view(arr[0:arr.length() - n])
  }
}

///|
/// `(nbutlast l)`
pub fn nbutlast(l : Value, n? : Int = 1) -> Value {
  butlast(l, n~)
}

///|
/// `(ldiff l tail)`
pub fn ldiff(l : Value, tail : Value) -> Value {
  let r = []
  let mut p = l
  while p is Cons(c) {
    if physical_equal_value(p, tail) {
      break
    }
    r.push(c.car)
    p = c.cdr
  }
  list(r)
}

///|
/// `(tailp sub l)`
pub fn tailp(sub : Value, l : Value) -> Bool {
  let mut p = l
  while true {
    if eql(p, sub) {
      return true
    }
    match p {
      Cons(c) => p = c.cdr
      _ => return false
    }
  }
  false
}

///|
/// Physical identity of two values (for conses and other heap objects).
pub fn physical_equal_value(a : Value, b : Value) -> Bool {
  match (a, b) {
    (Cons(x), Cons(y)) => physical_equal(x, y)
    _ => eq(a, b)
  }
}

// ---------------------------------------------------------------------------
// Membership and association

///|
/// `(member x l)` with eql.
pub fn member(x : Value, l : Value) -> Value {
  let mut p = l
  while p is Cons(c) {
    if eql(x, c.car) {
      return p
    }
    p = c.cdr
  }
  Nil
}

///|
/// `(memq x l)`
pub fn memq(x : Value, l : Value) -> Value {
  let mut p = l
  while p is Cons(c) {
    if eq(x, c.car) {
      return p
    }
    p = c.cdr
  }
  Nil
}

///|
/// `(member x l :test #'equal)`
pub fn member_equal(x : Value, l : Value) -> Value {
  let mut p = l
  while p is Cons(c) {
    if equal(x, c.car) {
      return p
    }
    p = c.cdr
  }
  Nil
}

///|
/// `(member x l :test f)`
pub fn member_if_test(
  x : Value,
  l : Value,
  pred2 : (Value, Value) -> Bool raise,
) -> Value raise {
  let mut p = l
  while p is Cons(c) {
    if pred2(x, c.car) {
      return p
    }
    p = c.cdr
  }
  Nil
}

///|
/// `(member-if pred l)`
pub fn member_if(pred : (Value) -> Bool raise, l : Value) -> Value raise {
  let mut p = l
  while p is Cons(c) {
    if pred(c.car) {
      return p
    }
    p = c.cdr
  }
  Nil
}

///|
/// `(assoc x alist)` with eql.
pub fn assoc(x : Value, al : Value) -> Value {
  let mut p = al
  while p is Cons(c) {
    match c.car {
      Cons(e) => if eql(x, e.car) { return c.car }
      _ => ()
    }
    p = c.cdr
  }
  Nil
}

///|
/// `(assq x alist)`
pub fn assq(x : Value, al : Value) -> Value {
  let mut p = al
  while p is Cons(c) {
    match c.car {
      Cons(e) => if eq(x, e.car) { return c.car }
      _ => ()
    }
    p = c.cdr
  }
  Nil
}

///|
/// `(assoc x alist :test #'equal)`
pub fn assoc_equal(x : Value, al : Value) -> Value {
  let mut p = al
  while p is Cons(c) {
    match c.car {
      Cons(e) => if equal(x, e.car) { return c.car }
      _ => ()
    }
    p = c.cdr
  }
  Nil
}

///|
/// `(assoc x alist :test f)`
pub fn assoc_test(
  x : Value,
  al : Value,
  pred2 : (Value, Value) -> Bool raise,
) -> Value raise {
  let mut p = al
  while p is Cons(c) {
    match c.car {
      Cons(e) => if pred2(x, e.car) { return c.car }
      _ => ()
    }
    p = c.cdr
  }
  Nil
}

///|
/// `(rassoc x alist)` with eql.
pub fn rassoc(x : Value, al : Value) -> Value {
  let mut p = al
  while p is Cons(c) {
    match c.car {
      Cons(e) => if eql(x, e.cdr) { return c.car }
      _ => ()
    }
    p = c.cdr
  }
  Nil
}

///|
/// `(getf plist key)`
pub fn getf(pl : Value, key : Value, default? : Value = Nil) -> Value {
  let mut p = pl
  while p is Cons(c) {
    if eq(c.car, key) {
      return cadr(p)
    }
    p = cdr(c.cdr)
  }
  default
}

// ---------------------------------------------------------------------------
// Removal and deletion

///|
/// `(remove x l)` with eql.
pub fn remove(x : Value, l : Value) -> Value {
  let r = []
  let mut p = l
  while p is Cons(c) {
    if !eql(x, c.car) {
      r.push(c.car)
    }
    p = c.cdr
  }
  list(r)
}

///|
/// `(remove x l :test #'equal)`
pub fn remove_equal(x : Value, l : Value) -> Value {
  let r = []
  let mut p = l
  while p is Cons(c) {
    if !equal(x, c.car) {
      r.push(c.car)
    }
    p = c.cdr
  }
  list(r)
}

///|
/// `(delete x l)` — returns a fresh list (non-destructive is a valid
/// implementation of delete).
pub fn delete(x : Value, l : Value) -> Value {
  remove(x, l)
}

///|
/// `(remove-if pred l)`
pub fn remove_if(pred : (Value) -> Bool raise, l : Value) -> Value raise {
  let r = []
  let mut p = l
  while p is Cons(c) {
    if !pred(c.car) {
      r.push(c.car)
    }
    p = c.cdr
  }
  list(r)
}

///|
/// `(remove-if-not pred l)`
pub fn remove_if_not(pred : (Value) -> Bool raise, l : Value) -> Value raise {
  let r = []
  let mut p = l
  while p is Cons(c) {
    if pred(c.car) {
      r.push(c.car)
    }
    p = c.cdr
  }
  list(r)
}

///|
/// `(remove-duplicates l)` with eql; keeps the last occurrence like CL.
pub fn remove_duplicates(
  l : Value,
  pred2? : (Value, Value) -> Bool raise = (a, b) => eql(a, b),
) -> Value raise {
  let arr = list_to_array(l)
  let r = []
  for i, x in arr {
    let mut dup = false
    for j in (i + 1)..<arr.length() {
      if pred2(x, arr[j]) {
        dup = true
        break
      }
    }
    if !dup {
      r.push(x)
    }
  }
  list(r)
}

// ---------------------------------------------------------------------------
// Mapping

///|
/// `(mapcar f l)`
pub fn mapcar(f : (Value) -> Value raise, l : Value) -> Value raise {
  let r = []
  let mut p = l
  while p is Cons(c) {
    r.push(f(c.car))
    p = c.cdr
  }
  list(r)
}

///|
/// `(mapcar f l1 l2)`
pub fn mapcar2(
  f : (Value, Value) -> Value raise,
  l1 : Value,
  l2 : Value,
) -> Value raise {
  let r = []
  let mut p = l1
  let mut q = l2
  while p is Cons(c) && q is Cons(d) {
    r.push(f(c.car, d.car))
    p = c.cdr
    q = d.cdr
  }
  list(r)
}

///|
/// `(mapc f l)`; returns l.
pub fn mapc(f : (Value) -> Unit raise, l : Value) -> Value raise {
  let mut p = l
  while p is Cons(c) {
    f(c.car)
    p = c.cdr
  }
  l
}

///|
/// `(mapcan f l)`
pub fn mapcan(f : (Value) -> Value raise, l : Value) -> Value raise {
  let parts = []
  let mut p = l
  while p is Cons(c) {
    parts.push(f(c.car))
    p = c.cdr
  }
  nconc_n(parts)
}

///|
/// `(maplist f l)`
pub fn maplist(f : (Value) -> Value raise, l : Value) -> Value raise {
  let r = []
  let mut p = l
  while p is Cons(c) {
    r.push(f(p))
    p = c.cdr
  }
  list(r)
}

///|
/// `(every pred l)`
pub fn every(pred : (Value) -> Bool raise, l : Value) -> Bool raise {
  let mut p = l
  while p is Cons(c) {
    if !pred(c.car) {
      return false
    }
    p = c.cdr
  }
  true
}

///|
/// `(some pred l)` returning Bool.
pub fn some(pred : (Value) -> Bool raise, l : Value) -> Bool raise {
  let mut p = l
  while p is Cons(c) {
    if pred(c.car) {
      return true
    }
    p = c.cdr
  }
  false
}

///|
/// `(some f l)` returning the first non-nil value of f.
pub fn some_value(f : (Value) -> Value raise, l : Value) -> Value raise {
  let mut p = l
  while p is Cons(c) {
    let v = f(c.car)
    if !(v is Nil) {
      return v
    }
    p = c.cdr
  }
  Nil
}

///|
/// `(find-if pred l)`
pub fn find_if(pred : (Value) -> Bool raise, l : Value) -> Value raise {
  let mut p = l
  while p is Cons(c) {
    if pred(c.car) {
      return c.car
    }
    p = c.cdr
  }
  Nil
}

///|
/// `(find x l)` with eql.
pub fn find(x : Value, l : Value) -> Value {
  let mut p = l
  while p is Cons(c) {
    if eql(x, c.car) {
      return c.car
    }
    p = c.cdr
  }
  Nil
}

///|
/// `(position x l)` with eql; -1 if absent.
pub fn position(x : Value, l : Value) -> Int {
  let mut i = 0
  let mut p = l
  while p is Cons(c) {
    if eql(x, c.car) {
      return i
    }
    i += 1
    p = c.cdr
  }
  -1
}

///|
/// `(position-if pred l)`; -1 if absent.
pub fn position_if(pred : (Value) -> Bool raise, l : Value) -> Int raise {
  let mut i = 0
  let mut p = l
  while p is Cons(c) {
    if pred(c.car) {
      return i
    }
    i += 1
    p = c.cdr
  }
  -1
}

///|
/// `(count-if pred l)`
pub fn count_if(pred : (Value) -> Bool raise, l : Value) -> Int raise {
  let mut n = 0
  let mut p = l
  while p is Cons(c) {
    if pred(c.car) {
      n += 1
    }
    p = c.cdr
  }
  n
}

///|
/// `(reduce f l :initial-value init)`
pub fn reduce(
  f : (Value, Value) -> Value raise,
  l : Value,
  initial? : Value,
) -> Value raise {
  let arr = list_to_array(l)
  match initial {
    Some(init) => {
      let mut acc = init
      for x in arr {
        acc = f(acc, x)
      }
      acc
    }
    None => {
      if arr.is_empty() {
        return Nil
      }
      let mut acc = arr[0]
      for i in 1..<arr.length() {
        acc = f(acc, arr[i])
      }
      acc
    }
  }
}

// ---------------------------------------------------------------------------
// Sets

///|
/// `(adjoin x l)` with eql.
pub fn adjoin(x : Value, l : Value) -> Value {
  if member(x, l) is Nil {
    cons(x, l)
  } else {
    l
  }
}

///|
/// `(union a b)` with a test.
pub fn union_(
  a : Value,
  b : Value,
  pred2? : (Value, Value) -> Bool raise = (x, y) => eql(x, y),
) -> Value raise {
  let mut r = b
  for x in list_to_array(a) {
    if member_if_test(x, b, pred2) is Nil {
      r = cons(x, r)
    }
  }
  r
}

///|
/// `(intersection a b)` with a test.
pub fn intersection(
  a : Value,
  b : Value,
  pred2? : (Value, Value) -> Bool raise = (x, y) => eql(x, y),
) -> Value raise {
  let r = []
  for x in list_to_array(a) {
    if !(member_if_test(x, b, pred2) is Nil) {
      r.push(x)
    }
  }
  list(r)
}

///|
/// `(set-difference a b)` with a test.
pub fn set_difference(
  a : Value,
  b : Value,
  pred2? : (Value, Value) -> Bool raise = (x, y) => eql(x, y),
) -> Value raise {
  let r = []
  for x in list_to_array(a) {
    if member_if_test(x, b, pred2) is Nil {
      r.push(x)
    }
  }
  list(r)
}

///|
/// `(subsetp a b)`
pub fn subsetp(
  a : Value,
  b : Value,
  pred2? : (Value, Value) -> Bool raise = (x, y) => eql(x, y),
) -> Bool raise {
  for x in list_to_array(a) {
    if member_if_test(x, b, pred2) is Nil {
      return false
    }
  }
  true
}

// ---------------------------------------------------------------------------
// Substitution and sorting

///|
/// `(subst new old tree)` with eql.
pub fn subst(new : Value, old : Value, tree : Value) -> Value {
  if eql(old, tree) {
    new
  } else {
    match tree {
      Cons(c) => {
        let a = subst(new, old, c.car)
        let d = subst(new, old, c.cdr)
        if physical_equal_value(a, c.car) && physical_equal_value(d, c.cdr) {
          tree
        } else {
          cons(a, d)
        }
      }
      _ => tree
    }
  }
}

///|
/// `(sublis alist tree)` with eql.
pub fn sublis(al : Value, tree : Value) -> Value {
  let hit = assoc(tree, al)
  if !(hit is Nil) {
    return cdr(hit)
  }
  match tree {
    Cons(c) => {
      let a = sublis(al, c.car)
      let d = sublis(al, c.cdr)
      if physical_equal_value(a, c.car) && physical_equal_value(d, c.cdr) {
        tree
      } else {
        cons(a, d)
      }
    }
    _ => tree
  }
}

///|
/// Stable merge sort of a list with a "less than" predicate (CL `sort` /
/// `stable-sort`).
pub fn sort_list(l : Value, lt : (Value, Value) -> Bool raise) -> Value raise {
  let arr = list_to_array(l)
  let sorted = merge_sort(arr, lt)
  list(sorted)
}

///|
fn merge_sort(
  arr : Array[Value],
  lt : (Value, Value) -> Bool raise,
) -> Array[Value] raise {
  let n = arr.length()
  if n <= 1 {
    return arr
  }
  let mid = n / 2
  let a = merge_sort(arr[0:mid].to_array(), lt)
  let b = merge_sort(arr[mid:].to_array(), lt)
  let r = Array::new(capacity=n)
  let mut i = 0
  let mut j = 0
  while i < a.length() && j < b.length() {
    // stable: take from b only if b < a
    if lt(b[j], a[i]) {
      r.push(b[j])
      j += 1
    } else {
      r.push(a[i])
      i += 1
    }
  }
  while i < a.length() {
    r.push(a[i])
    i += 1
  }
  while j < b.length() {
    r.push(b[j])
    j += 1
  }
  r
}

///|
/// Sort a MoonBit array stably with a "less than" predicate.
pub fn sort_array(
  arr : Array[Value],
  lt : (Value, Value) -> Bool raise,
) -> Array[Value] raise {
  merge_sort(arr, lt)
}

///|
/// `(push x place)` helper for a Ref-held list: returns the new list.
pub fn push_ref(x : Value, r : Ref[Value]) -> Value {
  r.val = cons(x, r.val)
  r.val
}

///|
/// `(pop place)` helper for a Ref-held list.
pub fn pop_ref(r : Ref[Value]) -> Value {
  let v = car(r.val)
  r.val = cdr(r.val)
  v
}

///|
/// `(push x sym)` on a special variable; returns the new value.
pub fn push_special(x : Value, s : Value) -> Value {
  set(s, cons(x, symval(s)))
}

///|
/// `(pop sym)` on a special variable.
pub fn pop_special(s : Value) -> Value {
  let l = symval(s)
  set(s, cdr(l)) |> ignore
  car(l)
}

///|
/// Simple list accumulator (CL `loop ... collect`).
pub(all) struct Collector {
  mut head : Value
  mut tail : Value
}

///|
pub fn Collector::new() -> Collector {
  { head: Nil, tail: Nil }
}

///|
pub fn Collector::add(self : Collector, x : Value) -> Unit {
  let c = cons(x, Nil)
  match self.tail {
    Cons(tc) => tc.cdr = c
    _ => self.head = c
  }
  self.tail = c
}

///|
/// Append a list (copying it) — `loop ... append`.
pub fn Collector::append_list(self : Collector, l : Value) -> Unit {
  for x in l.iter() {
    self.add(x)
  }
}

///|
pub fn Collector::result(self : Collector) -> Value {
  self.head
}
