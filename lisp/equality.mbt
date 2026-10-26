///|
/// `(eq a b)`. Fixnums and characters compare by value, as they do in every
/// CL implementation Maxima runs on.
pub fn eq(a : Value, b : Value) -> Bool {
  match (a, b) {
    (Nil, Nil) => true
    (Sym(x), Sym(y)) => physical_equal(x, y)
    (Cons(x), Cons(y)) => physical_equal(x, y)
    (Fix(x), Fix(y)) => x == y
    (Char(x), Char(y)) => x == y
    (Str(x), Str(y)) => physical_equal(x, y)
    (Vec(x), Vec(y)) => physical_equal(x, y)
    (Hash(x), Hash(y)) => physical_equal(x, y)
    (Func(x), Func(y)) => physical_equal(x, y)
    (Struct(x), Struct(y)) => physical_equal(x, y)
    (Stream(x), Stream(y)) => physical_equal(x, y)
    (Box(x), Box(y)) => physical_equal(x, y)
    (Flo(x), Flo(y)) => x == y && dsignbit(x) == dsignbit(y)
    // Bignums, ratios and complexes are heap objects in CL: EQ is identity.
    (Big(_), Big(_)) => physical_equal(a, b)
    (Ratio(_, _), Ratio(_, _)) => physical_equal(a, b)
    (Cplx(_, _), Cplx(_, _)) => physical_equal(a, b)
    _ => false
  }
}

///|
/// `(eql a b)`: numbers of the same type and value, characters, or `eq`.
pub fn eql(a : Value, b : Value) -> Bool {
  match (a, b) {
    (Fix(x), Fix(y)) => x == y
    (Big(x), Big(y)) => x == y
    (Ratio(n1, d1), Ratio(n2, d2)) => n1 == n2 && d1 == d2
    (Flo(x), Flo(y)) => x == y && dsignbit(x) == dsignbit(y)
    (Cplx(r1, i1), Cplx(r2, i2)) => eql(r1, r2) && eql(i1, i2)
    (Char(x), Char(y)) => x == y
    _ => eq(a, b)
  }
}

///|
/// `(equal a b)`: structural on conses and strings.
pub fn equal(a : Value, b : Value) -> Bool {
  let mut x = a
  let mut y = b
  while true {
    match (x, y) {
      (Cons(c1), Cons(c2)) => {
        if physical_equal(c1, c2) {
          return true
        }
        if !equal(c1.car, c2.car) {
          return false
        }
        x = c1.cdr
        y = c2.cdr
      }
      (Str(s1), Str(s2)) => return s1 == s2
      (Vec(v1), Vec(v2)) =>
        // CL equal on bit-vectors/strings only; treat char vectors as strings
        if v1.elt == "character" && v2.elt == "character" {
          return lstring(x) == lstring(y)
        } else {
          return physical_equal(v1, v2)
        }
      (Str(_), Vec(_)) | (Vec(_), Str(_)) => return lstring(x) == lstring(y)
      _ => return eql(x, y)
    }
  }
  false
}

///|
/// `(equalp a b)`: case-insensitive strings, numeric `=`, structural.
pub fn equalp(a : Value, b : Value) -> Bool {
  match (a, b) {
    (Cons(c1), Cons(c2)) => equalp(c1.car, c2.car) && equalp(c1.cdr, c2.cdr)
    (Str(s1), Str(s2)) => s1.to_lower() == s2.to_lower()
    (Char(c1), Char(c2)) => char_downcase(c1) == char_downcase(c2)
    (Vec(v1), Vec(v2)) => {
      let n = length(a)
      if n != length(b) {
        return false
      }
      for i in 0..<n {
        if !equalp(v1.data[i], v2.data[i]) {
          return false
        }
      }
      true
    }
    _ =>
      if numberp(a) && numberp(b) {
        num_eq(a, b) catch {
          _ => false
        }
      } else {
        eql(a, b)
      }
  }
}

///|
/// A structural hash consistent with `equal`.
pub fn hash_equal(x : Value) -> Int {
  hash_equal_depth(x, 0)
}

///|
fn hash_equal_depth(x : Value, depth : Int) -> Int {
  match x {
    Nil => 17
    Sym(s) => s.id * 31 + 7
    Fix(n) => n.to_int() ^ (n >> 32).to_int()
    Big(b) => b.hash()
    Ratio(n, d) => n.hash() * 31 + d.hash()
    Flo(f) => f.hash()
    Cplx(r, i) => hash_equal_depth(r, depth) * 31 + hash_equal_depth(i, depth)
    Char(c) => c.to_int() + 3
    Str(s) => s.hash()
    Cons(_) => {
      if depth > 4 {
        return 99
      }
      let mut h = 23
      let mut p = x
      let mut n = 0
      while p is Cons(c) && n < 8 {
        h = h * 31 + hash_equal_depth(c.car, depth + 1)
        p = c.cdr
        n += 1
      }
      h
    }
    Vec(v) => if v.elt == "character" { lstring(x).hash() } else { 5 }
    _ => 1
  }
}
