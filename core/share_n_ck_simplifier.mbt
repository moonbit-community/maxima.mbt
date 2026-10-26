// Port of share/logic/Ksimplifier.lisp: simplification of logic
// expressions by Karnaugh-map (Quine-McCluskey) reduction.

///|
/// Checks if the two forms can be combined (are adjacent in the K-Map).
/// Example : (is-adjacent '(0 0 1 0) '(0 0 1 1)) -> t
///           (is-adjacent '(0 0 1 1) '(0 0 1 1)) -> nil
fn is_adjacent(form1 : Value, form2 : Value) -> Value raise {
  let mut x = form1
  let mut y = form2
  while x is Cons(_) && y is Cons(_) {
    if !equal(car(x), car(y)) {
      if equal(cdr(x), cdr(y)) {
        if equal(car(x), Fix(2L)) || equal(car(y), Fix(2L)) {
          return Nil
        } else {
          return t
        }
      } else {
        return Nil
      }
    }
    x = cdr(x)
    y = cdr(y)
  }
  Nil
}

///|
/// Returns the common-expression obtained by combining 2 minterms.
/// Example : (common-expression '(1 1 0 1) '(1 1 1 1)) -> (1 1 2 1)
fn common_expression(minterm1 : Value, minterm2 : Value) -> Value raise {
  let acc = Collector::new()
  let mut x = minterm1
  let mut y = minterm2
  while x is Cons(_) && y is Cons(_) {
    acc.add(if equal(car(x), car(y)) { car(x) } else { Fix(2L) })
    x = cdr(x)
    y = cdr(y)
  }
  acc.result()
}

///|
/// Checks a minterm against a list of minterms to find adjacent pairs.
/// Returns a list l such that (car l) is a list of implicants formed by
/// combining minterm with all possible neighbours in minterms, and
/// (cadr l) is a list of all minterms covered in the implicants in the
/// first list.
fn combine_neighbours(minterm : Value, minterms : Value) -> Value raise {
  let mut pair_found = false
  let comm_expr_ls = Collector::new()
  let to_remove = Collector::new()
  for minterm2 in minterms.iter() {
    if is_adjacent(minterm, minterm2).truthy() {
      pair_found = true
      comm_expr_ls.add(common_expression(minterm, minterm2))
      to_remove.add(minterm2)
    }
  }
  let result = list([comm_expr_ls.result(), cons(minterm, to_remove.result())])
  if pair_found {
    result
  } else {
    list([cons(minterm, Nil), Nil])
  }
}

///|
/// Reduces a list of minterms, corresponding to numvar number of boolean
/// variables, to its prime-implicants, collectively covering all minterms.
fn reduce_to_prime_implicants(numvar : Value, minterms : Value) -> Value raise {
  let mut minterms = minterms
  let n = to_int(numvar)
  for _counter in 0..<n {
    let mut implicants : Value = Nil
    let mut covered : Value = Nil
    let mut minterms_left = minterms
    while minterms_left is Cons(_) {
      let result = combine_neighbours(car(minterms_left), cdr(minterms_left))
      // Add the returned list of combined minterms to "implicants" list
      implicants = append(implicants, car(result))
      // Add all the minterms covered in prime-implicants to list "covered"
      covered = append(covered, cadr(result))
      minterms_left = cdr(minterms_left)
    }
    let cov = covered
    minterms = remove_duplicates(
      remove_if(implicant => member(implicant, cov).truthy(), implicants),
      pred2=(a, b) => equal(a, b),
    )
  }
  minterms
}

///|
/// Returns prime-implicant if minterm is covered in given prime-implicant,
/// else return nil.
fn is_covered_by_implicant(
  minterm : Value,
  prime_implicant : Value,
) -> Value raise {
  let acc = Collector::new()
  let mut x = minterm
  let mut y = prime_implicant
  while x is Cons(_) && y is Cons(_) {
    let bit_minterm = car(x)
    let bit_prime_implicant = car(y)
    acc.add(
      lbool(
        equal(bit_minterm, bit_prime_implicant) ||
        equal(bit_prime_implicant, Fix(2L)),
      ),
    )
    x = cdr(x)
    y = cdr(y)
  }
  if every(term => term.truthy(), acc.result()) {
    prime_implicant
  } else {
    Nil
  }
}

///|
/// Returns list of prime-implicants covering the minterm.
fn is_covered_by_set_of_implicants(
  minterm : Value,
  prime_implicants : Value,
) -> Value raise {
  remove_if(
    x => x is Nil,
    mapcar(p => is_covered_by_implicant(minterm, p), prime_implicants),
  )
}

///|
fn share_n_ck_simplifier__count2(minterm : Value) -> Int64 {
  let mut c = 0L
  for b in minterm.iter() {
    if eql(b, Fix(2L)) {
      c += 1L
    }
  }
  c
}

///|
/// Given a list of prime-implicants by minterms, returns a list of
/// implicants by minterms having maximum level of reduction.
fn select_maximum_reduced_prime_implicants(
  implicant_by_minterms : Value,
) -> Value raise {
  let maxes = mapcar(
    minterms => {
      let mut m = 0L
      for minterm in minterms.iter() {
        let c = share_n_ck_simplifier__count2(minterm)
        if c > m {
          m = c
        }
      }
      Fix(m)
    },
    implicant_by_minterms,
  )
  let acc = Collector::new()
  let mut a = implicant_by_minterms
  let mut b = maxes
  while a is Cons(_) && b is Cons(_) {
    let max_reduction = car(b)
    acc.add(
      remove_if(
        minterm => !num_eq(
          Fix(share_n_ck_simplifier__count2(minterm)),
          max_reduction,
        ),
        car(a),
      ),
    )
    a = cdr(a)
    b = cdr(b)
  }
  acc.result()
}

///|
/// numvar : number of boolean variables
/// minterms : list of minterms of the form (X X X X) where Xs are 0s or 1s.
/// Returns a list of prime-implicants which is the minimum cover of the
/// given minterms.
fn reduce_to_minimum_cover(numvar : Value, minterms : Value) -> Value raise {
  let prime_implicants = reduce_to_prime_implicants(numvar, minterms)
  let implicant_by_minterms = mapcar(
    minterm => is_covered_by_set_of_implicants(minterm, prime_implicants),
    minterms,
  )
  remove_duplicates(
    mapcar(
      minterms => car(minterms),
      select_maximum_reduced_prime_implicants(implicant_by_minterms),
    ),
  )
}

///|
/// Returns the binary representation of number, numvar bits.
/// Example : (decimal-to-binary 2 3) -> (1 1)
fn decimal_to_binary(numvar : Value, number : Value) -> Value raise {
  let acc = Collector::new()
  let mut number = number
  let mut x = num_sub(numvar, Fix(1L))
  while num_ge(x, Fix(0L)) {
    let p = expt(Fix(2L), x)
    if num_ge(number, p) {
      number = num_sub(number, p)
      acc.add(Fix(1L))
    } else {
      acc.add(Fix(0L))
    }
    x = num_sub(x, Fix(1L))
  }
  acc.result()
}

///|
/// Returns the maxima-expression corresponding to the given minimum-cover.
fn maxima_expression(
  minimum_cover : Value,
  list_of_variables : Value,
) -> Value raise {
  cons(
    list([q_mor, q_simp]),
    mapcar(
      prime_implicant => {
        let terms = Collector::new()
        let mut b = prime_implicant
        let mut v = list_of_variables
        while b is Cons(_) && v is Cons(_) {
          let bit = car(b)
          let variable = car(v)
          terms.add(
            if equal(bit, Fix(0L)) {
              list([list([q_mnot, q_simp]), variable])
            } else if equal(bit, Fix(1L)) {
              variable
            } else {
              Nil
            },
          )
          b = cdr(b)
          v = cdr(v)
        }
        let implicant_maxima_expr = remove_if(x => x is Nil, terms.result())
        if length(implicant_maxima_expr) == 1 {
          car(implicant_maxima_expr)
        } else {
          cons(list([q_mand, q_simp]), implicant_maxima_expr)
        }
      },
      minimum_cover,
    ),
  )
}

///|
fn transform_to_intermediate(
  expr : Value,
  substitution_table : Value,
) -> Value raise {
  if consp(expr) &&
    consp(car(expr)) &&
    member(caar(expr), list([q_mand, q_mor, q_mnot])).truthy() {
    cons(
      car(expr),
      mapcar(x => transform_to_intermediate(x, substitution_table), cdr(expr)),
    )
  } else if consp(expr) && consp(car(expr)) {
    let sym_ = gensym()
    sethash(sym_, substitution_table, expr) |> ignore
    sym_
  } else {
    expr
  }
}

///|
fn substitute_intermediate(
  expr : Value,
  substitution_table : Value,
) -> Value raise {
  if consp(expr) && consp(car(expr)) {
    cons(
      car(expr),
      mapcar(x => substitute_intermediate(x, substitution_table), cdr(expr)),
    )
  } else if atom(expr) {
    let (v, found) = gethash2(expr, substitution_table)
    if found {
      v
    } else {
      expr
    }
  } else {
    Nil
  }
}

///|
/// Given a logic expression, reduce it to its simplest form using the
/// method of K-Map reduction.
fn d_logic_simplify(expr : Value) -> Value raise {
  let substitutions = make_hash_table()
  let intermediate = transform_to_intermediate(expr, substitutions)
  let characteristic_vector = cdr(d_characteristic_vector(intermediate, Nil))
  let list_of_variables = list_of_variables(intermediate)
  let numvar = length(list_of_variables)
  let limit = num_sub(expt(Fix(2L), int(numvar)), Fix(1L))
  let minterms = Collector::new()
  let mut counter : Value = Fix(0L)
  for bit in characteristic_vector.iter() {
    if num_gt(counter, limit) {
      break
    }
    if bit.truthy() {
      minterms.add(decimal_to_binary(int(numvar), counter))
    }
    counter = num_add(counter, Fix(1L))
  }
  let minimum_cover = reduce_to_minimum_cover(int(numvar), minterms.result())
  if minimum_cover is Nil {
    Nil
  } else if equal(car(minimum_cover), list(Array::make(numvar, Value::Fix(2L)))) {
    t
  } else {
    let converted_expression = substitute_intermediate(
      maxima_expression(minimum_cover, list_of_variables),
      substitutions,
    )
    if length(converted_expression) == 2 {
      cadr(converted_expression)
    } else {
      converted_expression
    }
  }
}
