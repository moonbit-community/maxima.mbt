// Port of share/affine/sheafa.lisp (part 1): helpers shared by the sheaf
// files (sheafa, sheafb, sheafc, dim-3, dim4-help), then the first half of
// sheafa.lisp.
//
// Representation notes:
// - The list-type named structures of amacros.lisp (`ldata`, `zopen`,
//   `rmap`, `pre-ldata-sheaves`, `s-var`, `matrix`) are plain lists headed
//   by their name, as in CL: `(ldata eqns inequality usedup
//   open-inequality variables)`.  Their constructors/accessors are not in
//   the contract; they are the `sheafa__` helpers below.
// - The other structures (`variable-correspondence`, `ideal`,
//   `polynomial-vectors`) are `make_struct` instances.
// - `defremember` functions (memoized through an EQUAL hash table on the
//   `:memory-table` property) use `sheafa__remember`.

// ---------------------------------------------------------------------------
// Symbols without generated constants

///|
let sheafa__q_variable_correspondence : Value = sym("variable-correspondence")

///|
let sheafa__q_ideal : Value = sym("ideal")

///|
let sheafa__q_list_tableaux : Value = sym("list-tableaux")

///|
let sheafa__q_compose_rmap : Value = sym("compose-rmap")

// ---------------------------------------------------------------------------
// Structure helpers (defstructs of amacros.lisp)

///|
fn sheafa__slot_set(x : Value, i : Int, v : Value) -> Value raise {
  let cell = nthcdr(i, x)
  if cell is Nil {
    raise LispError::SimpleError(
      format_to_string("Cannot set slot ~A of ~S", [int(i), x]),
    )
  }
  setf_car(cell, v) |> ignore
  v
}

///|
/// `(make-ldata :eqns :inequality :usedup :open-inequality :variables)`
fn sheafa__make_ldata(
  eqns? : Value = Nil,
  inequality? : Value = Fix(1L),
  usedup? : Value = Fix(0L),
  open_inequality? : Value = Fix(1L),
  variables? : Value = Nil,
) -> Value {
  list([q_ldata, eqns, inequality, usedup, open_inequality, variables])
}

///|
fn sheafa__ldata_eqns(x : Value) -> Value {
  nth(1, x)
}

///|
fn sheafa__ldata_inequality(x : Value) -> Value {
  nth(2, x)
}

///|
fn sheafa__ldata_usedup(x : Value) -> Value {
  nth(3, x)
}

///|
fn sheafa__ldata_open_inequality(x : Value) -> Value {
  nth(4, x)
}

///|
fn sheafa__ldata_variables(x : Value) -> Value {
  nth(5, x)
}

///|
fn sheafa__set_ldata_eqns(x : Value, v : Value) -> Value raise {
  sheafa__slot_set(x, 1, v)
}

///|
fn sheafa__set_ldata_inequality(x : Value, v : Value) -> Value raise {
  sheafa__slot_set(x, 2, v)
}

///|
fn sheafa__set_ldata_usedup(x : Value, v : Value) -> Value raise {
  sheafa__slot_set(x, 3, v)
}

///|
fn sheafa__set_ldata_open_inequality(x : Value, v : Value) -> Value raise {
  sheafa__slot_set(x, 4, v)
}

///|
fn sheafa__set_ldata_variables(x : Value, v : Value) -> Value raise {
  sheafa__slot_set(x, 5, v)
}

///|
/// `(make-pre-ldata-sheaves :s-var :data)`
fn sheafa__make_pls(s_var? : Value = Nil, data? : Value = Nil) -> Value {
  list([q_pre_ldata_sheaves, s_var, data])
}

///|
fn sheafa__pls_s_var(x : Value) -> Value {
  nth(1, x)
}

///|
fn sheafa__pls_data(x : Value) -> Value {
  nth(2, x)
}

///|
fn sheafa__set_pls_s_var(x : Value, v : Value) -> Value raise {
  sheafa__slot_set(x, 1, v)
}

///|
fn sheafa__set_pls_data(x : Value, v : Value) -> Value raise {
  sheafa__slot_set(x, 2, v)
}

///|
/// `(make-s-var :zopens)`
fn sheafa__make_s_var(zopens? : Value = Nil) -> Value {
  list([q_s_var, zopens])
}

///|
fn sheafa__sv_zopens(x : Value) -> Value {
  nth(1, x)
}

///|
fn sheafa__set_sv_zopens(x : Value, v : Value) -> Value raise {
  sheafa__slot_set(x, 1, v)
}

///|
/// `(make-rmap :fns :denom)`
fn sheafa__make_rmap(fns? : Value = Nil, denom? : Value = Nil) -> Value {
  list([q_rmap, fns, denom])
}

///|
fn sheafa__rmap_fns(x : Value) -> Value {
  nth(1, x)
}

///|
fn sheafa__rmap_denom(x : Value) -> Value {
  nth(2, x)
}

///|
fn sheafa__set_rmap_fns(x : Value, v : Value) -> Value raise {
  sheafa__slot_set(x, 1, v)
}

///|
fn sheafa__set_rmap_denom(x : Value, v : Value) -> Value raise {
  sheafa__slot_set(x, 2, v)
}

///|
/// `(make-zopen :coord :inv :inequality :history)`
fn sheafa__make_zopen(
  coord? : Value = Nil,
  inv? : Value = Nil,
  inequality? : Value = Nil,
  history? : Value = Nil,
) -> Value {
  list([q_zopen, coord, inv, inequality, history])
}

///|
fn sheafa__zopen_coord(x : Value) -> Value {
  nth(1, x)
}

///|
fn sheafa__zopen_inv(x : Value) -> Value {
  nth(2, x)
}

///|
fn sheafa__zopen_inequality(x : Value) -> Value {
  nth(3, x)
}

///|
fn sheafa__zopen_history(x : Value) -> Value {
  nth(4, x)
}

///|
fn sheafa__set_zopen_coord(x : Value, v : Value) -> Value raise {
  sheafa__slot_set(x, 1, v)
}

///|
fn sheafa__set_zopen_inv(x : Value, v : Value) -> Value raise {
  sheafa__slot_set(x, 2, v)
}

///|
fn sheafa__set_zopen_inequality(x : Value, v : Value) -> Value raise {
  sheafa__slot_set(x, 3, v)
}

///|
fn sheafa__set_zopen_history(x : Value, v : Value) -> Value raise {
  sheafa__slot_set(x, 4, v)
}

///|
/// `(make-matrix :rows)`
fn sheafa__make_matrix(rows? : Value = Nil) -> Value {
  list([q_matrix, rows])
}

///|
fn sheafa__matrix_rows(x : Value) -> Value {
  nth(1, x)
}

///|
fn sheafa__set_matrix_rows(x : Value, v : Value) -> Value raise {
  sheafa__slot_set(x, 1, v)
}

///|
/// `(make-variable-correspondence :genvar :varlist :add-method)`
fn sheafa__make_vc(
  genvar? : Value = Nil,
  varlist? : Value = Nil,
  add_method? : Value = Nil,
) -> Value {
  make_struct("variable-correspondence", [genvar, varlist, add_method])
}

///|
fn sheafa__vc_genvar(x : Value) -> Value raise {
  struct_ref(x, 0)
}

///|
fn sheafa__vc_varlist(x : Value) -> Value raise {
  struct_ref(x, 1)
}

///|
fn sheafa__set_vc_genvar(x : Value, v : Value) -> Value raise {
  struct_set(x, 0, v)
}

///|
fn sheafa__set_vc_varlist(x : Value, v : Value) -> Value raise {
  struct_set(x, 1, v)
}

///|
/// `(make-ideal :char-set :generators :localization
/// :variable-correspondence)`
fn sheafa__make_ideal(
  char_set? : Value = Nil,
  generators? : Value = Nil,
  localization? : Value = Nil,
  variable_correspondence? : Value = Nil,
) -> Value {
  make_struct("ideal", [
    char_set, generators, localization, variable_correspondence,
  ])
}

///|
fn sheafa__ideal_char_set(x : Value) -> Value raise {
  struct_ref(x, 0)
}

///|
fn sheafa__ideal_generators(x : Value) -> Value raise {
  struct_ref(x, 1)
}

///|
fn sheafa__ideal_localization(x : Value) -> Value raise {
  struct_ref(x, 2)
}

///|
fn sheafa__ideal_variable_correspondence(x : Value) -> Value raise {
  struct_ref(x, 3)
}

///|
fn sheafa__set_ideal_char_set(x : Value, v : Value) -> Value raise {
  struct_set(x, 0, v)
}

///|
fn sheafa__set_ideal_localization(x : Value, v : Value) -> Value raise {
  struct_set(x, 2, v)
}

///|
fn sheafa__set_ideal_variable_correspondence(
  x : Value,
  v : Value,
) -> Value raise {
  struct_set(x, 3, v)
}

///|
/// `(pv-the-sparse-matrix x)`: slot 13 of `polynomial-vectors`.
fn sheafa__pv_the_sparse_matrix(x : Value) -> Value raise {
  struct_ref(x, 13)
}

// ---------------------------------------------------------------------------
// Debugging-output macros

///|
/// `(show form)` (commac.lisp): the macro prints the source form, given
/// here as `form` (upcased, as SBCL prints it).
fn sheafa__show(form : String, v : Value) -> Unit raise {
  format(t, "~%The value of ~A is ~A", [Str(form), v]) |> ignore
}

///|
/// `(mshow form)` (amacros.lisp).
fn sheafa__mshow(form : String, v : Value) -> Unit raise {
  format(t, "~%The value of ~A is.. ", [Str(form)]) |> ignore
  des(v) |> ignore
}

// ---------------------------------------------------------------------------
// defremember (amacros.lisp)

///|
/// The body of a `defremember` function `fsym` called with hash key `key`
/// (the argument, or the list of arguments).  Unless `fsym` has the
/// `:dont-remember` property, answers are memoized in the EQUAL hash table
/// on its `:memory-table` property (a NIL answer is not remembered).
fn sheafa__remember(
  fsym : Value,
  key : Value,
  body : () -> Value raise,
) -> Value raise {
  if get(fsym, q_kw_dont_remember) is Nil {
    let mut table = get(fsym, q_kw_memory_table)
    if table is Nil {
      table = make_hash_table(kind=Equal)
      putprop(fsym, table, q_kw_memory_table) |> ignore
    }
    let ans = gethash(key, table)
    if ans.truthy() {
      ans
    } else {
      let ans = body()
      sethash(key, table, ans) |> ignore
      ans
    }
  } else {
    body()
  }
}
