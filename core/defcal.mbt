// Port of src/defcal.lisp: compile-time support for defining things which
// dispatch off the property list (used by the Maxima parser), and the
// CSTR tables used by the tokenizer to recognize operator symbols.

///|
/// Used by the Parser at compile time: the expansion of a parser function
/// definition `(def-<p>-fun op bvl (car bvl) . body)`.
fn make_parser_fun_def(
  op : Value,
  p : Value,
  bvl : Value,
  body : Value,
) -> Value raise {
  if !consp(op) {
    list_star([symbolconc(list([q_def_, p, q_n_fun])), op, bvl, car(bvl), body])
  } else {
    cons(
      q_progn,
      cons(
        make_parser_fun_def(car(op), p, bvl, body),
        mapcar(
          x => {
            list4(
              q_inherit_propl,
              list2(q_quote, x),
              list2(q_quote, car(op)),
              list1(symbolconc(list2(p, q_n_propl))),
            )
          },
          cdr(op),
        ),
      ),
    )
  }
}

// The tokenizer use the famous CSTR to represent the possible extended
// token symbols.
//
// (CSTRSETUP <description>)
//
//  <description> ::= (<descriptor> <descriptor> ...)
//  <descriptor>  ::= <name> ! (<name> <translation>)
//
//  If no translation is supplied, $<name> is the default.
//
//  Sets up a CSTR [Command STRucture] object which may be used in
//  conjunction with the CEQ predicate to determine if the LINBUF cursor is
//  currently pointing at any keyword in that structure.
//
//  Note: Names containing shorter names as initial segments must follow
//        the shorter names in arg to CSTRSETUP.

///|
fn n_stardefine_initial_symbols(l : Value) -> Value raise {
  set(
    q_symbols_defined,
    sort_list(copy_list(l), (x, y) => num_lt(flatc(x), flatc(y))),
  )
  |> ignore
  set(q_macsyma_operators, cstrsetup(symval(q_symbols_defined)))
}

///|
/// `(define-initial-symbols &rest l)`: set SYMBOLS-DEFINED and
/// MACSYMA-OPERATORS from the operator names L.
fn define_initial_symbols(l : Value) -> Value raise {
  // The macro computes the tables at expansion time and installs copies.
  let (sd, mo) = save_specials([q_symbols_defined, q_macsyma_operators], () => {
    n_stardefine_initial_symbols(l) |> ignore
    (symval(q_symbols_defined), symval(q_macsyma_operators))
  })
  set(q_symbols_defined, copy_list(sd)) |> ignore
  set(q_macsyma_operators, copy_tree(mo))
}

///|
fn undefine_symbol(opr : Value) -> Value raise {
  n_stardefine_initial_symbols(
    remove_if(x => equal(x, opr), symval(q_symbols_defined)),
  )
}

///|
fn define_symbol(x : Value) -> Value raise {
  // Only extend SYMBOLS-DEFINED when X is not already known.  A duplicate
  // entry makes CSTRSETUP build a degenerate node carrying a spurious empty
  // branch, which pushes READ-COMMAND-TOKEN-AUX out of its leaf case.  It
  // also keeps SYMBOLS-DEFINED, and the trie rebuilt from it, from growing
  // every time a package that declares operators is loaded again.
  if member_equal(x, symval(q_symbols_defined)) is Nil {
    n_stardefine_initial_symbols(cons(x, symval(q_symbols_defined))) |> ignore
  }
  symbolconc(list2(q_d_, maybe_invert_string_case(x)))
}

///|
fn cstrsetup(arg : Value) -> Value raise {
  let mut tree : Value = Nil
  for a in arg.iter() {
    if atom(a) {
      tree = add2cstr(
        a,
        tree,
        symbolconc(
          list2(q_d_, if stringp(a) { maybe_invert_string_case(a) } else { a }),
        ),
      )
    } else {
      tree = add2cstr(car(a), tree, cadr(a))
    }
  }
  list_star([Nil, list2(q_ans, Nil), tree])
}

///|
/// (ADD2CSTR <name> <tree> <translation>)
///
///  Adds the information <name> -> <translation> to a CSTR-style <tree>.
fn add2cstr(x : Value, tree : Value, ans : Value) -> Value raise {
  add2cstr1(nconc(exploden(x), list1(list2(q_ans, ans))), tree)
}

///|
/// (ADD2CSTR1 <translation-info> <tree>)
///
///  Helping function for ADD2CSTR.  Puts information about a keyword into
///  the <tree>
fn add2cstr1(x : Value, tree : Value) -> Value raise {
  if tree is Nil {
    x
  } else if atom(car(tree)) {
    if equal(car(tree), car(x)) {
      rplacd(tree, add2cstr1(cdr(x), cdr(tree)))
    } else {
      list2(
        tree,
        if atom(car(x)) {
          x
        } else if equal(caar(x), q_ans) {
          car(x)
        } else {
          x
        },
      )
    }
  } else if equal(caar(tree), car(x)) {
    rplacd(car(tree), add2cstr1(cdr(x), cdar(tree))) |> ignore
    tree
  } else if cdr(tree) is Nil {
    rplacd(tree, list1(x)) |> ignore
    tree
  } else {
    rplacd(tree, add2cstr1(x, cdr(tree))) |> ignore
    tree
  }
}

///|
fn init_defcal() -> Unit raise {
  macsyma_module(sym("defcal"), list1(q_macro)) |> ignore
  defvar_init(q_symbols_defined, Nil)
  defvar_init(q_macsyma_operators, Nil)
}
