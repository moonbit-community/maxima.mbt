// Port of src/globals.lisp: global variables (defvars/defmvars) used in
// multiple files, the DEFMVAR machinery, and a few small utilities.
//
// Literal initial values are set by gen_vars.mbt (init_vars_globals).
// `init_globals` below reproduces the rest of what loading globals.lisp
// does: it records every DEFMVAR variable in *variable-initial-values*
// (used by `reset`), installs the variable options (:properties,
// :setting-predicate, :setting-list, boolean, :setter-method) and sets
// the non-literal initial values.

///|
let globals__q_no_reset : Value = sym("no-reset")

///|
let globals__q_in_core : Value = sym("in-core")

///|
let globals__q_see_also : Value = sym("see-also")

///|
let globals__q_modified_commands : Value = sym("modified-commands")

///|
let globals__q_setting_list : Value = sym("setting-list")

///|
let globals__q_kw_properties : Value = kw("properties")

///|
let globals__q_kw_setting_predicate : Value = kw("setting-predicate")

///|
let globals__q_kw_setting_list : Value = kw("setting-list")

///|
let globals__q_kw_setter_method : Value = kw("setter-method")

///|
/// The *variable-initial-values* hash table, created on first use.
fn globals__initial_values_table() -> Value {
  if !boundp(q_ear_variable_initial_values) {
    set(q_ear_variable_initial_values, make_hash_table(kind=Eql)) |> ignore
  }
  symval(q_ear_variable_initial_values)
}

///|
/// The ASSIGN function installed by :SETTING-LIST and BOOLEAN: only the
/// values in POSSIBLE-VALUES may be assigned.
fn globals__setting_list_assign(possible_values : Value) -> Value {
  lfunc("defmvar-setting-list", args => {
    let var_ = arg(args, 0)
    let val = arg(args, 1)
    if member(val, possible_values) is Nil {
      mseterr(
        var_,
        val,
        reason=format(Nil, "must be one of: ~{~A~^, ~}", [
          mapcar(x => stripdollar(x), possible_values),
        ]),
      )
    } else {
      Nil
    }
  })
}

///|
/// The ASSIGN function installed by :SETTING-PREDICATE.  PRED is a
/// function designator of one argument; since the port's funcall returns
/// only the primary value, the optional second value (the reason string
/// passed to MSETERR) may be supplied by giving `(pred "reason")`, a
/// two-element list, instead of PRED.  The function INTEGER-PREDICATE is
/// recognized and called directly so that its reason is used.
fn globals__setting_predicate_assign(spec : Value) -> Value {
  let (pred, reason0) = match spec {
    Cons(_) if length(spec) == 2 && stringp(cadr(spec)) =>
      (car(spec), cadr(spec))
    _ => (spec, Nil)
  }
  lfunc("defmvar-setting-predicate", args => {
    let var_ = arg(args, 0)
    let val = arg(args, 1)
    let (ok, reason) = if eq(pred, q_integer_predicate) {
      integer_predicate(val)
    } else {
      (funcall(pred, [val]), reason0)
    }
    if ok is Nil {
      mseterr(var_, val, reason~)
    } else {
      Nil
    }
  })
}

///|
/// Run-time equivalent of the DEFMVAR macro: define the Maxima variable
/// VAR_ with initial value VAL and process OPTIONS (a list, as in the Lisp
/// source, except that option arguments are already evaluated):
///
///   no-reset, boolean, in-core, fixnum, string, flonum,
///   :properties ((ind val) ...), :setting-predicate pred,
///   :setting-list (values...), :setter-method fn,
///   see-also x, modified-commands x, :deprecated-p "message".
///
/// For :setting-predicate, see `globals__setting_predicate_assign` for how
/// to pass the reason string.  The returned value is the variable symbol.
fn defmvar(
  var_ : Value,
  val~ : Value = Nil,
  doc~ : Value = Nil,
  options : Value,
) -> Value raise {
  ignore(doc)
  let mut maybe_reset = true
  let mut maybe_set_props : Array[() -> Unit raise] = []
  let mut maybe_predicate : Value? = None
  let mut maybe_boolean_predicate : Value? = None
  let mut maybe_setter_method : Value? = None
  let mut setting_predicate_p = false
  let mut setting_list_p = false
  let mut setter_method_p = false
  let mut assign_property_p = false
  let mut deprecated_p = false
  let mut opts = options
  while !(opts is Nil) {
    let o = car(opts)
    let name = match o {
      Sym(s) => s.name
      _ => ""
    }
    match name {
      "no-reset" => if !deprecated_p { maybe_reset = false }
      "fixnum" | "string" | "flonum" =>
        // Types are not declared (yet); the Lisp macro only warns at
        // compile time when *warn-deprecated-defmvar-options* is set.
        ()
      "in-core" => ()
      "boolean" =>
        // Vars declared as boolean create a setting-list so that only
        // true and false can be assigned to the variable.
        maybe_boolean_predicate = Some(
          globals__setting_list_assign(list2(t, Nil)),
        )
      ":properties" => {
        if !deprecated_p {
          let props = cadr(opts)
          maybe_set_props = []
          for p in props.iter() {
            let ind = car(p)
            let pval = cadr(p)
            if eq(ind, q_assign) {
              assign_property_p = true
            }
            maybe_set_props.push(() => putprop_(var_, pval, ind) |> ignore)
          }
          if assign_property_p {
            if setting_predicate_p {
              raise LispError::SimpleError(
                "Cannot use 'ASSIGN property in :PROPERTIES if :SETTING-PREDICATE already specified.",
              )
            }
            if setting_list_p {
              raise LispError::SimpleError(
                "Cannot use 'ASSIGN property in :PROPERTIES if :SETTING-LIST already specified.",
              )
            }
          }
        }
        opts = cdr(opts)
      }
      ":setting-predicate" => {
        if !deprecated_p {
          if setting_list_p {
            raise LispError::SimpleError(
              "Cannot use :SETTING-PREDICATE when :SETTING-LIST already specified.",
            )
          }
          if assign_property_p {
            raise LispError::SimpleError(
              "Cannot use :SETTING-PREDICATE when :PROPERTIES uses the 'ASSIGN property.",
            )
          }
          setting_predicate_p = true
          maybe_predicate = Some(globals__setting_predicate_assign(cadr(opts)))
        }
        // Skip over the predicate function.
        opts = cdr(opts)
      }
      ":setting-list" => {
        if !deprecated_p {
          if setting_predicate_p {
            raise LispError::SimpleError(
              "Cannot use :SETTING-LIST when :SETTING-PREDICATE already specified.",
            )
          }
          if assign_property_p {
            raise LispError::SimpleError(
              "Cannot use :SETTING-LIST when :PROPERTIES uses the 'ASSIGN property.",
            )
          }
          setting_list_p = true
          maybe_predicate = Some(globals__setting_list_assign(cadr(opts)))
        }
        // Skip over the values.
        opts = cdr(opts)
      }
      ":setter-method" => {
        setter_method_p = true
        maybe_setter_method = Some(cadr(opts))
        opts = cdr(opts)
      }
      "see-also" | "modified-commands" =>
        // Not yet supported; skip over the parameter too.
        opts = cdr(opts)
      "setting-list" =>
        raise LispError::SimpleError(
          "setting-list has been superseded by :setting-list",
        )
      ":deprecated-p" => {
        // This overrides everything and makes the variable deprecated:
        // it is unbound, the 'bindtest property is set and the 'assign
        // property is 'neverset.
        deprecated_p = true
        maybe_reset = false
        maybe_predicate = None
        setting_predicate_p = false
        setting_list_p = false
        assign_property_p = false
        let msg = cadr(opts)
        maybe_set_props = [
          () => {
            makunbound(var_) |> ignore
            putprop_(var_, q_kw_deprecated, q_bindtest) |> ignore
            putprop_(var_, q_neverset, q_assign) |> ignore
            set(
              q_ear_bindtest_deprecation_messages,
              cons(
                cons(
                  var_,
                  cons(
                    Str("Deprecated variable `~M': " + lstring(string(msg))),
                    val,
                  ),
                ),
                symval(q_ear_bindtest_deprecation_messages),
              ),
            )
            |> ignore
          },
        ]
        opts = cdr(opts)
      }
      _ =>
        format(
          error_output,
          "~&WARNING: Ignoring unknown defmvar option for ~S: ~S~%",
          [var_, o],
        )
        |> ignore
    }
    opts = cdr(opts)
  }
  match maybe_boolean_predicate {
    Some(bp) =>
      if setting_predicate_p || setting_list_p || assign_property_p {
        raise LispError::SimpleError(
          "Do not use BOOLEAN option when :SETTING-PREDICATE, :SETTING-LIST, or :PROPERTIES is used",
        )
      } else {
        // The other predicates supersede boolean.
        maybe_predicate = Some(bp)
      }
    None => ()
  }
  let nset = (if setting_predicate_p { 1 } else { 0 }) +
    (if setting_list_p { 1 } else { 0 }) +
    (if setter_method_p { 1 } else { 0 })
  if nset > 1 {
    raise LispError::SimpleError(
      "Only one of :SETTING-PREDICATE, :SETTING-LIST, or :SETTING-METHOD maybe be specified.)",
    )
  }
  // (progn maybe-reset (defvar var val) maybe-set-props maybe-predicate
  //        maybe-setter-method)
  if maybe_reset {
    let table = globals__initial_values_table()
    if gethash(var_, table) is Nil {
      sethash(var_, table, val) |> ignore
    }
  }
  if !boundp(var_) {
    set(var_, val) |> ignore
  }
  for f in maybe_set_props {
    f()
  }
  match maybe_predicate {
    Some(f) => putprop_(var_, f, q_assign) |> ignore
    None => ()
  }
  match maybe_setter_method {
    Some(f) => putprop_(var_, f, q_setter_method) |> ignore
    None => ()
  }
  var_
}

///|
/// For the symbol SYM, add to the plist the property INDIC with a value
/// of VAL.  SYM may also be a list, whose cdr is then the property list.
///
/// Some known INDIC properties:
///   ASSIGN   - funcall'ed when a variable is assigned (in maxima) to check
///              whether the value to be assigned is valid.
///   EVFLAG   - '<expr>, <x>' is equivalent to 'ev(<expr>, <x>=true)'.
///   SYSCONST - the symbol is a constant that cannot be changed.
fn putprop_(sym_ : Value, val : Value, indic : Value) -> Value raise {
  if consp(sym_) {
    // (setf (getf (cdr sym) indic) val)
    let mut l = cdr(sym_)
    while consp(l) {
      if eq(car(l), indic) {
        rplaca(cdr(l), val) |> ignore
        return val
      }
      l = cddr(l)
    }
    rplacd(sym_, cons(indic, cons(val, cdr(sym_)))) |> ignore
    val
  } else {
    putprop(sym_, val, indic)
  }
}

///|
/// For defmvar :setting-predicate.  Checks that the argument is an
/// integer.  The second value is the message to use when the argument is
/// not an integer.
fn integer_predicate(val : Value) -> (Value, Value) raise {
  (lbool(integerp(val)), Str("must be an integer"))
}

///|
fn sanitize_string_for_path(s : Value) -> Value raise {
  let str = lstring(s)
  let chars = string_chars(str)
  let n = if chars.length() < 142 { chars.length() } else { 142 }
  let out = StringBuilder::new()
  for i in 0..<n {
    let x = chars[i]
    out.write_char(if alphanumericp(x) { x } else { '_' })
  }
  Str(out.to_string())
}

///|
fn lisp_implementation_version1() -> Value raise {
  // (lisp-implementation-version): the port runs on the MoonBit runtime.
  sanitize_string_for_path(Str("MoonBit"))
}

///|
fn maxima_version1() -> Value raise {
  sanitize_string_for_path(symval(q_ear_autoconf_version))
}

///|
/// A :setting-predicate option value with a constant reason string (the
/// second value of the Lisp predicate).
fn globals__pred(f : (Value) -> Bool raise, reason : String) -> Value {
  list2(lfunc("setting-predicate", args => lbool(f(arg(args, 0)))), Str(reason))
}

///|
/// An ASSIGN property function of (name val).
fn globals__assign(f : (Value, Value) -> Value raise) -> Value {
  lfunc("assign", args => f(arg(args, 0), arg(args, 1)))
}

///|
/// `(list '(mlist))`
fn globals__empty_mlist() -> Value {
  list1(list1(q_mlist))
}

///|
/// `(list '(mlist simp))`
fn globals__empty_mlist_simp() -> Value {
  list1(list2(q_mlist, q_simp))
}

///|
/// Handles setting inchar/outchar/linechar.  The VALUE must be a string or
/// symbol.  Symbols are assigned as is, but strings are converted to
/// symbols and then assigned.
fn globals__assign_prompts(var_ : Value, val : Value) -> Value raise {
  let v = match val {
    // Always add a $ as prefix.  Then intern the string
    Str(s) => intern_invert_case(Str("$" + s))
    Sym(_) | Nil => val
    _ => mseterr(var_, val, reason=Str("Must be a string or symbol"))
  }
  set(var_, v)
}

///|
/// ASSIGN property of $ratwtlvl.
fn globals__ratwtlvl_assign(name : Value, val : Value) -> Value raise {
  if val.truthy() && !fixnump(val) {
    mseterr(name, val, reason=Str("must be an integer")) |> ignore
  }
  if val.truthy() && symval(q_d_ratfac).truthy() {
    merr(
      "assignment: 'ratfac' and 'ratwtlvl' may not both be used at the same time.",
      [],
    )
  } else {
    Nil
  }
}

///|
/// ASSIGN property of $ratweights.
fn globals__ratweights_assign(name : Value, val : Value) -> Value raise {
  if !d_listp(val).truthy() {
    mseterr(name, val, reason=Str("must be a list"))
  } else if cdr(val) is Nil {
    kill1(q_d_ratweights)
  } else {
    d_ratweight(cdr(val))
  }
}

///|
/// ASSIGN property of $ratfac.
fn globals__ratfac_assign(name : Value, val : Value) -> Value raise {
  ignore(name)
  if val.truthy() && symval(q_d_ratwtlvl).truthy() {
    merr(
      "assignment: 'ratfac' and 'ratwtlvl' may not both be used at the same time.",
      [],
    )
  } else {
    Nil
  }
}

///|
/// ASSIGN property of $niceindicespref.
fn globals__niceindicespref_assign(name : Value, val : Value) -> Value raise {
  if !(d_listp(val).truthy() &&
    !d_emptyp(val).truthy() &&
    every(x => d_symbolp(x).truthy(), cdr(val))) {
    merr("~M: value must be a nonempty list of symbols; found: ~:M", [name, val])
  } else {
    Nil
  }
}

///|
/// :setting-predicate of MODULUS.  The modulus must be $false, or a
/// positive integer.  If the value is a positive integer, print a warning
/// if it is not prime.
fn globals__modulus_predicate(val : Value) -> Value raise {
  if val is Nil {
    t
  } else if integerp(val) && plusp(val) {
    if primep(val) is Nil {
      mtell(
        list([Str("Warning: assigning ~:M, a non-prime, to 'modulus'~&"), val]),
      )
      |> ignore
    }
    t
  } else {
    Nil
  }
}

///|
fn init_globals() -> Unit raise {
  // Non-literal DEFVAR/DEFPARAMETER initial values.
  set(q_opers, list1(q_d_linear)) |> ignore
  defvar_init(q_d_activecontexts, globals__empty_mlist())
  // These three variables are what get stuck in array slots as magic
  // unbound objects.  They are for T, FIXNUM, and FLONUM type arrays
  // respectively.  (gen_vars cannot read '|#####|.)
  set(q_munbound, sym("#####")) |> ignore
  defvar_init(q_fixunbound, most_negative_fixnum)
  defvar_init(q_flounbound, Flo(-most_positive_double_float))
  // Function Call stack each element is (fname . bindlist) where bindlist
  // was the value at time of entry.
  defvar_init(q_ear_mlambda_call_stack, make_array([30], fill=0))
  defvar_init(q_ear_checkfactors, Nil)
  defvar_init(q_ear_flonum_op, make_hash_table(kind=Eql))
  defvar_init(q_ear_big_float_op, make_hash_table(kind=Eql))
  defvar_init(q_ear_temp_files_list, make_hash_table(kind=Equal))
  defvar_init(q_ear_alphabet, list2(Char('_'), Char('%')))
  // Bigfloat constants for the default precision of 56 bits (the
  // #.(expt 2 55) read-time values cannot be read by gen_vars).
  let two55 = expt(Fix(2L), Fix(55L))
  set(
    q_ear_bigfloatzero,
    list3(list3(q_bigfloat, q_simp, Fix(56L)), Fix(0L), Fix(0L)),
  )
  |> ignore
  set(
    q_ear_bigfloatone,
    list3(list3(q_bigfloat, q_simp, Fix(56L)), two55, Fix(1L)),
  )
  |> ignore
  set(q_ear_bfhalf, list3(list3(q_bigfloat, q_simp, Fix(56L)), two55, Fix(0L)))
  |> ignore
  set(
    q_ear_bfmhalf,
    list3(list3(q_bigfloat, q_simp, Fix(56L)), num_neg(two55), Fix(0L)),
  )
  |> ignore
  // DEFMVAR variables, in source order.
  // *variable-initial-values*
  globals__initial_values_table() |> ignore
  defmvar(q_ear_infinities, val=symval(q_ear_infinities), Nil) |> ignore
  defmvar(q_ear_real_infinities, val=symval(q_ear_real_infinities), Nil)
  |> ignore
  defmvar(q_ear_infinitesimals, val=symval(q_ear_infinitesimals), Nil) |> ignore
  defvar_init(q_d__pctrnum_list, globals__empty_mlist())
  defmvar(q_d__pctrnum_list, val=globals__empty_mlist(), Nil) |> ignore
  defmvar(q_d_zeta_pctpi, val=symval(q_d_zeta_pctpi), Nil) |> ignore
  defmvar(
    q_d_factlim,
    val=symval(q_d_factlim),
    list([
      globals__q_kw_setting_predicate,
      globals__pred(x => integerp(x), "Must be an explicit integer"),
    ]),
  )
  |> ignore
  defmvar(
    q_d_cauchysum,
    val=symval(q_d_cauchysum),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(
    q_d_gensumnum,
    val=symval(q_d_gensumnum),
    list([
      globals__q_kw_setting_predicate,
      globals__pred(
        x => x is Nil || (integerp(x) && num_ge(x, Fix(0L))),
        "must be false or a non-negative integer",
      ),
    ]),
  )
  |> ignore
  defmvar(
    q_d_genindex,
    val=symval(q_d_genindex),
    list([
      globals__q_kw_setting_predicate,
      lfunc("symbolp", args => lbool(symbolp(arg(args, 0)))),
    ]),
  )
  |> ignore
  defmvar(q_d_zerobern, val=symval(q_d_zerobern), Nil) |> ignore
  defmvar(
    q_d_simpsum,
    val=symval(q_d_simpsum),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(
    q_d_simpproduct,
    val=symval(q_d_simpproduct),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(q_d_cflength, val=symval(q_d_cflength), Nil) |> ignore
  defmvar(q_d_taylordepth, val=symval(q_d_taylordepth), Nil) |> ignore
  defmvar(q_d_verbose, val=symval(q_d_verbose), Nil) |> ignore
  defmvar(
    q_d_rootsconmode,
    val=symval(q_d_rootsconmode),
    list([globals__q_kw_setting_list, list([Nil, t, q_d_all])]),
  )
  |> ignore
  defmvar(q_d_exptsubst, val=symval(q_d_exptsubst), Nil) |> ignore
  defmvar(q_d_partswitch, val=symval(q_d_partswitch), Nil) |> ignore
  defmvar(q_d_inflag, val=symval(q_d_inflag), Nil) |> ignore
  defmvar(q_d_derivsubst, val=symval(q_d_derivsubst), Nil) |> ignore
  defmvar(q_d_opsubst, val=symval(q_d_opsubst), Nil) |> ignore
  defmvar(
    q_d_contexts,
    val=symval(q_d_contexts),
    list([
      globals__q_no_reset,
      globals__q_kw_properties,
      list([list2(q_assign, q_neverset)]),
    ]),
  )
  |> ignore
  defmvar(q_d_prederror, val=symval(q_d_prederror), Nil) |> ignore
  defmvar(q_limitp, val=Nil, Nil) |> ignore
  defmvar(
    q_sign_imag_errp,
    val=symval(q_sign_imag_errp),
    list([globals__q_no_reset]),
  )
  |> ignore
  defmvar(q_d_polyfactor, val=symval(q_d_polyfactor), Nil) |> ignore
  defmvar(q_d_gamma_expand, val=symval(q_d_gamma_expand), Nil) |> ignore
  defmvar(
    q_d_demoivre,
    val=symval(q_d_demoivre),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(q_d_nointegrate, val=symval(q_d_nointegrate), Nil) |> ignore
  defmvar(q_d_lhospitallim, val=symval(q_d_lhospitallim), Nil) |> ignore
  defmvar(q_d_tlimswitch, val=symval(q_d_tlimswitch), Nil) |> ignore
  defmvar(q_d_limsubst, val=symval(q_d_limsubst), Nil) |> ignore
  defmvar(q_d_sumsplitfact, val=symval(q_d_sumsplitfact), Nil) |> ignore
  defmvar(q_integerl, val=symval(q_integerl), Nil) |> ignore
  defmvar(q_nonintegerl, val=symval(q_nonintegerl), Nil) |> ignore
  defmvar(q_d_ttyoff, val=symval(q_d_ttyoff), Nil) |> ignore
  defmvar(
    q_d_display2d,
    val=symval(q_d_display2d),
    list([globals__q_kw_setting_list, list([Nil, t, q_d_emaxima, q_d_imaxima])]),
  )
  |> ignore
  defmvar(q_d_lispdisp, val=symval(q_d_lispdisp), Nil) |> ignore
  defmvar(q_d_derivabbrev, val=symval(q_d_derivabbrev), Nil) |> ignore
  defmvar(q_d_stringdisp, val=symval(q_d_stringdisp), Nil) |> ignore
  defmvar(
    q_d_linel,
    val=symval(q_d_linel),
    list([
      globals__q_kw_setting_predicate,
      globals__pred(
        val => {
          fixnump(val) && num_lt(Fix(0L), val) && num_lt(val, Fix(1000001L))
        },
        "must be an integer between 0 and 1000001, exclusive",
      ),
    ]),
  )
  |> ignore
  defmvar(
    q_d_known_index_properties,
    val=symval(q_d_known_index_properties),
    Nil,
  )
  |> ignore
  defmvar(q_d_packagefile, val=symval(q_d_packagefile), Nil) |> ignore
  defmvar(q_d_float2bf, val=symval(q_d_float2bf), Nil) |> ignore
  defmvar(q_d_bftorat, val=symval(q_d_bftorat), Nil) |> ignore
  defmvar(q_d_bftrunc, val=symval(q_d_bftrunc), Nil) |> ignore
  defmvar(
    q_d_fpprintprec,
    val=symval(q_d_fpprintprec),
    list([
      globals__q_kw_setting_predicate,
      globals__pred(
        val => fixnump(val) && num_ge(val, Fix(0L)) && !num_eq(val, Fix(1L)),
        "must be a non-negative integer and not equal to -1",
      ),
    ]),
  )
  |> ignore
  defvar_init(q_d_maxfpprintprec, Fix(16L))
  defmvar(q_d_maxfpprintprec, val=Fix(16L), Nil) |> ignore
  defvar_init(q_d_fpprec, symval(q_d_maxfpprintprec))
  defmvar(
    q_d_fpprec,
    val=symval(q_d_maxfpprintprec),
    list([globals__q_kw_properties, list([list2(q_assign, q_fpprec1)])]),
  )
  |> ignore
  defmvar(
    q_ear_bigfloatzero,
    val=symval(q_ear_bigfloatzero),
    list([globals__q_in_core]),
  )
  |> ignore
  defmvar(
    q_ear_bigfloatone,
    val=symval(q_ear_bigfloatone),
    list([globals__q_in_core]),
  )
  |> ignore
  defmvar(q_ear_bfhalf, val=symval(q_ear_bfhalf), Nil) |> ignore
  defmvar(q_ear_bfmhalf, val=symval(q_ear_bfmhalf), Nil) |> ignore
  defmvar(q_d_factorial_expand, val=symval(q_d_factorial_expand), Nil) |> ignore
  defmvar(q_d_beta_expand, val=symval(q_d_beta_expand), Nil) |> ignore
  defmvar(
    q_d_hypergeometric_representation,
    val=symval(q_d_hypergeometric_representation),
    Nil,
  )
  |> ignore
  defmvar(q_d_listconstvars, val=symval(q_d_listconstvars), list([q_boolean]))
  |> ignore
  defmvar(
    q_d_showtime,
    val=symval(q_d_showtime),
    list([globals__q_kw_setting_list, list([Nil, t, q_d_all])]),
  )
  |> ignore
  defmvar(q_d_op_, val=symval(q_d_op_), Nil) |> ignore
  defmvar(q_d_op__, val=symval(q_d_op__), Nil) |> ignore
  defmvar(q_d_globalsolve, val=symval(q_d_globalsolve), Nil) |> ignore
  defmvar(q_d_sparse, val=symval(q_d_sparse), Nil) |> ignore
  defmvar(q_d_backsubst, val=symval(q_d_backsubst), Nil) |> ignore
  defmvar(q_d__pctrnum, val=symval(q_d__pctrnum), Nil) |> ignore
  defmvar(q_d_linsolve_params, val=symval(q_d_linsolve_params), Nil) |> ignore
  defmvar(q_ear_rank, val=symval(q_ear_rank), Nil) |> ignore
  defmvar(q_ear_inv, val=symval(q_ear_inv), Nil) |> ignore
  defmvar(q_d_detout, val=symval(q_d_detout), Nil) |> ignore
  defmvar(
    q_d_ratmx,
    val=symval(q_d_ratmx),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(q_d_matrix_element_mult, val=symval(q_d_matrix_element_mult), Nil)
  |> ignore
  defmvar(q_d_matrix_element_add, val=symval(q_d_matrix_element_add), Nil)
  |> ignore
  defmvar(
    q_d_dotscrules,
    val=symval(q_d_dotscrules),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(q_d_dotdistrib, val=symval(q_d_dotdistrib), Nil) |> ignore
  defmvar(q_d_dotexptsimp, val=symval(q_d_dotexptsimp), Nil) |> ignore
  defmvar(
    q_d_dotassoc,
    val=symval(q_d_dotassoc),
    list([
      globals__q_kw_properties,
      list([
        list2(
          q_assign,
          globals__assign((_, val) => cput(q_mnctimes, val, q_associative)),
        ),
      ]),
    ]),
  )
  |> ignore
  defmvar(q_d_doallmxops, val=symval(q_d_doallmxops), Nil) |> ignore
  defmvar(q_d_domxmxops, val=symval(q_d_domxmxops), Nil) |> ignore
  defmvar(q_d_doscmxops, val=symval(q_d_doscmxops), Nil) |> ignore
  defmvar(
    q_d_scalarmatrixp,
    val=symval(q_d_scalarmatrixp),
    list([globals__q_kw_setting_list, list([Nil, t, q_d_all])]),
  )
  |> ignore
  defmvar(
    q_d_assumescalar,
    val=symval(q_d_assumescalar),
    list([globals__q_kw_setting_list, list([Nil, t, q_d_all])]),
  )
  |> ignore
  defvar_init(q_d_error, list2(list2(q_mlist, q_simp), Str("No error.")))
  defmvar(
    q_d_error,
    val=list2(list2(q_mlist, q_simp), Str("No error.")),
    list([globals__q_kw_properties, list([list2(q_assign, q_neverset)])]),
  )
  |> ignore
  defmvar(q_d_errormsg, val=symval(q_d_errormsg), Nil) |> ignore
  defvar_init(
    q_d_features,
    cons(list2(q_mlist, q_simp), copy_list(symval(q_featurel))),
  )
  defmvar(
    q_d_features,
    val=cons(list2(q_mlist, q_simp), copy_list(symval(q_featurel))),
    Nil,
  )
  |> ignore
  defmvar(
    q_d__pctenumer,
    val=symval(q_d__pctenumer),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(
    q_d_float,
    val=symval(q_d_float),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(q_d_translate, val=symval(q_d_translate), Nil) |> ignore
  defmvar(q_d_transrun, val=symval(q_d_transrun), Nil) |> ignore
  defmvar(
    q_d_savedef,
    val=symval(q_d_savedef),
    list([globals__q_kw_setting_list, list([Nil, t, q_d_all])]),
  )
  |> ignore
  defmvar(
    q_d_infeval,
    val=symval(q_d_infeval),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(q_d_piece, val=symval(q_d_piece), Nil) |> ignore
  defmvar(q_munbindp, val=symval(q_munbindp), list([globals__q_no_reset]))
  |> ignore
  defmvar(
    q_d_setcheck,
    val=symval(q_d_setcheck),
    list([
      globals__q_kw_setting_predicate,
      globals__pred(
        val => {
          d_listp(val).truthy() || member(val, list([q_d_all, t, Nil])).truthy()
        },
        "must be a list or one of all, true, or false",
      ),
    ]),
  )
  |> ignore
  defmvar(q_d_use_fast_arrays, val=symval(q_d_use_fast_arrays), Nil) |> ignore
  defvar_init(q_d_structures, globals__empty_mlist())
  defmvar(
    q_d_structures,
    val=globals__empty_mlist(),
    list([
      globals__q_no_reset,
      globals__q_kw_properties,
      list([list2(q_assign, q_neverset)]),
    ]),
  )
  |> ignore
  defmvar(q_d_load_pathname, val=symval(q_d_load_pathname), Nil) |> ignore
  defmvar(q_d_powerdisp, val=symval(q_d_powerdisp), Nil) |> ignore
  defmvar(q_d_pfeformat, val=symval(q_d_pfeformat), Nil) |> ignore
  defmvar(q_d__pctedispflag, val=symval(q_d__pctedispflag), Nil) |> ignore
  defmvar(q_d_exptdispflag, val=symval(q_d_exptdispflag), Nil) |> ignore
  defmvar(q_d_sqrtdispflag, val=symval(q_d_sqrtdispflag), Nil) |> ignore
  defmvar(
    q_d_ratwtlvl,
    val=symval(q_d_ratwtlvl),
    list([
      globals__q_kw_properties,
      list([list2(q_assign, globals__assign(globals__ratwtlvl_assign))]),
    ]),
  )
  |> ignore
  defmvar(
    q_d_ratalgdenom,
    val=symval(q_d_ratalgdenom),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(q_ear_gcdl, val=symval(q_ear_gcdl), Nil) |> ignore
  defvar_init(q_d_gcd, car(symval(q_ear_gcdl)))
  defmvar(
    q_d_gcd,
    val=car(symval(q_ear_gcdl)),
    list([
      globals__q_kw_setting_predicate,
      lfunc("setting-predicate", args => {
        let val = arg(args, 0)
        if val is Nil {
          t
        } else {
          member(val, symval(q_ear_gcdl))
        }
      }),
    ]),
  )
  |> ignore
  defmvar(q_n_staralpha, val=Nil, Nil) |> ignore
  defmvar(q_algfac_star, val=symval(q_algfac_star), Nil) |> ignore
  defmvar(q_low_star, val=symval(q_low_star), Nil) |> ignore
  defmvar(q_d_intfaclim, val=symval(q_d_intfaclim), Nil) |> ignore
  defmvar(
    q_d_factor_max_degree,
    val=symval(q_d_factor_max_degree),
    list([
      globals__q_kw_properties,
      list([list2(q_assign, q_non_negative_integer_set)]),
    ]),
  )
  |> ignore
  defmvar(q_d_savefactors, val=symval(q_d_savefactors), Nil) |> ignore
  defmvar(
    q_d_keepfloat,
    val=symval(q_d_keepfloat),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(
    q_d_factorflag,
    val=symval(q_d_factorflag),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defvar_init(q_d_dontfactor, globals__empty_mlist())
  defmvar(q_d_dontfactor, val=globals__empty_mlist(), Nil) |> ignore
  defmvar(q_d_norepeat, val=symval(q_d_norepeat), Nil) |> ignore
  defvar_init(q_d_ratweights, globals__empty_mlist_simp())
  defmvar(
    q_d_ratweights,
    val=globals__empty_mlist_simp(),
    list([
      globals__q_kw_properties,
      list([list2(q_assign, globals__assign(globals__ratweights_assign))]),
    ]),
  )
  |> ignore
  defmvar(
    q_d_algebraic,
    val=symval(q_d_algebraic),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(
    q_d_ratfac,
    val=symval(q_d_ratfac),
    list([
      globals__q_kw_properties,
      list([
        list2(q_evflag, t),
        list2(q_assign, globals__assign(globals__ratfac_assign)),
      ]),
    ]),
  )
  |> ignore
  defvar_init(q_d_ratvars, globals__empty_mlist_simp())
  defmvar(
    q_d_ratvars,
    val=globals__empty_mlist_simp(),
    list([
      globals__q_kw_properties,
      list([
        list2(
          q_assign,
          globals__assign((name, val) => {
            if d_listp(val).truthy() {
              d_ratvars(cdr(val))
            } else {
              mseterr(name, val, reason=Str("must be a list"))
            }
          }),
        ),
      ]),
    ]),
  )
  |> ignore
  defmvar(q_d_facexpand, val=symval(q_d_facexpand), Nil) |> ignore
  defmvar(q_genvar, val=symval(q_genvar), Nil) |> ignore
  defmvar(q_genpairs, val=symval(q_genpairs), Nil) |> ignore
  defmvar(q_n_starfnewvarsw, val=symval(q_n_starfnewvarsw), Nil) |> ignore
  defmvar(q_n_starratweights, val=symval(q_n_starratweights), Nil) |> ignore
  defmvar(q_tellratlist, val=symval(q_tellratlist), Nil) |> ignore
  defmvar(q_adn_star, val=symval(q_adn_star), Nil) |> ignore
  defmvar(q_d_ratprint, val=symval(q_d_ratprint), Nil) |> ignore
  defmvar(q_d_ratepsilon, val=symval(q_d_ratepsilon), Nil) |> ignore
  defmvar(q_d_ratexpand, val=symval(q_d_ratexpand), Nil) |> ignore
  defmvar(q_varlist, val=symval(q_varlist), Nil) |> ignore
  defmvar(q_d_resultant, val=symval(q_d_resultant), Nil) |> ignore
  defmvar(q_d_liflag, val=symval(q_d_liflag), Nil) |> ignore
  defmvar(q_d_negdistrib, val=symval(q_d_negdistrib), Nil) |> ignore
  defmvar(
    q_d_numer,
    val=symval(q_d_numer),
    list([globals__q_kw_properties, list([list2(q_assign, q_numerset)])]),
  )
  |> ignore
  defmvar(
    q_d_simp,
    val=symval(q_d_simp),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(
    q_d_sumexpand,
    val=symval(q_d_sumexpand),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(
    q_d_numer_pbranch,
    val=symval(q_d_numer_pbranch),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(
    q_d_expop,
    val=symval(q_d_expop),
    list([
      globals__q_kw_properties,
      list([list2(q_assign, q_non_negative_integer_set)]),
    ]),
  )
  |> ignore
  defmvar(
    q_d_expon,
    val=symval(q_d_expon),
    list([
      globals__q_kw_properties,
      list([list2(q_assign, q_non_negative_integer_set)]),
    ]),
  )
  |> ignore
  defmvar(
    q_d_maxposex,
    val=symval(q_d_maxposex),
    list([
      globals__q_kw_properties,
      list([list2(q_assign, q_non_negative_integer_set)]),
    ]),
  )
  |> ignore
  defmvar(
    q_d_maxnegex,
    val=symval(q_d_maxnegex),
    list([
      globals__q_kw_properties,
      list([list2(q_assign, q_non_negative_integer_set)]),
    ]),
  )
  |> ignore
  defmvar(q_dosimp, val=symval(q_dosimp), Nil) |> ignore
  defmvar(q_errorsw, val=symval(q_errorsw), Nil) |> ignore
  defmvar(q_d_rootsepsilon, val=symval(q_d_rootsepsilon), Nil) |> ignore
  defmvar(q_d_algepsilon, val=symval(q_d_algepsilon), Nil) |> ignore
  defmvar(q_d_true, val=symval(q_d_true), Nil) |> ignore
  defmvar(q_d_false, val=symval(q_d_false), Nil) |> ignore
  defmvar(
    q_d_logabs,
    val=symval(q_d_logabs),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(
    q_d_listarith,
    val=symval(q_d_listarith),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(q_d_domain, val=symval(q_d_domain), Nil) |> ignore
  defmvar(
    q_d_m1pbranch,
    val=symval(q_d_m1pbranch),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(q_d__pcte_to_numlog, val=symval(q_d__pcte_to_numlog), Nil) |> ignore
  defmvar(
    q_d__pctemode,
    val=symval(q_d__pctemode),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(
    q_d_ratsimpexpons,
    val=symval(q_d_ratsimpexpons),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(
    q_d_logexpand,
    val=symval(q_d_logexpand),
    list([
      globals__q_kw_properties,
      list([list2(q_evflag, t)]),
      globals__q_kw_setting_list,
      list([Nil, t, q_d_all, q_d_super]),
    ]),
  )
  |> ignore
  defmvar(
    q_d_radexpand,
    val=symval(q_d_radexpand),
    list([
      globals__q_kw_properties,
      list([list2(q_evflag, t)]),
      globals__q_kw_setting_predicate,
      globals__pred(
        val => member(val, list([q_d_all, t, Nil])).truthy(),
        "must be one of all, true, or false",
      ),
    ]),
  )
  |> ignore
  defmvar(q_d_subnumsimp, val=symval(q_d_subnumsimp), Nil) |> ignore
  defmvar(q_d_logsimp, val=symval(q_d_logsimp), Nil) |> ignore
  defmvar(q_d_breakup, val=symval(q_d_breakup), Nil) |> ignore
  defmvar(q_d_multiplicities, val=symval(q_d_multiplicities), Nil) |> ignore
  defmvar(
    q_d_programmode,
    val=symval(q_d_programmode),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(q_d_solvefactors, val=symval(q_d_solvefactors), Nil) |> ignore
  defmvar(q_d_solvetrigwarn, val=symval(q_d_solvetrigwarn), Nil) |> ignore
  defmvar(q_d_solveradcan, val=symval(q_d_solveradcan), Nil) |> ignore
  defmvar(
    q_d_niceindicespref,
    val=symval(q_d_niceindicespref),
    list([
      globals__q_kw_properties,
      list([list2(q_assign, globals__assign(globals__niceindicespref_assign))]),
    ]),
  )
  |> ignore
  defmvar(
    q_d_loadprint,
    val=symval(q_d_loadprint),
    list([
      globals__q_kw_setting_list,
      list([Nil, t, q_d_loadfile, q_d_autoload]),
    ]),
  )
  |> ignore
  defmvar(q_d_nolabels, val=symval(q_d_nolabels), Nil) |> ignore
  defvar_init(q_d_aliases, globals__empty_mlist_simp())
  defmvar(
    q_d_aliases,
    val=globals__empty_mlist_simp(),
    list([
      globals__q_no_reset,
      globals__q_kw_properties,
      list([list2(q_assign, q_neverset)]),
    ]),
  )
  |> ignore
  defvar_init(q_d_labels, globals__empty_mlist_simp())
  defmvar(
    q_d_labels,
    val=globals__empty_mlist_simp(),
    list([globals__q_kw_properties, list([list2(q_assign, q_neverset)])]),
  )
  |> ignore
  defvar_init(q_d_values, globals__empty_mlist_simp())
  defmvar(
    q_d_values,
    val=globals__empty_mlist_simp(),
    list([
      globals__q_no_reset,
      globals__q_kw_properties,
      list([list2(q_assign, q_neverset)]),
    ]),
  )
  |> ignore
  defvar_init(q_d_functions, globals__empty_mlist_simp())
  defmvar(
    q_d_functions,
    val=globals__empty_mlist_simp(),
    list([
      globals__q_no_reset,
      globals__q_kw_properties,
      list([list2(q_assign, q_neverset)]),
    ]),
  )
  |> ignore
  defvar_init(q_d_macros, globals__empty_mlist_simp())
  defmvar(
    q_d_macros,
    val=globals__empty_mlist_simp(),
    list([
      globals__q_no_reset,
      globals__q_kw_properties,
      list([list2(q_assign, q_neverset)]),
    ]),
  )
  |> ignore
  defvar_init(q_d_arrays, globals__empty_mlist_simp())
  defmvar(
    q_d_arrays,
    val=globals__empty_mlist_simp(),
    list([
      globals__q_no_reset,
      globals__q_kw_properties,
      list([list2(q_assign, q_neverset)]),
    ]),
  )
  |> ignore
  defvar_init(q_d_myoptions, globals__empty_mlist_simp())
  defmvar(
    q_d_myoptions,
    val=globals__empty_mlist_simp(),
    list([
      globals__q_no_reset,
      globals__q_kw_properties,
      list([list2(q_assign, q_neverset)]),
    ]),
  )
  |> ignore
  defvar_init(q_d_props, globals__empty_mlist_simp())
  defmvar(
    q_d_props,
    val=globals__empty_mlist_simp(),
    list([
      globals__q_no_reset,
      globals__q_kw_properties,
      list([list2(q_assign, q_neverset)]),
    ]),
  )
  |> ignore
  defvar_init(q_d_rules, globals__empty_mlist_simp())
  defmvar(
    q_d_rules,
    val=globals__empty_mlist_simp(),
    list([
      globals__q_no_reset,
      globals__q_kw_properties,
      list([list2(q_assign, q_neverset)]),
    ]),
  )
  |> ignore
  defvar_init(q_d_gradefs, globals__empty_mlist_simp())
  defmvar(
    q_d_gradefs,
    val=globals__empty_mlist_simp(),
    list([
      globals__q_no_reset,
      globals__q_kw_properties,
      list([list2(q_assign, q_neverset)]),
    ]),
  )
  |> ignore
  defvar_init(q_d_dependencies, globals__empty_mlist_simp())
  defmvar(
    q_d_dependencies,
    val=globals__empty_mlist_simp(),
    list([
      globals__q_no_reset,
      globals__q_kw_properties,
      list([list2(q_assign, q_neverset)]),
    ]),
  )
  |> ignore
  defmvar(
    q_d_let_rule_packages,
    val=symval(q_d_let_rule_packages),
    list([globals__q_kw_properties, list([list2(q_assign, q_let_rule_setter)])]),
  )
  |> ignore
  defmvar(
    q_d_infolists,
    val=symval(q_d_infolists),
    list([globals__q_kw_properties, list([list2(q_assign, q_neverset)])]),
  )
  |> ignore
  defmvar(q_d_dispflag, val=symval(q_d_dispflag), Nil) |> ignore
  defmvar(q_d_op_pct, val=symval(q_d_op_pct), list([globals__q_no_reset]))
  |> ignore
  defmvar(
    q_d_op_pct_pct,
    val=symval(q_d_op_pct_pct),
    list([globals__q_no_reset]),
  )
  |> ignore
  // (flet ((assign-prompts (var val) ...)) (defmvar $inchar ...) ...)
  defvar_init(q_d_inchar, q_d__pcti)
  defmvar(
    q_d_inchar,
    val=q_d__pcti,
    list([
      globals__q_kw_setter_method,
      globals__assign(globals__assign_prompts),
      globals__q_kw_properties,
      list([list2(q_reset_on_kill, t)]),
    ]),
  )
  |> ignore
  defvar_init(q_d_outchar, q_d__pcto)
  defmvar(
    q_d_outchar,
    val=q_d__pcto,
    list([
      globals__q_kw_setter_method,
      globals__assign(globals__assign_prompts),
      globals__q_kw_properties,
      list([list2(q_reset_on_kill, t)]),
    ]),
  )
  |> ignore
  defvar_init(q_d_linechar, q_d__pctt)
  defmvar(
    q_d_linechar,
    val=q_d__pctt,
    list([
      globals__q_kw_setter_method,
      globals__assign(globals__assign_prompts),
      globals__q_kw_properties,
      list([list2(q_reset_on_kill, t)]),
    ]),
  )
  |> ignore
  defmvar(
    q_d_linenum,
    val=symval(q_d_linenum),
    list([
      globals__q_no_reset, globals__q_kw_setting_predicate, q_integer_predicate,
    ]),
  )
  |> ignore
  defmvar(q_d_file_output_append, val=symval(q_d_file_output_append), Nil)
  |> ignore
  defmvar(q_d__pctpiargs, val=symval(q_d__pctpiargs), Nil) |> ignore
  defmvar(q_d__pctiargs, val=symval(q_d__pctiargs), Nil) |> ignore
  defmvar(
    q_d_triginverses,
    val=symval(q_d_triginverses),
    list([globals__q_kw_setting_list, list([Nil, t, q_d_all])]),
  )
  |> ignore
  defmvar(
    q_d_trigexpand,
    val=symval(q_d_trigexpand),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(q_d_trigexpandplus, val=symval(q_d_trigexpandplus), Nil) |> ignore
  defmvar(q_d_trigexpandtimes, val=symval(q_d_trigexpandtimes), Nil) |> ignore
  defmvar(q_d_trigsign, val=symval(q_d_trigsign), Nil) |> ignore
  defmvar(
    q_d_exponentialize,
    val=symval(q_d_exponentialize),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(
    q_d_logarc,
    val=symval(q_d_logarc),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(
    q_d_halfangles,
    val=symval(q_d_halfangles),
    list([globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
  defmvar(q_d_browser, val=symval(q_d_browser), Nil) |> ignore
  defmvar(q_d_url_base, val=symval(q_d_url_base), Nil) |> ignore
  defmvar(
    q_d_output_format_for_help,
    val=symval(q_d_output_format_for_help),
    list([
      globals__q_kw_properties,
      list([list2(q_assign, q_set_output_format_for_help)]),
    ]),
  )
  |> ignore
  defmvar(
    q_d_maxima_userdir,
    val=symval(q_d_maxima_userdir),
    list([
      globals__q_kw_properties,
      list([
        list2(q_assign, q_shadow_string_assignment),
        list2(q_lisp_shadow, q_ear_maxima_userdir),
      ]),
    ]),
  )
  |> ignore
  defmvar(
    q_d_maxima_tempdir,
    val=symval(q_d_maxima_tempdir),
    list([
      globals__q_kw_properties,
      list([
        list2(q_assign, q_shadow_string_assignment),
        list2(q_lisp_shadow, q_ear_maxima_tempdir),
      ]),
    ]),
  )
  |> ignore
  defmvar(
    q_d_maxima_objdir,
    val=symval(q_d_maxima_objdir),
    list([
      globals__q_kw_properties,
      list([
        list2(q_assign, q_shadow_string_assignment),
        list2(q_lisp_shadow, q_ear_maxima_objdir),
      ]),
    ]),
  )
  |> ignore
  defmvar(
    q_d_default_let_rule_package,
    val=symval(q_d_default_let_rule_package),
    list([globals__q_kw_properties, list([list2(q_assign, q_let_rule_setter)])]),
  )
  |> ignore
  defmvar(
    q_d_current_let_rule_package,
    val=symval(q_d_current_let_rule_package),
    list([globals__q_kw_properties, list([list2(q_assign, q_let_rule_setter)])]),
  )
  |> ignore
  defmvar(q_d_nalgfac, val=symval(q_d_nalgfac), Nil) |> ignore
  defmvar(q_gauss, val=symval(q_gauss), Nil) |> ignore
  defmvar(q_ear_min, val=symval(q_ear_min), Nil) |> ignore
  defmvar(q_ear_mx, val=symval(q_ear_mx), Nil) |> ignore
  defmvar(q_minpoly_star, val=symval(q_minpoly_star), Nil) |> ignore
  defmvar(q_mplc_star, val=symval(q_mplc_star), Nil) |> ignore
  defmvar(q_mm_star, val=symval(q_mm_star), Nil) |> ignore
  defmvar(q_generate_atan2, val=symval(q_generate_atan2), Nil) |> ignore
  defmvar(q_implicit_real, val=symval(q_implicit_real), Nil) |> ignore
  defmvar(q_ear_alpha, val=symval(q_ear_alpha), Nil) |> ignore
  defmvar(
    q_modulus,
    val=symval(q_modulus),
    list([
      globals__q_kw_setting_predicate,
      lfunc("setting-predicate", args => {
        globals__modulus_predicate(arg(args, 0))
      }),
    ]),
  )
  |> ignore
  // $modulus is aliased to modulus and vice-versa.
  putprop_(q_d_modulus, q_modulus, q_alias) |> ignore
  putprop_(q_modulus, q_d_modulus, q_reversealias) |> ignore
  defmvar(q_d_maxpsiposint, val=symval(q_d_maxpsiposint), Nil) |> ignore
  defmvar(q_d_maxpsinegint, val=symval(q_d_maxpsinegint), Nil) |> ignore
  defmvar(q_d_maxpsifracnum, val=symval(q_d_maxpsifracnum), Nil) |> ignore
  defmvar(q_d_maxpsifracdenom, val=symval(q_d_maxpsifracdenom), Nil) |> ignore
  defvar_init(q_ear_preserve_direction, Nil)
  defmvar(q_ear_preserve_direction, val=Nil, Nil) |> ignore
  defmvar(
    q_d_ask_hide_prompt,
    val=symval(q_d_ask_hide_prompt),
    list([q_boolean, globals__q_kw_properties, list([list2(q_evflag, t)])]),
  )
  |> ignore
}

///|
/// DEFMVAR variables defined outside globals.lisp whose initial values the
/// porters of those files did not record in *variable-initial-values*
/// (the variable options were installed by those files' init functions).
/// Variables with NO-RESET are omitted.
let globals__other_defmvars : Array[String] = [
    // algsys
    "$algdelta", "$realonly", "realonlyratnum", "$algexact", "algnotexact",
    // asum
    "$maxtaydiff",
    // bessel
    "$besselexpand", "$bessel_reduce",
    // comm
    "$vect_cross",
    // comm2
    "$logconcoeffp",
    // compar
    "$signbfloat", "$askexp", "$assume_pos", "$assume_pos_pred", "factored",
    "*local-signs*", "sign", "minus", "odds", "evens",
    // csimp2
    "$gammalim", "$beta_args_sum_to_integer",
    // defint
    "$intanalysis",
    // displa
    "$stardisp", "$leftjust", "$noundisp", "displayp", "$boxchar",
    "$absboxchar", "$lmxchar", "$rmxchar", "$display2d_unicode",
    "$display_matrix_brackets", "$display_matrix_padding_vertical",
    "$display_matrix_padding_horizontal", "$display_determinant_bars",
    "$display_box_double_lines",
    // expintegral
    "$expintexpand", "$expintrep",
    // fcall
    "$tr_warn_bad_function_calls",
    // fortra
    "$fortspaces", "$fortindent",
    // hayat
    "tlist", "$psexpand", "$maxtayorder", "$taylor_truncate_polynomials",
    "$taylor_logexpand", "$taylor_simplifier", "$taylor_order_coefficients",
    // hyp
    "$prefer_whittaker", "$prefer_gamma_incomplete", "$expand_polynomials",
    // hypergeometric
    "$max_fpprec", "$expand_hypergeometric", "$multiple_value_return",
    // hypgeo
    "$prefer_d",
    // ifactor
    "$save_primes", "$primep_number_of_tests", "$pollard_rho_limit",
    "$pollard_pm1_limit", "$pollard_rho_tests", "$pollard_pm1_tests",
    "$pollard_rho_limit_step", "$pollard_pm1_limit_step",
    "$ecm_number_of_curves", "$ecm_limit", "$ecm_max_limit", "$ecm_limit_delta",
    "$ifactor_verbose", "$factors_only",
    // init-cl
    "$batch_answers_from_file",
    // inmis
    "$listdummyvars",
    // intpol
    "$find_root_abs", "$find_root_rel", "$find_root_error",
    // invert
    "$invert_method", "$invert_by_adjoint_size_limit",
    // limit
    "simplimplus-problems", "limit-answers", "limit-using-taylor",
    "extended-reals",
    // matcom
    "$announce_rules_firing",
    // matrix
    "top*", "$matrix_element_transpose",
    // matrun
    "$maxapplydepth", "$maxapplyheight", "matchreverse",
    // maxmin
    "$maxmin_effort",
    // mdot
    "$dotconstrules", "$dot0simp", "$dot0nscsimp", "$dot1simp", "$domxnctimes",
    "$dotident",
    // merror
    "$error_size", "$error_syms",
    // mgrind
    "$display_format_internal",
    // mlisp
    "$mapprint", "$refcheck", "$maperror", "$optionset", "$setcheckbreak",
    "$setval",
    // mload
    "$file_type_lisp", "$file_type_maxima", "$file_type_wxmx",
    "$float_approx_equal_tolerance", "$file_search_cache",
    "$file_search_ignore_dirs",
    // mmacro
    "$macroexpansion",
    // mtrace
    "$trace", "$trace_safety", "$trace_break_arg", "$trace_max_indent",
    "$timer", "$timer_devalue",
    // nforma
    "$negsumdispflag",
    // nisimp
    "$letvarsimp", "$letrat",
    // nparse
    "*whitespace-chars*", "$report_synerr_line", "$report_synerr_info",
    "$fast_bfloat_conversion", "$fast_bfloat_threshold",
    // nrat4
    "$radsubstflag",
    // numth
    "$zn_primroot_limit", "$zn_primroot_verbose", "$zn_primroot_pretest",
    "$gf_rat", "$gf_symmetric", "$gf_balanced", "$gf_coeff_limit",
    "$gf_cantor_zassenhaus", "$ef_coeff_mult", "$ef_coeff_add", "$ef_coeff_inv",
    "$ef_coeff_exp", "$gf_powers", "$gf_logs", "$gf_zech_logs",
    // optim
    "$optimprefix", "$optimwarn",
    // outmis
    "$exptisolate", "$isolate_wrt_times", "$combineflag",
    // prompt-util
    "$prompt",
    // psolve
    "flag4",
    // rat3d
    "*irreds", "$berlefact", "$factor_max_degree_print_warning", "$homog_hack",
    // rat3e
    "factorresimp", "inratsimp", "fr-factor", "$ratdenomdivide",
    // risch
    "$erfflag",
    // simp
    "$doscmxplus", "$domxexpt", "$domxplus", "$domxtimes", "$mx0simp",
    "derivsimp", "$grindswitch", "$on", "$off", "$limitdomain", "$lognegint",
    "$distribute_over",
    // sin
    "$integration_constant_counter", "$integration_constant",
    // sinint
    "$integrate_use_rootsof",
    // solve
    "$linsolvewarn", "$solvedecomposes", "$solveexplicit", "$solvenullwarn",
    // spgcd
    "$pointbound",
    // sublis
    "$sublis_apply_lambda",
    // suprv1
    "$strdisp", "$grind", "$backtrace", "$debugmode", "$poislim",
    "$ratvarswitch",
    // tlimit
    "*max-limit-depth*", "*large-positive-number*",
]

///|
/// The MAYBE-RESET part of DEFMVAR for `globals__other_defmvars`: record
/// each variable's value (as set by the initialization) in
/// *variable-initial-values* unless it is already there, so that `reset`
/// restores it. Called once every file's init has run.
fn globals__record_other_defmvars() -> Unit raise {
  let tbl = globals__initial_values_table()
  for name in globals__other_defmvars {
    let s = sym(name)
    if boundp(s) && !gethash2(s, tbl).1 {
      sethash(s, tbl, symval(s)) |> ignore
    }
  }
}
