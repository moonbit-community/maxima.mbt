// Port of src/trdata.lisp: the MODE data for the "built-in" functions.

///|
fn init_trdata() -> Unit raise {
  // MODEDECLARE(FUNCTION(LENGTH),FIXNUM)
  for x in [
    "$length", "$nterms", "$nroots", "$rank", "$polysign", "$time", "$array_dimension_n",
  ] {
    putprop(sym(x), q_d_fixnum, q_function_mode) |> ignore
  }
  // Functions of BOOLEAN return VALUE. i.e. PREDICATES
  for x in [
    "$array", "$bfloatp", "$listp", "$matrixp", "$ratnump", "$constantp", "$atom",
    "$freeof", "$subvarp", "$symbolp", "$evenp", "$oddp", "$orderlessp", "$ordergreatp",
    "$mapatom", "$integerp", "$floatnump", "$nonscalarp", "$numberp", "$ratp", "$member",
    "$emptyp",
  ] {
    putprop(sym(x), q_d_boolean, q_function_mode) |> ignore
  }
  // MODEDECLARE(TRUE,BOOLEAN)
  for x in [
    "$true", "$false", "$doallmxops", "$domxmxops", "$doscmxops", "$detout", "$dotassoc",
    "$dotdistrib", "$dotscrules", "$exponentialize", "$keepfloat", "$listarith", "$logsimp",
    "$maxapplyheight", "$maxapplydepth", "$maperror", "$powerdisp", "$scalarmatrix", "$simp",
    "$ttyoff", "$underflow", "$infeval", "$xaxis", "$yaxis", "$ratfac",
  ] {
    putprop(sym(x), q_d_boolean, q_mode) |> ignore
  }
  for x in [
    "$eval", "$done", "$%i", "$%pi", "$%e", "$%phi", "$%gamma",
    // important for array referencing conventions.
     "mqapply",
  ] {
    putprop(sym(x), t, q_implied_quotep) |> ignore
  }
  // The result of a part function never needs simplification.
  // $CONS for example has the same property, although it is not a "PART"
  // function.
  for x in [
    "$print", "$num", "$denom", "$lhs", "$rhs", "$part", "$cons", "$reverse", "$endcons",
    "$append", "$union", "$intersection", "$setdiff", "$symdiff", "$mapset", "$predset",
    "${", "$elementof",
  ] {
    putprop(sym(x), t, q_tr_nosimp) |> ignore
  }
}
