// Port of src/max_ext.lisp: autoload data for Maxima share packages.
// (The helper functions are in autol.mbt.)

///|
fn init_max_ext() -> Unit raise {
  d_auto_mexpr(sym("$ordering"), Str("list_operations.mac")) |> ignore
  d_auto_mexpr(sym("$ranks"), Str("list_operations.mac")) |> ignore
  d_auto_mexpr(sym("$find_runs"), Str("list_operations.mac")) |> ignore
  d_auto_mexpr(sym("$accumulate"), Str("accumulate.mac")) |> ignore
  d_auto_mexpr(sym("$guess_exact_value"), Str("pslq")) |> ignore
  setf_get(sym("$pslq_integer_relation"), q_autoload, Str("pslq")) |> ignore
  d_auto_mexpr(sym("$lratsubst"), Str("lrats")) |> ignore
  d_auto_mexpr(sym("$fullratsubst"), Str("lrats")) |> ignore
  d_auto_mexpr(sym("$nusum"), Str("nusum")) |> ignore
  d_auto_mexpr(sym("$unsum"), Str("nusum")) |> ignore
  d_auto_mexpr(sym("$funcsolve"), Str("nusum")) |> ignore
  d_auto_mexpr(sym("$bffac"), Str("bffac")) |> ignore
  d_auto_mexpr(sym("$cbffac"), Str("bffac")) |> ignore
  d_auto_mexpr(sym("$bfzeta"), Str("bffac")) |> ignore
  d_auto_mexpr(sym("$bfpsi"), Str("bffac")) |> ignore
  d_auto_mexpr(sym("$bfpsi0"), Str("bffac")) |> ignore
  // CL passes the symbol |trigrat|, which FILE_SEARCH turns into "trigrat".
  auto_mexpr(sym("$trigrat"), Str("trigrat")) |> ignore
  // CL passes the symbol |gcdex|, which FILE_SEARCH turns into "gcdex".
  d_auto_mexpr(sym("$gcdex"), Str("gcdex")) |> ignore
  d_auto_mexpr(sym("$expandwrt"), Str("simplification/stopex")) |> ignore
  d_auto_mexpr(sym("$expandwrt_factored"), Str("simplification/stopex")) |> ignore
  d_auto_mexpr(sym("$facsum"), Str("simplification/facexp")) |> ignore
  d_auto_mexpr(sym("$factorfacsum"), Str("simplification/facexp")) |> ignore
  d_auto_mexpr(sym("$collectterms"), Str("simplification/facexp")) |> ignore
  d_auto_mexpr(sym("$disolate"), Str("simplification/disol")) |> ignore
  d_auto_mexpr(sym("$linsimp"), Str("misc/declin")) |> ignore
  d_auto_mexpr(sym("$declare_linear_operator"), Str("misc/declin")) |> ignore
  d_auto_mexpr(sym("$nonumfactor"), Str("simplification/genut")) |> ignore
  // (meval '((%setup_autoload simp) "bffac" $bfzeta))
  meval(list3(list2(q_p_setup_autoload, q_simp), Str("bffac"), sym("$bfzeta")))
  |> ignore
  d_auto_mexpr(sym("$eigenvectors"), Str("eigen.mac")) |> ignore
  d_auto_mexpr(sym("$eivects"), Str("eigen.mac")) |> ignore
  d_auto_mexpr(sym("$eigenvalues"), Str("eigen.mac")) |> ignore
  d_auto_mexpr(sym("$eivals"), Str("eigen.mac")) |> ignore
  d_auto_mexpr(sym("$trigsimp"), Str("trgsmp.mac")) |> ignore
  d_auto_mexpr(sym("$ode2"), Str("ode2.mac")) |> ignore
  d_auto_mexpr(sym("$ic1"), Str("ode2.mac")) |> ignore
  d_auto_mexpr(sym("$ic2"), Str("ode2.mac")) |> ignore
  d_auto_mexpr(sym("$bc2"), Str("ode2.mac")) |> ignore
  d_auto_mexpr(sym("$desimp"), Str("ode2.mac")) |> ignore
  d_auto_mexpr(sym("$linear2"), Str("ode2")) |> ignore
  d_auto_mexpr(sym("$similaritytransform"), Str("eigen.mac")) |> ignore
  d_auto_mexpr(sym("$simtran"), Str("eigen.mac")) |> ignore
  for f in [
    "$cyclep", "$permp", "$permult", "$perm_inverse", "$permute",
    "$apply_cycles", "$perm_undecomp", "$perm_cycles", "$perm_lex_rank",
    "$perm_lex_unrank", "$perm_length", "$perm_decomp", "$perm_parity",
    "$perms_lex", "$perm_lex_next", "$perm_rank", "$perm_unrank", "$perms",
    "$perm_next", "$random_perm",
  ] {
    setf_get(sym(f), q_autoload, Str("combinatorics")) |> ignore
  }
  for f in [
    "$arite", "$card_orbit", "$card_stab", "$comp2ele", "$comp2pui",
    "$cont2part", "$contract", "$direct", "$ele2comp", "$ele2polynome",
    "$ele2pui", "$elem", "$explose", "$kostka", "$lgtreillis", "$ltreillis",
    "$mon2schur", "$multi_elem", "$multi_orbit", "$multi_pui",
    "$multinomial", "$multsym", "$orbit", "$part2cont", "$partpol",
    "$permut", "$polynome2ele", "$prodrac", "$pui", "$pui2comp", "$pui2ele",
    "$pui2polynome", "$pui_direct", "$puireduc", "$resolvante",
    "$resolvante_alternee1", "$resolvante_bipartite", "$resolvante_diedrale",
    "$resolvante_klein", "$resolvante_klein3", "$resolvante_produit_sym",
    "$resolvante_unitaire", "$resolvante_vierer", "$schur2comp", "$somrac",
    "$tcontract", "$tpartpol", "$treillis", "$treinat",
  ] {
    setf_get(sym(f), q_autoload, Str("sym.mac")) |> ignore
  }
  for f in [
    "$adjust_external_format", "$close", "$flush_output", "$flength",
    "$fposition", "$freshline", "$newline", "$opena", "$openr", "$openw",
    "$make_string_input_stream", "$make_string_output_stream",
    "$get_output_stream_string", "$stderr", "$stdin", "$stdout", "$printf",
    "$sprint", "$writebyte", "$readbyte", "$readchar", "$readline",
    "$alphacharp", "$alphanumericp", "$ascii", "$cequal", "$cequalignore",
    "$cgreaterp", "$cgreaterpignore", "$charp", "$cint", "$clessp",
    "$clesspignore", "$constituent", "$cunlisp", "$digitcharp", "$lcharp",
    "$lowercasep", "$uppercasep", "$stringp", "$charat", "$charlist",
    "$eval_string", "$parse_string", "$scopy", "$sdowncase", "$sequal",
    "$sequalignore", "$sexplode", "$sgreaterp", "$sgreaterpignore",
    "$simplode", "$sinsert", "$sinvertcase", "$slength", "$slessp",
    "$slesspignore", "$smake", "$smismatch", "$split", "$sposition",
    "$sremove", "$sremovefirst", "$sreverse", "$ssearch", "$ssort",
    "$ssubst", "$ssubstfirst", "$strim", "$striml", "$strimr", "$substring",
    "$supcase", "$tab", "$tokens", "$unicode", "$unicode_to_utf8",
    "$utf8_to_unicode", "$base64", "$base64_decode", "$crc24sum", "$md5sum",
    "$mgf1_sha1", "$number_to_octets", "$octets_to_number", "$octets_to_oid",
    "$oid_to_octets", "$octets_to_string", "$string_to_octets", "$sha1sum",
    "$sha256sum", "$inferred_encoding", "$recognized_encoding_p",
  ] {
    setf_get(sym(f), q_autoload, Str("stringproc")) |> ignore
  }
  for f in [
    "$regex_compile", "$regex_match_pos", "$regex_match", "$regex_split",
    "$regex_subst_first", "$regex_subst", "$string_to_regex",
  ] {
    setf_get(sym(f), q_autoload, Str("sregex")) |> ignore
  }
  setf_get(sym("$romberg"), q_autoload, Str("romberg")) |> ignore
  for f in [
    "$assume_external_byte_order", "$opena_binary", "$openr_binary",
    "$openw_binary", "$read_array", "$read_binary_array",
    "$read_binary_list", "$read_binary_matrix", "$read_hashed_array",
    "$read_lisp_array", "$read_list", "$read_matrix", "$read_maxima_array",
    "$read_nested_list", "$write_binary_data", "$write_data",
  ] {
    setf_get(sym(f), q_autoload, Str("numericalio")) |> ignore
  }
  for f in [
    "$bit_and", "$bit_length", "$bit_lsh", "$bit_not", "$bit_onep",
    "$bit_or", "$bit_rsh", "$bit_xor",
  ] {
    setf_get(sym(f), q_autoload, Str("bitwise")) |> ignore
  }
  for f in [
    "$eigens_by_jacobi", "$cholesky", "$circulant", "$cauchy_matrix",
    "$hessian", "$jacobian", "$krylov_matrix", "$matrix_sign",
    "$sylvester_matrix", "$vandermonde_matrix", "$blockmatrixp",
    "$ctranspose", "$identfor", "$matrix_size", "$require_list",
    "$require_matrix", "$require_nonempty_matrix", "$require_posinteger",
    "$require_real_symmetric_matrix", "$require_selfadjoint_matrix",
    "$require_square_matrix", "$require_symmetric_matrix",
    "$require_unblockedmatrix", "$zerofor", "$zeromatrixp",
    "$determinant_by_lu", "$get_lu_factors", "$invert_by_lu",
    "$linsolve_by_lu", "$lu_backsub", "$lu_factor", "$mat_cond",
    "$matrixexp", "$matrixfun", "$spectral_rep", "$addmatrices",
    "$require_ring",
  ] {
    setf_get(sym(f), q_autoload, Str("linearalgebra")) |> ignore
  }
  for f in [
    "$column_reduce", "$columnop", "$columnspace", "$columnswap",
    "$diag_matrix", "$dotproduct", "$good_pivot", "$hankel",
    "$hilbert_matrix", "$hipow_gzero", "$kronecker_product", "$linalg_rank",
    "$locate_matrix_entry", "$mat_fullunblocker", "$mat_norm", "$mat_trace",
    "$mat_unblocker", "$moore_penrose_pseudoinverse", "$nullity",
    "$nullspace", "$orthogonal_complement", "$polytocompanion",
    "$ptriangularize", "$ptriangularize_with_proviso",
    "$request_rational_matrix", "$require_integer", "$require_symbol",
    "$rowop", "$rowswap", "$toeplitz",
  ] {
    d_auto_mexpr(sym(f), Str("linearalgebra")) |> ignore
  }
  for f in [
    "$assoc_legendre_p", "$assoc_legendre_q", "$chebyshev_t", "$chebyshev_u",
    "$gen_laguerre", "$hermite", "$intervalp", "$jacobi_p", "$laguerre",
    "$legendre_p", "$legendre_q", "$orthopoly_recur", "$orthopoly_weight",
    "$pochhammer", "$spherical_bessel_j", "$spherical_bessel_y",
    "$spherical_hankel1", "$spherical_hankel2", "$spherical_harmonic",
    "$ultraspherical",
  ] {
    setf_get(sym(f), q_autoload, Str("orthopoly")) |> ignore
  }
  putprop(sym("$unit_step"), sym("simp-unit-step"), sym("operators")) |> ignore
  autof(sym("simp-unit-step"), Str("orthopoly")) |> ignore
  putprop(sym("$pochhammer"), sym("simp-pochhammer"), sym("operators")) |> ignore
  autof(sym("simp-pochhammer"), Str("orthopoly")) |> ignore
  for f in [
    "$activate_window", "$add_zeroes", "$draw", "$draw2d", "$draw3d",
    "$draw_file", "$get_pixel", "$make_level_picture", "$make_rgb_picture",
    "$multiplot_mode", "$negative_picture", "$picture_equalp", "$picturep",
    "$read_xpm", "$rgb2level", "$set_draw_defaults", "$take_channel",
  ] {
    setf_get(sym(f), q_autoload, Str("draw")) |> ignore
  }
  for f in [
    "$julia", "$mandelbrot", "$plotdf", "$ploteq", "$rk",
  ] {
    setf_get(sym(f), q_autoload, Str("dynamics")) |> ignore
  }
  for f in [
    "$evolution", "$staircase", "$evolution2d", "$chaosgame", "$ifs",
    "$orbits",
  ] {
    d_auto_mexpr(sym(f), Str("dynamics")) |> ignore
  }
  setf_get(sym("$scene"), q_autoload, Str("visualization")) |> ignore
  d_auto_mexpr(sym("$abramowitz_id"), Str("abramowitz_id")) |> ignore
  d_auto_mexpr(sym("$hypergeometric_simp"), Str("hypergeometric_mac")) |> ignore
  for f in [
    "$cl_eval", "$common_lisp", "$to_cl",
  ] {
    setf_get(sym(f), q_autoload, Str("tocl")) |> ignore
  }
  for f in [
    "$pwilt",
  ] {
    setf_get(sym(f), q_autoload, Str("pwilt")) |> ignore
  }
}
