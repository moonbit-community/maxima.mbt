// Port of src/testsuite.lisp: the lists of test files run by
// run_testsuite(), with the known-failure registry.  Read-time
// conditionals are resolved for the features of the port, which match an
// SBCL build (:sbcl, :lisp-unicode-capable, not a lisp-only build).

///|
fn init_testsuite() -> Unit raise {
  // The Maxima test suite is defined to be the sum of all the tests in the
  // files listed in the Maxima option variable $testsuite_files.  Each
  // entry can either be a plain file name (minus extension) or a Maxima list
  // containing a file name followed by another Maxima list of the numbers of
  // the test problems that are expected to fail.
  set(
    q_d_testsuite_files,
    lread(
    #|((mlist simp) "rtest_ask1" "rtest_sqdnst" "rtest_extensions" ((mlist
    #|simp) "rtest_rules" ) "rtestnset" ((mlist simp) "rtest1" ((mlist
    #|simp))) ((mlist simp) "rtest1a" ((mlist simp) 33)) ((mlist simp)
    #|"rtest2" ((mlist simp) 86 95)) "rtest4" ((mlist simp) "rtest5" )
    #|"rtest6" "rtest6a" "rtest6b" "rtest7" "rtest9" ((mlist simp) "rtest9a"
    #|) ((mlist simp) "rtest10" ((mlist simp) 24 25)) ((mlist simp)
    #|"rtest11" ) "rtest13" "rtest13s" ((mlist simp) "rtest14") "rtest15"
    #|((mlist simp) "rtest16" ((mlist simp)) ) "rtestode" "rtestode_zp"
    #|((mlist simp) "rtest3" ((mlist simp) 146)) ((mlist simp) "rtest8")
    #|((mlist) "rtest12" 68 69 70) "rexamples" ((mlist simp) "rtesthyp"
    #|((mlist simp) 105 112 113 123 124 128)) ((mlist simp) "rtest_hypgeo"
    #|((mlist simp) 143)) "rtestmt19937" "rtest_allnummod" ((mlist simp)
    #|"rtest_maxmin" ((mlist simp) 40 52 53 57 97 109)) "rtestconjugate"
    #|((mlist simp) "rtestsum" ((mlist simp) 23 24 38)) ((mlist simp)
    #|"rtest_trig" ) "rtest_zeta" "rtest_diff_invtrig" "rtest_scalarp"
    #|"rtest_everysome" ((mlist simp) "rtestint" ((mlist simp)))
    #|"rtest_mactex" "rtest_numth" "rtestifactor" ((mlist simp)
    #|"rtest_equal" ((mlist simp) 157 160)) "rtest_abs" ((mlist simp)
    #|"rtest_taylor" ((mlist simp) 88 91 97 104 129)) ((mlist simp)
    #|"rtest_dot") "rtest_mset" "rtest_boolean" "rtest_round" ((mlist simp)
    #|"rtest_map" ((mlist simp) 2 3 4)) ((mlist simp) "rtest_sign" ((mlist
    #|simp) 21 25 30 40 145)) "rtest_algebraic" ((mlist simp) "rtest_gamma"
    #|) "rtest_expintegral" ((mlist simp) "rtest_signum") "rtest_lambert_w"
    #|((mlist simp) "rtest_elliptic" ((mlist simp) 135) ) ((mlist simp)
    #|"rtest_integrate" ((mlist simp) 826 827)) "rtest_integrate_special"
    #|((mlist simp) "rtest_sqrt" ((mlist simp) 89)) ((mlist simp)
    #|"rtest_carg" ((mlist simp) 40 41)) ((mlist simp) "rtest_log") ((mlist
    #|simp) "rtest_power" ((mlist simp) 19 20 26)) "rtestdefstruct" ((mlist
    #|simp) "rtest_limit" ((mlist simp) 160 161)) "rtest_powerseries"
    #|((mlist simp) "rtest_laplace" ((mlist simp) 29 49 50 51 59 60 61 62 78
    #|80)) "rtest_plotoptions" "rtest_algsys" "rtest_trace"
    #|"rtest_polynomialp" ((mlist simp) "rtest_limit_extra" ((mlist simp) 42
    #|59 61 82 83 84 89 96 104 124 125 126 127 132 133 135 136 137 240 243
    #|244 245 246 249 267 272 357 358)) ((mlist simp) "rtest_limit_gruntz"
    #|((mlist simp) 20 25 28 29 30 37 39 86)) ((mlist simp)
    #|"rtest_limit_wester" ((mlist simp) 12 13)) ((mlist simp) "rtest_great"
    #|((mlist simp))) ((mlist simp) "rtest_atan2" ((mlist simp) 65))
    #|"rtest_gcd" ((mlist simp) "rtest_hstep") ((mlist simp) "rtest_sinc"
    #|((mlist simp))) ((mlist simp) "rtest_hg" ) ((mlist simp)
    #|"rtest_nfloat") ((mlist simp) "rtest_ilt") ((mlist simp) "ulp_tests" )
    #|"rtest_unicode_display" ((mlist simp) "rtest_setvar" )
    #|"rtest_operators" "rtest_wxmx" "rtest_load_relative"),
    ),
  )
  |> ignore
}
