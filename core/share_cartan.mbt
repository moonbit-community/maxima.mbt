// Port of share/calculus/cartan.lisp: exterior calculus of differential
// forms -- the operators | (contraction) and ~ (exterior product),
// ext_diff, lie_diff, edit and basub, defined as MEXPR properties
// (translated from Maxima code), and init_cartan.

///|
/// The property and Maxima function definitions of the file, in their Lisp
/// source form (read with the port's reader, which follows CL's case
/// conventions).
let share_cartan__forms : String =
  #|(DEFPROP $\| %\| VERB) 
  #|(DEFPROP $\| "|" OP) 
  #|(putopr "|" '$\|)
  #|(ADD2LNC (QUOTE "|") $PROPS) 
  #|(DEFPROP $\| DIMENSION-infix DIMENSION) 
  #|(DEFPROP $\| (#\Space #\| #\Space) DISSYM) 
  #|(DEFPROP $\| 120 LBP) 
  #|(DEFPROP $\| 180 RBP) 
  #|(DEFPROP $\| PARSE-INFIX LED) 
  #|(DEFPROP $\| MSIZE-INFIX GRIND) 
  #|(DEFPROP %\| DIMENSION-infix DIMENSION) 
  #|(DEFPROP %\| (#\Space #\| #\Space) DISSYM) 
  #|(MDEFPROP $\| ((LAMBDA) ((MLIST) $V $F) ((MPROG SIMP) ((MLIST SIMP)
  #| $I $J $EXT101 $EXT102 $EXT103 $EXT104) ((MSETQ SIMP) $EXT103 
  #|(($EXPAND SIMP) $F)) ((MSETQ SIMP) $EXT102 ((MTIMES SIMP) 
  #|(($V SIMP ARRAY) 1) (($COEFF SIMP) $EXT103 (($CARTAN_BASIS SIMP ARRAY) 1)))) 
  #|((MDO SIMP) $I 2 NIL NIL $CARTAN_DIM NIL ((MPROGN SIMP) ((MSETQ SIMP) 
  #|$EXT101 (($COEFF SIMP) $EXT103 (($CARTAN_BASIS SIMP ARRAY) $I))) 
  #|((MCOND SIMP) ((MNOTEQUAL SIMP) $EXT101 0) ((MSETQ SIMP) $EXT101
  #| (($SUBSTITUTE SIMP) (($EXTSUB SIMP ARRAY) $I) $EXT101)) T $FALSE)
  #| ((MSETQ SIMP) $EXT102 ((MPLUS SIMP) $EXT102 ((MTIMES SIMP) $EXT101
  #| (($V SIMP ARRAY) $I)))))) ((MRETURN SIMP) (($EXPAND SIMP) $EXT102))))
  #| MEXPR) 
  #|(ADD2LNC (QUOTE (($\|) $V $F)) $FUNCTIONS) 
  #|(DEFPROP %\| $\| NOUN) 
  #|(DEFPROP $~ %~ VERB) 
  #|(DEFPROP $~ "~" OP) 
  #|(putopr "~" '$~)
  #|(ADD2LNC (QUOTE "~") $PROPS) 
  #|(DEFPROP $~ DIMENSION-infix DIMENSION) 
  #|(DEFPROP $~ (#\Space #\~ #\Space) DISSYM) 
  #|(DEFPROP $~ 140 LBP) 
  #|(DEFPROP $~ 180 RBP) 
  #|(DEFPROP $~ PARSE-INFIX LED) 
  #|(DEFPROP $~ MSIZE-INFIX GRIND) 
  #|(DEFPROP %~ DIMENSION-infix DIMENSION) 
  #|(DEFPROP %~ (#\Space #\~ #\Space) DISSYM) 
  #|(MDEFPROP $~ ((LAMBDA) ((MLIST) $F $G) ((MPROG SIMP) ((MLIST SIMP) $I $J $EXT101 $EXT102 $EXT103 $EXT104 $EXT105) ((MSETQ SIMP) $EXT101 0) ((MSETQ SIMP) $EXT102 $TRUE) ((MSETQ SIMP) $EXT103 (($EXPAND SIMP) $F)) ((MDO SIMP) $I $CARTAN_DIM -1 NIL 1 NIL ((MPROGN SIMP) ((MSETQ SIMP) $EXT104 (($EXPAND SIMP) (($BOTHCOEF SIMP) $EXT103 (($CARTAN_BASIS SIMP ARRAY) $I)))) ((MSETQ SIMP) $EXT105 (($FIRST SIMP) $EXT104)) ((MCOND SIMP) ((MNOTEQUAL SIMP) $EXT105 0) ((MPROGN SIMP) ((MSETQ SIMP) $EXT103 (($LAST SIMP) $EXT104)) ((MSETQ SIMP) $CARTAN_DIM ((MPLUS SIMP) -1 $I)) ((MSETQ SIMP) $EXT101 ((MPLUS SIMP) $EXT101 (($~ SIMP) $EXT105 ((MTIMES SIMP) (($CARTAN_BASIS SIMP ARRAY) $I) (($SUBSTITUTE SIMP) (($EXTSUBB SIMP ARRAY) $I) $G))))) ((MSETQ SIMP) $CARTAN_DIM $EXTDIM) ((MSETQ SIMP) $EXT102 $FALSE)) T $FALSE))) ((MCOND SIMP) $EXT102 ((MRETURN SIMP) (($EXPAND SIMP) ((MTIMES SIMP) $F $G))) T ((MRETURN SIMP) (($EXPAND SIMP) $EXT101))))) MEXPR) 
  #|(ADD2LNC (QUOTE (($~) $F $G)) $FUNCTIONS) 
  #|(DEFPROP %~ $~ NOUN) 
  #|(MDEFPROP $EXT_DIFF ((LAMBDA) ((MLIST) $F) (($SUM SIMP) (($~ SIMP) 
  #|(($CARTAN_BASIS SIMP ARRAY) $I) (($DIFF SIMP) $F (($CARTAN_COORDS SIMP ARRAY) $I)))
  #| $I 1 $CARTAN_DIM)) MEXPR) 
  #|(ADD2LNC (QUOTE (($EXT_DIFF) $F)) $FUNCTIONS) 
  #|(MDEFPROP $LIE_DIFF_F ((LAMBDA) ((MLIST) $V $F) ((MPLUS SIMP) (($\| SIMP) $V 
  #|(($EXT_DIFF SIMP) $F)) (($EXT_DIFF SIMP) (($\| SIMP) $V $F)))) MEXPR) 
  #|(ADD2LNC (QUOTE (($LIE_DIFF_F) $V $F)) $FUNCTIONS) 
  #|(MDEFPROP $LIE_DIFF_V ((LAMBDA) ((MLIST) $V $W) ((MPROG SIMP) ((MLIST SIMP) 
  #|$I $J $EXT101) ((MSETQ SIMP) $EXT101 ((MLIST SIMP))) ((MDO SIMP) 
  #|$I 1 NIL NIL $CARTAN_DIM NIL ((MSETQ SIMP) $EXT101 (($ENDCONS SIMP) 
  #|(($SUM SIMP) ((MPLUS SIMP) ((MTIMES SIMP) (($DIFF SIMP)
  #| (($W SIMP ARRAY) $I) (($CARTAN_COORDS SIMP ARRAY) $J)) (($V SIMP ARRAY) $J))
  #| ((MTIMES SIMP) -1 (($DIFF SIMP) (($V SIMP ARRAY) $I) 
  #|(($CARTAN_COORDS SIMP ARRAY) $J)) (($W SIMP ARRAY) $J))) $J 1 $CARTAN_DIM) $EXT101)))
  #| ((MRETURN SIMP) (($EXPAND SIMP) $EXT101)))) MEXPR) 
  #|(ADD2LNC (QUOTE (($LIE_DIFF_V) $V $W)) $FUNCTIONS) 
  #|(MDEFPROP $EDIT ((LAMBDA) ((MLIST) $F) ((MPROG SIMP) ((MLIST SIMP) $I
  #| $EXT101 $EXT102 $EXT103 $EXT104 $EXT105) ((MSETQ SIMP) $EXT101 0)
  #| ((MSETQ SIMP) $EXT102 (($EXPAND SIMP) $F)) ((MDO SIMP) $I $CARTAN_DIM -1 
  #|NIL 1 NIL ((MPROGN SIMP) ((MSETQ SIMP) $EXT103 (($EXPAND SIMP) 
  #|(($BOTHCOEF SIMP) $EXT102 (($CARTAN_BASIS SIMP ARRAY) $I)))) ((MSETQ SIMP)
  #| $EXT104 (($FIRST SIMP) $EXT103)) ((MCOND SIMP) ((MNOTEQUAL SIMP)
  #| $EXT104 0) ((MPROGN SIMP) ((MSETQ SIMP) $EXT102 (($LAST SIMP) $EXT103))
  #| ((MSETQ SIMP) $CARTAN_DIM ((MPLUS SIMP) -1 $I)) ((MSETQ SIMP) $EXT105
  #| (($EDIT SIMP) $EXT104)) ((MSETQ SIMP) $CARTAN_DIM $EXTDIM) ((MCOND SIMP) 
  #|((MEQUAL SIMP) $EXT105 0) ((MSETQ SIMP) $EXT101 ((MPLUS SIMP) $EXT101
  #| ((MTIMES SIMP) $EXT104 (($CARTAN_BASIS SIMP ARRAY) $I)))) T ((MCOND SIMP)
  #| ((MEQUAL SIMP) (($INPART SIMP) $EXT105 0) "+") ((MSETQ SIMP) $EXT101
  #| ((MPLUS SIMP) $EXT101 (($MULTTHRU SIMP) ((MTIMES SIMP) $EXT105
  #| (($CARTAN_BASIS SIMP ARRAY) $I))))) T ((MSETQ SIMP) $EXT101 ((MPLUS SIMP)
  #| $EXT101 ((MTIMES SIMP) $EXT105 (($CARTAN_BASIS SIMP ARRAY) $I))))))) 
  #|T $FALSE))) ((MRETURN SIMP) $EXT101))) MEXPR) 
  #|(ADD2LNC (QUOTE (($EDIT) $F)) $FUNCTIONS) 
  #|(MDEFPROP $BASUB ((LAMBDA) ((MLIST) $F $G $H) ((MPROG SIMP) 
  #|((MLIST SIMP) $I $EXT101 $EXT102 $EXT103 $EXT104) ((MSETQ SIMP)
  #| $EXT101 (($EXPAND SIMP) $H)) ((MSETQ SIMP) $EXT102 (($EXPAND SIMP)
  #| (($BOTHCOEF SIMP) $EXT101 $G))) ((MSETQ SIMP) $EXT103 (($FIRST SIMP)
  #| $EXT102)) ((MCOND SIMP) ((MEQUAL SIMP) $EXT103 0) ((MRETURN SIMP) $H)
  #| T $FALSE) ((MCOND SIMP) ((MEQUAL SIMP) $G (($CARTAN_BASIS SIMP ARRAY) 1))
  #| ((MRETURN SIMP) ((MPLUS SIMP) (($LAST SIMP) $EXT102) (($~ SIMP) $F
  #| $EXT103))) T $FALSE) ((MDO SIMP) $I 2 NIL NIL $CARTAN_DIM NIL ((MCOND SIMP)
  #| ((MEQUAL SIMP) $G (($CARTAN_BASIS SIMP ARRAY) $I)) ((MRETURN SIMP) 
  #|((MSETQ SIMP) $EXT104 ((MPLUS SIMP) (($LAST SIMP) $EXT102) (($~ SIMP)
  #| $F (($SUBSTITUTE SIMP) (($EXTSUB SIMP ARRAY) $I) $EXT103))))) 
  #|T $FALSE)) ((MRETURN SIMP) $EXT104))) MEXPR) 
  #|(ADD2LNC (QUOTE (($BASUB) $F $G $H)) $FUNCTIONS) 
  #|
  #|
  #|(meval '((MDEFINE) (($LIE_DIFF) $V $X)
  #|         ((MCOND) (($LISTP) $X) (($LIE_DIFF_V) $V $X) T
  #|          (($LIE_DIFF_F) $V $X))))

///|
/// (QUOTE x) => x
fn share_cartan__unquote(x : Value) -> Value raise {
  if consp(x) && eq(car(x), q_quote) {
    cadr(x)
  } else {
    x
  }
}

///|
/// Evaluate one of the top-level forms of SHARE_CARTAN__FORMS.
fn share_cartan__eval_form(form : Value) -> Unit raise {
  let args = cdr(form)
  match symbol_name(car(form)) {
    "defprop" => putprop(car(args), cadr(args), caddr(args)) |> ignore
    "mdefprop" => mputprop(car(args), cadr(args), caddr(args)) |> ignore
    "putopr" => putopr(car(args), share_cartan__unquote(cadr(args))) |> ignore
    "add2lnc" =>
      add2lnc(share_cartan__unquote(car(args)), symval(cadr(args))) |> ignore
    "meval" => meval(share_cartan__unquote(car(args))) |> ignore
    _ =>
      raise LispError::SimpleError(
        "cartan: unexpected form " + prin1_to_string(form),
      )
  }
}

///|
fn init_share_cartan() -> Unit raise {
  if d_get(q_d_cartan, q_d_version).truthy() {
    merr("CARTAN already loaded", []) |> ignore
  } else {
    d_put(q_d_cartan, q_d_v20041209, q_d_version) |> ignore
  }
  for form in lread_all(share_cartan__forms) {
    share_cartan__eval_form(form)
  }
}

///|
/// The following is a hand translation (more or less) of this MAXIMA code:
///
/// init_cartan(coords):=block
/// (
///   [ci],
///   cartan_coords:coords,
///   cartan_dim:extdim:length(cartan_coords),
///   cartan_basis:extsubb[1]:[],
///   for i thru cartan_dim do
///   (
///     ci:concat(zzz,i),
///     cartan_basis:endcons(ci,cartan_basis),
///     extsub[i+1]:cons(ci=-ci,extsub[i]),
///     extsubb[i]:cons(ci=0,extsub[i]),
///     apply('alias,[concat(d,cartan_coords[i]),ci])
///   )
/// );
fn d_init_cartan(c : Value) -> Value raise {
  set(q_d_cartan_coords, c) |> ignore
  set(q_d_cartan_dim, d_length(symval(q_d_cartan_coords))) |> ignore
  set(q_d_extdim, symval(q_d_cartan_dim)) |> ignore
  set(q_d_cartan_basis, Nil) |> ignore
  let extsub = sym("$extsub")
  let extsubb = sym("$extsubb")
  let simp_list = list1(list2(q_mlist, q_simp))
  meval(list([list1(q_msetq), list2(list2(extsub, q_array), int(1)), simp_list]))
  |> ignore
  meval(
    list([list1(q_msetq), list2(list2(extsubb, q_array), int(1)), simp_list]),
  )
  |> ignore
  let mut c = cdr(symval(q_d_cartan_coords))
  let mut i = 1
  while c.truthy() {
    let ci = d_concat(list2(sym("zzz"), int(i)))
    set(q_d_cartan_basis, cons(ci, symval(q_d_cartan_basis))) |> ignore
    meval(
      list([
        list1(q_msetq),
        list2(list2(extsub, q_array), int(i + 1)),
        d_cons(
          list([
            list2(q_mequal, q_simp),
            ci,
            list([list2(q_mtimes, q_simp), int(-1), ci]),
          ]),
          meval(list2(list2(extsub, q_array), int(i))),
        ),
      ]),
    )
    |> ignore
    meval(
      list([
        list1(q_msetq),
        list2(list2(extsubb, q_array), int(i)),
        d_cons(
          list([list2(q_mequal, q_simp), ci, int(0)]),
          meval(list2(list2(extsub, q_array), int(i))),
        ),
      ]),
    )
    |> ignore
    meval(list([list1(q_alias), d_concat(list2(sym("d"), car(c))), ci]))
    |> ignore
    c = cdr(c)
    i = i + 1
  }
  set(
    q_d_cartan_basis,
    cons(list2(q_mlist, q_simp), reverse(symval(q_d_cartan_basis))),
  )
}
