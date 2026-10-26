// Port of share/contrib/diffequations/gauss.lisp (Barton Willis, 2004):
// derivatives (grad properties) of the hypergeometric functions gauss_a, gauss_b,
// for odelin. The file consists of top-level
// $put and putprop forms only; they are kept in their Lisp source form
// and evaluated by `share_odeutils__eval_put_forms` at load time.

///|
let share_gauss__forms : String =
  #|($put '$gauss 1 '$version)
  #|
  #|(putprop '$gauss_a
  #|	 '((a b c x)
  #|	   ((unk) "$first" "$gauss_a")
  #|	   ((unk) "$second" "$gauss_a")
  #|	   ((unk) "$third" "$gauss_a")
  #|	   (($dgauss_a) a b c x))
  #|	 'grad)
  #|
  #|(putprop '$dgauss_a
  #|	 '((a b c x)
  #|	   ((unk) "$first" "$dgauss_a")
  #|	   ((unk) "$second" "$dgauss_a")
  #|	   ((unk) "$third" "$dgauss_a")
  #|	   ((mtimes) ((mexpt) ((mplus) 1 ((mtimes) -1 x)) -1)
  #|	    ((mexpt) x -1)
  #|	    ((mplus) ((mtimes) a (($gauss_a) a b c x) b)
  #|	     ((mtimes) (($dgauss_a) a b c x)
  #|	      ((mplus) ((mtimes) -1 c)
  #|	       ((mtimes) ((mplus) 1 a b) x))))))
  #|	 'grad)
  #|
  #|(putprop '$gauss_b
  #|	 '((a b c x)
  #|	   ((unk) "$first" "$gauss_b")
  #|	   ((unk) "$second" "$gauss_b")
  #|	   ((unk) "$third" "$gauss_b")
  #|	   (($dgauss_b) a b c x))
  #|	 'grad)
  #|
  #|(putprop '$dgauss_b
  #|	 '((a b c x)
  #|	   ((unk) "$first" "$dgauss_b")
  #|	   ((unk) "$second" "$dgauss_b")
  #|	   ((unk) "$third" "$dgauss_b")
  #|	   ((mtimes) ((mexpt) ((mplus) 1 ((mtimes) -1 x)) -1)
  #|	    ((mexpt) x -1)
  #|	    ((mplus) ((mtimes) a (($gauss_b) a b c x) b)
  #|	     ((mtimes) (($dgauss_b) a b c x)
  #|	      ((mplus) ((mtimes) -1 c)
  #|	       ((mtimes) ((mplus) 1 a b) x))))))
  #|	 'grad)

///|
fn init_share_gauss() -> Unit raise {
  share_odeutils__eval_put_forms(share_gauss__forms)
}
