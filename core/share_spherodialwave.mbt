// Port of share/contrib/diffequations/spherodialwave.lisp (Barton Willis, 2004):
// derivatives (grad properties) of the spheroidal wave functions,
// for odelin. The file consists of top-level
// $put and putprop forms only; they are kept in their Lisp source form
// and evaluated by `share_odeutils__eval_put_forms` at load time.

///|
let share_spherodialwave__forms : String =
  #|($put '$spherodialwave 1 '$version)
  #|
  #|(putprop '$spherodialwave_a
  #|	 '((b c q x)
  #|	   ((unk) "$order" "$spherodialwave_a")
  #|	   ((unk) "$order" "$spherodialwave_a")
  #|	   ((unk) "$order" "$spherodialwave_a")
  #|	   (($dspherodialwave_a) b c q x))
  #|	 'grad)
  #|
  #|(putprop '$dspherodialwave_a
  #|	 '((b c q x)
  #|	   ((unk) "$order" "$dspherodialwave_a")
  #|	   ((unk) "$order" "$dspherodialwave_a")
  #|	   ((unk) "$order" "$dspherodialwave_a")
  #|	   ((mtimes) -1
  #|	    ((mexpt) ((mplus) -1 ((mexpt) x 2)) -1)
  #|	    ((mplus)
  #|	     ((mtimes) -1 (($spherodialwave_a) b c q x) c)
  #|	     ((mtimes) ((mplus) 2 ((mtimes) 2 b))
  #|	      (($dspherodialwave_a) b c q x) x)
  #|	     ((mtimes) 4 (($spherodialwave_a) b c q x) q
  #|	      ((mexpt) x 2)))))
  #|	 'grad)
  #|
  #|(putprop '$spherodialwave_b
  #|	 '((b c q x)
  #|	   ((unk) "$order" "$spherodialwave_b")
  #|	   ((unk) "$order" "$spherodialwave_b")
  #|	   ((unk) "$order" "$spherodialwave_b")
  #|	   (($dspherodialwave_b) b c q x))
  #|	 'grad)
  #|
  #|(putprop '$dspherodialwave_b
  #|	 '((b c q x)
  #|	   ((unk) "$order" "$dspherodialwave_b")
  #|	   ((unk) "$order" "$dspherodialwave_b")
  #|	   ((unk) "$order" "$dspherodialwave_b")
  #|	   ((mtimes) -1
  #|	    ((mexpt) ((mplus) -1 ((mexpt) x 2)) -1)
  #|	    ((mplus)
  #|	     ((mtimes) -1 (($spherodialwave_b ) b c q x) c)
  #|	     ((mtimes) ((mplus) 2 ((mtimes) 2 b))
  #|	      (($dspherodialwave_b) b c q x) x)
  #|	     ((mtimes) 4 (($spherodialwave_b) b c q x) q
  #|	      ((mexpt) x 2)))))
  #|	 'grad)

///|
fn init_share_spherodialwave() -> Unit raise {
  share_odeutils__eval_put_forms(share_spherodialwave__forms)
}
