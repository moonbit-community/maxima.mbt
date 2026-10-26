// Port of share/contrib/integration/abs_integrate.lisp.

///|
/// `$integration_depth`
fn d_integration_depth() -> Value raise {
  if boundp(q_ear_integrator_level) {
    symval(q_ear_integrator_level)
  } else {
    Fix(0L)
  }
}

///|
fn init_share_abs_integrate() -> Unit raise {
  defmvar(
    q_d_extra_integration_methods,
    val=simplifya(
      list([
        list1(q_mlist),
        q_d_intfudu,
        q_d_intfugudu,
        q_d_signum_int,
        q_d_abs_integrate_use_if,
        q_d_floor_int,
        q_d_if_int,
      ]),
      t,
    ),
    Nil,
  )
  |> ignore
  defmvar(
    q_d_extra_definite_integration_methods,
    val=simplifya(list([list1(q_mlist), q_d_abs_defint]), t),
    Nil,
  )
  |> ignore
}
