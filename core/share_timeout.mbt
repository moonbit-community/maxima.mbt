// Port of share/contrib/timeout.lisp: stopme and time_constrained (SBCL
// only in Maxima).
//
// stopme and time_constrained are the same except that time_constrained,
// in case of timeout, simply returns the expression Aborted. stopme gives a
// message, and returns it. The message contains the unevaluated expr.
//
// SBCL implements them with sb-ext timers, which interrupt the running
// computation asynchronously. The port has no asynchronous interrupts: the
// scheduled timers are polled by `meval1` (see
// `share_timeout__check_timers`), so a timer fires at the next evaluation of
// a Maxima form after its deadline -- which covers Maxima-level loops, but
// not a single long-running Lisp-level computation.

///|
/// Scheduled timers: (id, deadline in ms of wall time, action).
let share_timeout__timers : Array[(Int, UInt64, () -> Unit raise)] = []

///|
let share_timeout__next_id : Ref[Int] = { val: 0 }

///|
/// Earliest deadline of the scheduled timers, 0 when there is none. Read by
/// `meval1` on every evaluation, so it must stay cheap.
let share_timeout__deadline : Ref[UInt64] = { val: 0UL }

///|
fn share_timeout__recompute_deadline() -> Unit {
  let mut d = 0UL
  for tm in share_timeout__timers {
    if d == 0UL || tm.1 < d {
      d = tm.1
    }
  }
  share_timeout__deadline.val = d
}

///|
/// sb-ext:schedule-timer: run `action` after `seconds` seconds.
fn share_timeout__schedule(
  seconds : Value,
  action : () -> Unit raise,
) -> Int raise {
  let secs = to_double(seconds)
  let ms = if secs <= 0.0 { 0UL } else { (secs * 1000.0).to_uint64() }
  let id = share_timeout__next_id.val
  share_timeout__next_id.val = id + 1
  share_timeout__timers.push((id, wall_time_ms() + ms, action))
  share_timeout__recompute_deadline()
  id
}

///|
/// sb-ext:unschedule-timer.
fn share_timeout__unschedule(id : Int) -> Unit {
  for i, tm in share_timeout__timers {
    if tm.0 == id {
      share_timeout__timers.remove(i) |> ignore
      break
    }
  }
  share_timeout__recompute_deadline()
}

///|
/// Called by `meval1` when a timer is scheduled: fire the expired timers
/// (each fires once).
fn share_timeout__check_timers() -> Unit raise {
  let now = wall_time_ms()
  if now < share_timeout__deadline.val {
    return
  }
  for i, tm in share_timeout__timers {
    if tm.1 <= now {
      share_timeout__timers.remove(i) |> ignore
      share_timeout__recompute_deadline()
      (tm.2)()
      return
    }
  }
  share_timeout__recompute_deadline()
}

///|
/// usage: stopme (do x:x+1, 2) ; stops infinite loop after 2 sec
fn d_stopme(args : Value) -> Value raise {
  let evalme = cadr(args) // not evaluated !
  let timelimit = meval(caddr(args)) // evaluate the time limit
  catch_tag(q_stopme, () => {
    let v = share_timeout__schedule(timelimit, () => {
      // the timer program
      let msg = list([
        list1(q_mtext),
        evalme,
        Str("   timed out after "),
        timelimit,
        Str(" seconds"),
      ])
      mformat(list([t, Str("~m"), msg])) |> ignore
      throw_tag(q_stopme, msg) |> ignore
    })
    defer share_timeout__unschedule(v)
    meval(evalme)
  })
}

///|
/// usage: time_constrained (do x:x+1, 2) ; returns Aborted after 2 sec
fn d_time_constrained(args : Value) -> Value raise {
  let evalme = cadr(args) // not evaluated !
  let timelimit = meval(caddr(args)) // evaluate the time limit
  catch_tag(q_stopme, () => {
    let v = share_timeout__schedule(timelimit, () => {
      throw_tag(q_stopme, q_d_aborted) |> ignore
    })
    defer share_timeout__unschedule(v)
    meval(evalme)
  })
}
