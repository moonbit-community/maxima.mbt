// Port of src/rand-mt19937.lisp: the Mersenne Twister MT19937 random number
// generator (package mt19937, functions declared with an `mt_` prefix) and
// the Maxima-level functions set_random_state, make_random_state, random.
//
// The state is stored in a 627-element array of (unsigned-byte 32) wrapped
// in a random-state structure:
//
//   0-1:   Constant matrix A. [0, #x9908b0df]
//   2:     Index k.
//   3-626: State.
//
// The array holds `Fix` values; the arithmetic is done on `UInt` (32-bit,
// wrapping) which reproduces the Lisp `(ldb (byte 32 0) ...)` exactly.

///|
let mt__n : Int = 624

///|
let mt__m : Int = 397

///|
let mt__upper_mask : UInt = 0x80000000U

///|
let mt__lower_mask : UInt = 0x7fffffffU

///|
let mt__b : UInt = 0x9D2C5680U

///|
let mt__c : UInt = 0xEFC60000U

///|
/// Low 32 bits of a Lisp integer, as `UInt`.
fn mt__u32(v : Value) -> UInt raise {
  match v {
    Fix(n) => n.to_int().reinterpret_as_uint()
    _ => to_int64(logand(v, Fix(0xffffffffL))).to_int().reinterpret_as_uint()
  }
}

///|
fn mt__val(u : UInt) -> Value {
  Fix(u.to_uint64().reinterpret_as_int64())
}

///|
/// The data array of a Lisp vector.
fn mt__data(state : Value) -> Array[Value] raise {
  match state {
    Vec(a) => a.data
    _ => raise type_error(state, "(simple-array (unsigned-byte 32) (627))")
  }
}

///|
fn mt__new_state_array() -> Value {
  make_array([627], initial=Fix(0L), elt="(unsigned-byte 32)")
}

///|
/// `(make-random-object :state s)`
fn mt__make_random_object(s : Value) -> Value {
  make_struct("random-state", [s])
}

///|
fn mt__random_state_p(x : Value) -> Bool {
  struct_typep(x, "random-state")
}

///|
fn mt__random_state_state(x : Value) -> Value raise {
  struct_ref(x, 0)
}

///|
/// GENERATE-SEED: the current (universal) time is used as the seed.
fn mt_generate_seed() -> Value raise {
  // get-universal-time counts seconds since 1900-01-01.
  let secs = (wall_time_ms() / 1000UL).reinterpret_as_int64() + 2208988800L
  logand(Fix(secs), Fix(0xffffffffL))
}

///|
/// Initializer proposed by Takuji Nishimura and Makoto Matsumoto:
///   mt[0] = s & 0xffffffff
///   mt[k] = 1812433253 * (mt[k-1] ^ (mt[k-1] >> 30)) + k   (mod 2^32)
fn mt_int_init_random_state(
  seed? : Value = Fix(5489L),
  state? : Value = Nil,
) -> Value raise {
  let state = if state.truthy() { state } else { mt__new_state_array() }
  let d = mt__data(state)
  d[0] = Fix(0L)
  d[1] = Fix(0x9908b0dfL)
  d[2] = Fix(mt__n.to_int64())
  d[3] = seed
  let mut prev = mt__u32(seed)
  for k in 1..<624 {
    let v = 1812433253U * (prev ^ (prev >> 30)) + k.reinterpret_as_uint()
    d[3 + k] = mt__val(v)
    prev = v
  }
  state
}

///|
/// Initialize from an array (init_by_array of the reference implementation).
fn mt_vec_init_random_state(key : Value, state? : Value = Nil) -> Value raise {
  let key_len = mt__length_of_vector(key)
  let state = mt_init_random_state(seed=Fix(19650218L), state~)
  let d = mt__data(state)
  let mut i = 1
  let mut j = 0
  let mut k = if key_len > mt__n { key_len } else { mt__n }
  while k > 0 {
    let prev = mt__u32(d[3 + (i - 1)])
    let kj = mt__u32(aref1(key, j))
    d[3 + i] = mt__val(
      kj +
      j.reinterpret_as_uint() +
      (mt__u32(d[3 + i]) ^ (1664525U * (prev ^ (prev >> 30)))),
    )
    i += 1
    j += 1
    if i >= mt__n {
      d[3] = d[3 + (mt__n - 1)]
      i = 1
    }
    if j >= key_len {
      j = 0
    }
    k -= 1
  }
  k = mt__n - 1
  while k > 0 {
    let prev = mt__u32(d[3 + (i - 1)])
    d[3 + i] = mt__val(
      (mt__u32(d[3 + i]) ^ (1566083941U * (prev ^ (prev >> 30)))) -
      i.reinterpret_as_uint(),
    )
    i += 1
    if i >= mt__n {
      d[3] = d[3 + (mt__n - 1)]
      i = 1
    }
    k -= 1
  }
  d[3] = Fix(0x80000000L)
  state
}

///|
/// `(length key)` for a Lisp vector.
fn mt__length_of_vector(v : Value) -> Int raise {
  match v {
    Vec(a) =>
      match a.fill {
        Some(f) => f
        None => a.data.length()
      }
    _ => raise type_error(v, "(array (unsigned-byte 32) (*))")
  }
}

///|
/// Generate a random state vector from the given SEED.  The seed can be
/// either an integer or a vector of (unsigned-byte 32).
fn mt_init_random_state(
  seed? : Value = Fix(5489L),
  state? : Value = Nil,
) -> Value raise {
  if integerp(seed) {
    mt_int_init_random_state(
      seed=logand(seed, Fix(0xffffffffL)),
      state~,
    )
  } else if vectorp(seed) || arrayp(seed) {
    mt_vec_init_random_state(seed, state~)
  } else {
    raise LispError::SimpleError(
      format_to_string(
        "~S fell through ETYPECASE expression.~%Wanted one of (INTEGER (ARRAY (UNSIGNED-BYTE 32) (*))).",
        [seed],
      ),
    )
  }
}

///|
/// Make a random state object.  If STATE is not supplied, return a copy of
/// the default random state.  If STATE is a random state, then return a copy
/// of STATE.  If STATE is T then return a random state generated from the
/// universal time.
fn mt_make_random_state(state? : Value = Nil) -> Value raise {
  fn copy_random_state(st : Value) -> Value raise {
    let old = mt__data(mt__random_state_state(st))
    let new_state = mt__new_state_array()
    let nd = mt__data(new_state)
    for i in 0..<627 {
      nd[i] = old[i]
    }
    mt__make_random_object(new_state)
  }

  if state is Nil {
    copy_random_state(symval(q_ear_random_state))
  } else if mt__random_state_p(state) {
    copy_random_state(state)
  } else if eq(state, t) {
    mt__make_random_object(mt_init_random_state(seed=mt_generate_seed()))
  } else {
    raise LispError::SimpleError(
      format_to_string(
        "make_random_state: argument must be a random state object, or true, or false; found: ~S",
        [state],
      ),
    )
  }
}

///|
/// Regenerate the 624 state words.
fn mt_random_mt19937_update(state : Value) -> Value raise {
  let d = mt__data(state)
  let s : Array[UInt] = Array::make(627, 0U)
  for i in 0..<627 {
    s[i] = mt__u32(d[i])
  }
  let mut y : UInt = 0
  let mut kk = 3
  while kk < 3 + (mt__n - mt__m) {
    y = (s[kk] & mt__upper_mask) | (s[kk + 1] & mt__lower_mask)
    s[kk] = s[kk + mt__m] ^ (y >> 1) ^ s[(y & 1U).reinterpret_as_int()]
    kk += 1
  }
  kk = mt__n - mt__m + 3
  while kk < mt__n - 1 + 3 {
    y = (s[kk] & mt__upper_mask) | (s[kk + 1] & mt__lower_mask)
    s[kk] = s[kk + (mt__m - mt__n)] ^ (y >> 1) ^ s[(y & 1U).reinterpret_as_int()]
    kk += 1
  }
  y = (s[3 + (mt__n - 1)] & mt__upper_mask) | (s[3] & mt__lower_mask)
  s[3 + (mt__n - 1)] = s[3 + (mt__m - 1)] ^
    (y >> 1) ^
    s[(y & 1U).reinterpret_as_int()]
  for i in 3..<627 {
    d[i] = mt__val(s[i])
  }
  Nil
}

///|
/// Generate a 32bit integer between 0 and #xffffffff inclusive.
fn mt_random_chunk(state : Value) -> Value raise {
  let st = mt__random_state_state(state)
  let d = mt__data(st)
  let mut k = to_int(d[2])
  if k == mt__n {
    mt_random_mt19937_update(st) |> ignore
    k = 0
  }
  d[2] = Fix((k + 1).to_int64())
  let mut y = mt__u32(d[3 + k])
  y = y ^ (y >> 11)
  y = y ^ ((y & (mt__b >> 7)) << 7)
  y = y ^ ((y & (mt__c >> 15)) << 15)
  y = y ^ (y >> 18)
  mt__val(y)
}

///|
/// Handle the single float case of RANDOM.  We generate a float in
/// [0f0, 1f0) by clobbering the mantissa of 1f0 with random bits (23 bits);
/// this yields a number in [1f0, 2f0). Then 1f0 is subtracted.
/// (The port has no single floats; the result is rounded to single
/// precision and returned as a double.)
fn mt_p_random_single_float(arg : Value, state : Value) -> Value raise {
  let bits = mt_p_random_integer(Fix(8388608L), state)
  let unit = to_double(num_add(Fix(8388608L), bits)) * 0x1.0p-23 - 1.0
  let a = Float::from_double(to_double(arg))
  Flo((a * Float::from_double(unit)).to_double())
}

///|
/// Handle the double float case of RANDOM.  We generate a float in
/// [0d0, 1d0) by clobbering the mantissa of 1d0 with random bits (52 bits);
/// this yields a number in [1d0, 2d0). Then 1d0 is subtracted.
fn mt_p_random_double_float(arg : Value, state : Value) -> Value raise {
  let two52 = expt(Fix(2L), Fix(52L))
  let bits = mt_p_random_integer(two52, state)
  let unit = scale_float(to_double(num_add(two52, bits)), -52) - 1.0
  Flo(to_double(arg) * unit)
}

///|
/// Generates an integer greater than or equal to zero and less than Arg.
/// Successive chunks are concatenated without overlap to construct integers
/// larger than a single chunk.
fn mt_p_random_integer(arg : Value, state : Value) -> Value raise {
  let ilen = integer_length(one_minus(arg))
  let mut nchunks = to_int(num_ceiling(int(ilen), b=Fix(32L)).0)
  let mut bits : Value = Fix(0L)
  let mut shift = 0
  while nchunks != 0 {
    nchunks -= 1
    let new_bits = mt_random_chunk(state)
    bits = logior(bits, ash(new_bits, shift))
    shift += 32
  }
  num_rem(bits, arg)
}

///|
/// Generates a uniformly distributed pseudo-random number greater than or
/// equal to zero and less than Arg.  State, if supplied, is the random state
/// to use.
fn mt_random(arg : Value, state? : Value) -> Value raise {
  let state = match state {
    Some(s) => s
    None => symval(q_ear_random_state)
  }
  match arg {
    Flo(d) if d > 0.0 => mt_p_random_double_float(arg, state)
    _ =>
      if integerp(arg) && plusp(arg) {
        mt_p_random_integer(arg, state)
      } else {
        raise LispError::SimpleError(
          format_to_string(
            "random: argument must be a positive integer or a positive float; found: ~S",
            [arg],
          ),
        )
      }
  }
}

// begin Maxima-specific stuff

///|
/// Copy the argument, and assign the copy to MT19937::*RANDOM-STATE*.
/// Returns '$done.
fn d_set_random_state(x : Value) -> Value raise {
  set(q_ear_random_state, mt_make_random_state(state=x)) |> ignore
  q_d_done
}

///|
/// Returns a new random state object. If argument is an integer or array,
/// use argument to initialize random state. Otherwise punt to
/// MT19937::MAKE-RANDOM-STATE.
fn d_make_random_state(x : Value) -> Value raise {
  if integerp(x) || arrayp(x) {
    mt__make_random_object(mt_init_random_state(seed=x))
  } else {
    mt_make_random_state(state=x)
  }
}

///|
/// Returns the next number from this generator.  Punt to MT19937::RANDOM.
fn d_random(x : Value) -> Value raise {
  if (integerp(x) || floatp(x)) && plusp(x) {
    mt_random(x)
  } else {
    merr(
      "random: argument must be a positive integer or positive float; found: ~M",
      [x],
    )
  }
}

///|
fn init_rand_mt19937() -> Unit raise {
  // (defvar *random-state* (make-random-object))
  defvar_init(q_ear_random_state, mt__make_random_object(mt_init_random_state()))
}
