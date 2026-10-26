// Port of share/sound/sound.lisp: a Maxima sound package (Mario Rodriguez
// Riotorto, 2009-2015). Sound samples are kept in a 2-dimensional Lisp
// array of floats ($sound_sample, channels x samples) and saved as WAV or
// text files.

///|
fn init_share_sound() -> Unit raise {
  d_put(q_d_sound, Flo(0.0), q_d_version) |> ignore
  // load package 'draw'
  if d_get(q_d_draw, q_d_version) is Nil {
    d_load(Str("draw")) |> ignore
  }
  // load package 'distrib'
  if d_get(sym("$distrib"), q_d_version) is Nil {
    d_load(Str("distrib")) |> ignore
  }
  // load package 'numericalio'
  d_load(Str("numericalio")) |> ignore
  // load package 'stringproc'
  d_load(Str("stringproc")) |> ignore
  // This variable stores actual sound options
  defvar_init(q_ear_sound_options, make_hash_table())
  ini_sound_options() |> ignore
}

///|
fn share_sound__sample_array() -> Value raise {
  symval(q_d_sound_sample)
}

///|
fn d_sound_sample_size() -> Value raise {
  let s = share_sound__sample_array()
  if arrayp(s) {
    cadr(array_dimensions(s))
  } else {
    Nil
  }
}

///|
fn d_sound_sample_channels() -> Value raise {
  let s = share_sound__sample_array()
  if arrayp(s) {
    car(array_dimensions(s))
  } else {
    Nil
  }
}

///|
fn d_sound_sample_list(chn : Value) -> Value raise {
  if !integerp(chn) ||
    num_lt(chn, Fix(0L)) ||
    num_gt(chn, d_sound_sample_channels()) {
    merr("sound: incorrect number of channels", []) |> ignore
  }
  let n = to_int(d_sound_sample_size())
  let arr = make_array([n], initial=Flo(0.0))
  for s in 0..<n {
    aset(arr, [s], aref(share_sound__sample_array(), [0, s])) |> ignore
  }
  d_listarray(arr)
}

// (defstruct a-wave sample channel att-coef repeat-at)

///|
fn share_sound__make_a_wave(
  sample : Value,
  channel : Value,
  att_coef : Value,
  repeat_at : Value,
) -> Value {
  make_struct("a-wave", [sample, channel, att_coef, repeat_at])
}

///|
fn share_sound__a_wave_sample(w : Value) -> Value raise {
  struct_ref(w, 0)
}

///|
fn share_sound__a_wave_channel(w : Value) -> Value raise {
  struct_ref(w, 1)
}

///|
fn share_sound__a_wave_att_coef(w : Value) -> Value raise {
  struct_ref(w, 2)
}

///|
fn share_sound__a_wave_repeat_at(w : Value) -> Value raise {
  struct_ref(w, 3)
}

///|
fn d_set_sound_defaults(opts : Value) -> Value raise {
  set(q_ear_user_sound_default_options, opts) |> ignore
  cons(list1(q_mlist), opts)
}

///|
fn share_sound__options() -> Value raise {
  symval(q_ear_sound_options)
}

///|
fn share_sound__set_option(opt : Value, val : Value) -> Value raise {
  sethash(opt, share_sound__options(), val)
}

///|
/// Sets default values of sound options
fn ini_sound_options() -> Value raise {
  share_sound__set_option(q_d_channel, Fix(1L)) |> ignore
  share_sound__set_option(q_d_file_name, Str("maxout")) |> ignore
  share_sound__set_option(q_d_file_format, sym("$wav")) |> ignore
  share_sound__set_option(q_d_oscillator, list([list1(q_d_sine), Flo(1.0)]))
  |> ignore
  share_sound__set_option(q_d_envelope, q_d_none) |> ignore
  share_sound__set_option(q_d_noise_generator, q_d_none) |> ignore
  share_sound__set_option(q_d_attenuation_coef, list([list1(q_mlist), Flo(1.0)]))
  |> ignore
  share_sound__set_option(q_d_normalize, q_d_auto) |> ignore
  share_sound__set_option(q_d_player, q_d_none) |> ignore
  share_sound__set_option(q_d_player_options, q_d_none) |> ignore
  share_sound__set_option(q_d_draw_wave_options, list1(list1(q_mlist))) |> ignore
  share_sound__set_option(q_d_draw_wave, Nil)
}

///|
/// Gives value of option
fn get_sound_option(opt : Value) -> Value raise {
  gethash(opt, share_sound__options())
}

///|
fn share_sound__float_args(val : Value) -> Value raise {
  cdr(d_float(d_args(val)))
}

///|
fn update_sound_option(opt : Value, val : Value) -> Value raise {
  if eq(opt, q_d_channel) {
    // defined as a non negative integer
    if integerp(val) && plusp(val) {
      share_sound__set_option(opt, val)
    } else {
      merr("sound: illegal channel: ~M ", [val])
    }
  } else if eq(opt, q_d_file_name) {
    share_sound__set_option(opt, d_sconcat(list1(val)))
  } else if eq(opt, q_d_file_format) {
    // defined as a wav or txt
    let val = d_concat(list1(val))
    if memq(val, list([sym("$wav"), sym("$txt")])).truthy() {
      share_sound__set_option(opt, val)
    } else {
      merr("sound: illegal file_format option: ~M ", [val])
    }
  } else if eq(opt, q_d_oscillator) {
    if d_atom(val).truthy() {
      merr("sound: oscillator must be an expression", []) |> ignore
    }
    if equal(d_op(val), q_d_sine) {
      let param = share_sound__float_args(val)
      if !every(
          z => floatp(z) ||
            (
              d_listp(z).truthy() &&
              num_eq(d_length(z), Fix(2L)) &&
              floatp(cadr(z)) &&
              num_gt(cadr(z), Fix(0L)) &&
              floatp(caddr(z)) &&
              num_le(Flo(0.0), caddr(z)) &&
              num_le(caddr(z), Flo(1.0))
            ),
          param,
        ) {
        merr("sound: incorrect argument(s) in sine oscillator", []) |> ignore
      }
      share_sound__set_option(opt, cons(list([q_d_sine, q_simp]), param))
    } else if memq(d_op(val), list([sym("$rectangle"), sym("$triangle")])).truthy() {
      let param = d_float(cadr(val))
      if !(
          floatp(param) &&
          num_gt(param, Flo(0.0)) &&
          num_lt(param, Flo(1.0))
        ) {
        merr("sound: incorrect argument in ~M oscillator", [d_op(val)])
        |> ignore
      }
      share_sound__set_option(opt, val)
    } else {
      merr("sound: oscillator not recognized", [])
    }
  } else if eq(opt, q_d_envelope) {
    if d_atom(val).truthy() && equal(val, q_d_none) {
      share_sound__set_option(opt, val)
    } else if d_atom(val).truthy() {
      merr("sound: unknown envelope", [])
    } else if equal(d_op(val), sym("$pairs")) {
      let param = share_sound__float_args(val)
      if some(
          z => !d_listp(z).truthy() ||
            !num_eq(d_length(z), Fix(2L)) ||
            !floatp(cadr(z)) ||
            !floatp(caddr(z)),
          param,
        ) {
        merr("sound: incorrect arguments to pairs envelope", []) |> ignore
      }
      share_sound__set_option(
        opt,
        cons(list([sym("$pairs"), q_simp]), mapcar(z => cdr(z), param)),
      )
    } else if equal(d_op(val), sym("$adsr")) {
      let param = share_sound__float_args(val)
      if length(param) != 4 ||
        some(z => !floatp(z) || num_lt(z, Flo(0.0)), param) {
        merr("sound: adsr envelope needs four non negative arguments", [])
        |> ignore
      }
      let attack = car(param)
      let decay = cadr(param)
      let sustain_level = caddr(param)
      let release = cadddr(param)
      if num_gt(num_add(num_add(attack, decay), release), Flo(1.0)) ||
        num_gt(sustain_level, Flo(1.0)) {
        merr("sound: incorrect arguments to adsr envelope", []) |> ignore
      }
      share_sound__set_option(
        opt,
        list([
          list([sym("$pairs"), q_simp]),
          list([Flo(0.0), Flo(0.0)]),
          list([attack, Flo(1.0)]),
          list([num_add(attack, decay), sustain_level]),
          list([num_sub(Flo(1.0), release), sustain_level]),
          list([Flo(1.0), Flo(0.0)]),
        ]),
      )
    } else if equal(d_op(val), q_d_function) {
      let param = share_sound__float_args(val)
      if !num_eq(d_length(param), Fix(3L)) ||
        !floatp(nth(2, param)) ||
        !floatp(nth(3, param)) ||
        !num_lt(nth(2, param), nth(3, param)) {
        merr("sound: incorrect arguments to function envelope", []) |> ignore
      }
      share_sound__set_option(opt, cons(list([q_d_function, q_simp]), param))
    } else {
      merr("sound: unknown envelope type", [])
    }
  } else if eq(opt, q_d_noise_generator) {
    if d_atom(val).truthy() && equal(val, q_d_none) {
      share_sound__set_option(opt, val)
    } else if d_atom(val).truthy() {
      merr("sound: unknown noise generator", [])
    } else if equal(d_op(val), sym("$gaussian")) {
      let param = share_sound__float_args(val)
      if length(param) != 2 ||
        !floatp(car(param)) ||
        !floatp(cadr(param)) ||
        num_le(cadr(param), Flo(0.0)) {
        merr("sound: gaussian noise generator is not correctly defined", [])
        |> ignore
      }
      share_sound__set_option(opt, cons(list([sym("$gaussian"), q_simp]), param))
    } else if equal(d_op(val), sym("$uniform")) {
      let param = share_sound__float_args(val)
      if length(param) != 2 ||
        !floatp(car(param)) ||
        !floatp(cadr(param)) ||
        num_lt(cadr(param), car(param)) {
        merr("sound: uniform noise generator is not correctly defined", [])
        |> ignore
      }
      share_sound__set_option(opt, cons(list([sym("$uniform"), q_simp]), param))
    } else {
      merr("sound: unknown noise generator", [])
    }
  } else if eq(opt, q_d_attenuation_coef) {
    let coefs = d_float(val)
    if d_listp(val).truthy() && every(z => floatp(z), cdr(coefs)) {
      share_sound__set_option(opt, coefs)
    } else {
      merr("sound: illegal attenuation coefficients specification", [])
    }
  } else if eq(opt, q_d_player) {
    share_sound__set_option(opt, val)
  } else if eq(opt, q_d_player_options) {
    share_sound__set_option(opt, val)
  } else if eq(opt, q_d_draw_wave_options) {
    if d_listp(val).truthy() {
      share_sound__set_option(opt, val)
    } else {
      merr("sound: draw_wave_options must be a list of draw options", [])
    }
  } else if eq(opt, q_d_normalize) {
    if equal(val, q_d_auto) ||
      equal(val, q_d_none) ||
      (integerp(val) && plusp(val) && num_le(val, Fix(32767L))) {
      share_sound__set_option(opt, val)
    } else {
      merr("sound: illegal normalize option: ~M ", [val])
    }
  } else if eq(opt, q_d_draw_wave) {
    // defined as true or false
    if equal(val, t) || val is Nil {
      share_sound__set_option(opt, val)
    } else {
      merr("sound: non boolean value: ~M ", [val])
    }
  } else {
    Nil
  }
}

///|
/// Sets user default values of sound options
fn sound_user_defaults() -> Value raise {
  for x in symval(q_ear_user_sound_default_options).iter() {
    if equal(d_op(x), Str("=")) {
      update_sound_option(d_lhs(x), d_rhs(x)) |> ignore
    } else {
      merr("sound: item ~M is not recognized as an option assignment", [x])
      |> ignore
    }
  }
  Nil
}

// File functions

///|
/// Saves sound sample in plain text file, with one row per channel, and as
/// many columns as samples.
fn d_save_sound_txt() -> Value raise {
  d_write_data(
    share_sound__sample_array(),
    d_sconcat(list([get_sound_option(q_d_file_name), Str(".txt")])),
  )
}

///|
/// (round (coerce x 'single-float)): round half to even of the value as a
/// single float.
fn share_sound__round_single(x : Value) -> Int64 raise {
  let d = Float::from_double(to_double(x)).to_double()
  let f = d.floor()
  let diff = d - f
  let r = if diff > 0.5 {
    f + 1.0
  } else if diff < 0.5 {
    f
  } else if (f * 0.5).floor() * 2.0 == f {
    f
  } else {
    f + 1.0
  }
  r.to_int64()
}

///|
/// wav format info : http://www.sonicspot.com/guide/wavefiles.html
fn d_save_sound_wav() -> Value raise {
  let samp = share_sound__sample_array()
  let num_chn = array_dimension(samp, 0)
  let num_sam = array_dimension(samp, 1)
  let fname = get_sound_option(q_d_file_name)
  let path = plot_temp_file(
    d_sconcat(list([fname, Str(".wav")])),
    preserve_file=t,
  )
  let out = @buffer.new()
  let write16 = (i : Int64) => {
    out.write_byte((i & 0xffL).to_byte())
    out.write_byte(((i >> 8) & 0xffL).to_byte())
  }
  let write32 = (i : Int64) => {
    out.write_byte((i & 0xffL).to_byte())
    out.write_byte(((i >> 8) & 0xffL).to_byte())
    out.write_byte(((i >> 16) & 0xffL).to_byte())
    out.write_byte(((i >> 24) & 0xffL).to_byte())
  }
  let rate = symval(q_d_sound_sample_rate)
  let nc = num_chn.to_int64()
  let ns = num_sam.to_int64()
  write32(0x46464952L) // string "RIFF"
  write32(2L * nc * ns + 36L) // filesize-8
  write32(0x45564157L) // string "WAVE"
  write32(0x20746d66L) // string "fmt "
  write32(16L) // format bytes
  write16(1L) // compression code
  write16(nc) // number of channels
  write32(share_sound__int64(round1(rate))) // sample rate
  write32(
    share_sound__int64(round1(num_mul(num_mul(Flo(2.0), rate), Fix(nc)))),
  ) // average bytes per second
  write16(2L * nc) // block align
  write16(16L) // significant bits per sample
  write32(0x61746164L) // string "data"
  write32(2L * nc * ns)
  for s in 0..<num_sam {
    for c in 0..<num_chn {
      write16(share_sound__round_single(aref(samp, [c, s])))
    }
  }
  @lisp.write_file_bytes(share_mathml__str(path), out.to_bytes())
  Nil
}

///|
fn share_sound__int64(x : Value) -> Int64 raise {
  match x {
    Fix(n) => n
    _ => to_double(x).to_int64()
  }
}

///|
/// A binary input file read whole: (read-byte in) and (file-position in).
struct ShareSoundIn {
  data : Bytes
  mut pos : Int
}

///|
fn ShareSoundIn::read_byte(self : ShareSoundIn) -> Int raise {
  if self.pos >= self.data.length() {
    raise LispError::Condition(
      intern("end-of-file"),
      "end of file on the WAV stream",
      Nil,
    )
  }
  let b = self.data[self.pos].to_int()
  self.pos += 1
  b
}

///|
fn ShareSoundIn::read16(self : ShareSoundIn) -> Int64 raise {
  let dat1 = self.read_byte().to_int64()
  let dat2 = self.read_byte().to_int64()
  dat1 | (dat2 << 8)
}

///|
fn ShareSoundIn::read32(self : ShareSoundIn) -> Int64 raise {
  let dat1 = self.read_byte().to_int64()
  let dat2 = self.read_byte().to_int64()
  let dat3 = self.read_byte().to_int64()
  let dat4 = self.read_byte().to_int64()
  dat1 | (dat2 << 8) | (dat3 << 16) | (dat4 << 24)
}

///|
fn d_load_sound_wav(fname : Value, verbose? : Value = t) -> Value raise {
  let path = match fname {
    Str(s) => s
    _ =>
      raise LispError::SimpleError(
        "The value " + prin1_to_string(fname) + " is not of type SIMPLE-STRING",
      )
  }
  let in_ : ShareSoundIn = { data: read_file_bytes(path), pos: 0 }
  let mut num_channels = 0L
  let mut n_samples_per_sec = 0L
  let mut n_bits_per_sample = 0L
  let mut total_bytes = 0L
  if in_.read32() != 0x46464952L {
    merr("sound: file to read is not of RIFF structure", []) |> ignore
  }
  let _file_size = in_.read32()
  if in_.read32() != 0x45564157L {
    merr("sound: file to read is not of WAVE format", []) |> ignore
  }
  // look for format specification and sample length
  while true {
    let next_header = in_.read32()
    let bytes = in_.read32()
    if next_header == 0x20746d66L {
      let _compression_code = in_.read16()
      num_channels = in_.read16()
      n_samples_per_sec = in_.read32()
      let _average_bytes_per_second = in_.read32()
      let _block_align = in_.read16()
      n_bits_per_sample = in_.read16()
      // possible extra (ignored) format bytes
      for _i = 0L; _i < bytes - 16L; _i = _i + 1L {
        in_.read_byte() |> ignore
      }
    } else if next_header == 0x61746164L {
      total_bytes = bytes
      break
    } else {
      for _i = 0L; _i < bytes; _i = _i + 1L {
        in_.read_byte() |> ignore
      }
    }
  }
  let header_bytes = in_.pos.to_int64()
  // with available parameters, let's read the file
  let total_num_samples = num_div(Fix(8L * total_bytes), Fix(n_bits_per_sample))
  let num_samples = num_div(total_num_samples, Fix(num_channels))
  if verbose.truthy() {
    print(
      Str(format_to_string("Number of channels.: ~a", [Fix(num_channels)])),
    )
    |> ignore
    print(
      Str(format_to_string("Samples per second.: ~a", [Fix(n_samples_per_sec)])),
    )
    |> ignore
    print(
      Str(format_to_string("Bits per sample....: ~a", [Fix(n_bits_per_sample)])),
    )
    |> ignore
    print(
      Str(format_to_string("Number of samples..: ~a", [total_num_samples])),
    )
    |> ignore
  }
  let n_total = to_int(total_num_samples)
  let sample_sequence : Array[Int64] = Array::make(n_total, 0L)
  // the samples are read as (unsigned-byte 8) or (signed-byte n) elements,
  // starting at element (/ n-bits-header n-bits-per-sample)
  let elt_bytes = (n_bits_per_sample + 7L) / 8L
  let start = to_int(num_div(Fix(8L * header_bytes), Fix(n_bits_per_sample)))
  let mut p = start * elt_bytes.to_int()
  let data = in_.data
  for k in 0..<n_total {
    if p + elt_bytes.to_int() > data.length() {
      break
    }
    let mut v = 0L
    for b = elt_bytes.to_int() - 1; b >= 0; b = b - 1 {
      v = (v << 8) | data[p + b].to_int64()
    }
    if n_bits_per_sample != 8L {
      let bits = n_bits_per_sample.to_int()
      if ((v >> (bits - 1)) & 1L) == 1L {
        v = v - (1L << bits)
      }
    }
    sample_sequence[k] = v
    p += elt_bytes.to_int()
  }
  let nch = num_channels.to_int()
  let rows = Collector::new()
  for k in 0..<to_int(num_samples) {
    let row = Collector::new()
    for j in 0..<nch {
      row.add(Fix(sample_sequence[j + k * nch]))
    }
    rows.add(cons(list([q_mlist, q_simp]), row.result()))
  }
  list([
    list([q_mlist, q_simp]),
    Fix(n_samples_per_sec),
    cons(list([q_mlist, q_simp]), rows.result()),
  ])
}

///|
fn save_sound() -> Value raise {
  let ff = get_sound_option(q_d_file_format)
  if eq(ff, sym("$wav")) {
    d_save_sound_wav()
  } else if eq(ff, sym("$txt")) {
    d_save_sound_txt()
  } else {
    Nil
  }
}

// Draw & play functions

///|
fn share_sound__gr2d_objects(
  options : (Int) -> Value raise,
) -> Value raise {
  let samp = share_sound__sample_array()
  let num_chn = array_dimension(samp, 0)
  let num_sam = array_dimension(samp, 1)
  let time = to_double(
    num_div(Fix(num_sam.to_int64()), symval(q_d_sound_sample_rate)),
  )
  let array1d = make_array([num_sam], initial=Flo(0.0))
  sound_user_defaults() |> ignore
  let objs = Collector::new()
  for c in 0..<num_chn {
    for s in 0..<num_sam {
      aset(array1d, [s], aref(samp, [c, s])) |> ignore
    }
    objs.add(
      d_apply(
        q_d_gr2d,
        d_append(
          list([
            list([
              list1(q_mlist),
              mk(q_mequal, [q_d_points_joined, t]),
              mk(q_mequal, [q_d_point_size, Fix(0L)]),
              mk(q_mequal, [
                q_d_xrange_secondary,
                list([list1(q_mlist), Fix(0L), Flo(time)]),
              ]),
              mk(q_mequal, [q_d_xtics_secondary, q_d_auto]),
              mk(q_mequal, [q_d_color, q_d_blue]),
              mk(q_mequal, [
                q_d_title,
                d_sconcat(
                  list([Str("Sound wave. Channel-"), Fix((c + 1).to_int64())]),
                ),
              ]),
            ]),
            options(c),
            list([
              list([q_mlist, q_simp]),
              list([list1(q_d_points), d_listarray(array1d)]),
            ]),
          ]),
        ),
      ),
    )
  }
  cons(list([q_mlist, q_simp]), objs.result())
}

///|
fn d_draw_sound() -> Value raise {
  let objs = share_sound__gr2d_objects(_ => get_sound_option(
    q_d_draw_wave_options,
  ))
  d_apply(q_d_draw, objs)
}

///|
/// draw_sound for wxMaxima
fn d_wxdraw_sound() -> Value raise {
  let objs = share_sound__gr2d_objects(_ => {
    let acc = Collector::new()
    for x in get_sound_option(q_d_draw_wave_options).iter() {
      if !(equal(q_d_terminal, nth(1, x)) || equal(q_d_file_name, nth(1, x))) {
        acc.add(x)
      }
    }
    acc.result()
  })
  d_apply(q_d_wxdraw, objs)
}

///|
fn d_play_sound() -> Value raise {
  if !(
      equal(get_sound_option(q_d_file_format), sym("$wav")) &&
      !equal(get_sound_option(q_d_player), q_d_none)
    ) {
    return Nil
  }
  let str = get_sound_option(q_d_player)
  let mut res1 : Value = Nil
  let mut res2 : Value = Nil
  if equal(symval(q_ear_autoconf_windows), Str("true")) {
    res1 = d_ssearch(Str(":"), str, Nil)
    res2 = d_ssearch(Str("\\"), str, Nil)
    res1 = if res2.truthy() &&
      num_ge(res2, Fix(1L)) &&
      !(res1.truthy() && num_eq(res1, Fix(2L))) {
      Fix(1L)
    } else {
      Nil
    }
  } else {
    res1 = d_ssearch(Str("/"), str, Nil)
    res1 = if res1.truthy() &&
      num_gt(res1, Fix(1L)) &&
      !num_eq(res1, Fix(1L)) {
      Fix(1L)
    } else {
      Nil
    }
  }
  res2 = get_sound_option(q_d_player_options)
  if equal(res2, q_d_none) {
    res2 = Str("")
  }
  let wav = plot_temp_file(get_sound_option(q_d_file_name), preserve_file=t)
  if res1.truthy() {
    let ty = d_pathname_type(str)
    d_system(
      list1(
        format(Nil, "\"~a~a\" ~a \"~a.wav\"", [
          d_first(d_directory(d_pathname_directory(str))),
          d_sconcat(
            list([
              d_pathname_name(str),
              if ty is Nil {
                Str("")
              } else {
                d_sconcat(list([Str("."), ty]))
              },
            ]),
          ),
          res2,
          wav,
        ]),
      ),
    )
  } else {
    d_system(
      list1(format(Nil, "\"~a\" ~a \"~a.wav\"", [str, res2, wav])),
    )
  }
}

// Envelope functions

///|
fn share_sound__flo(x : Value) -> Double raise {
  to_double(x)
}

///|
fn pairs_envelope(samp : Value) -> Value raise {
  let n = array_dimension(samp, 0)
  let mut args = cdr(d_args(get_sound_option(q_d_envelope)))
  let d = 1.0 / n.to_double()
  let mut x = 0.0
  // order with respect to 1st coordinate
  args = sort_list(args, (p1, p2) => num_le(car(p1), car(p2)))
  // is args a list of pairs in [0, 1]^2 ?
  if some(
      z => num_lt(car(z), Flo(0.0)) ||
        num_gt(car(z), Flo(1.0)) ||
        num_lt(cadr(z), Flo(0.0)) ||
        num_gt(cadr(z), Flo(1.0)),
      args,
    ) {
    merr("sound: arguments in pairs envelope must be in [0, 1]^2", [])
    |> ignore
  }
  // add extremes x=0 and y=0 if not already present
  args = append(
    if num_eq(caar(args), Flo(0.0)) {
      Nil
    } else {
      list1(list([Flo(0.0), Flo(0.0)]))
    },
    append(
      args,
      if num_eq(caar(last(args)), Flo(1.0)) {
        Nil
      } else {
        list1(list([Flo(1.0), Flo(0.0)]))
      },
    ),
  )
  // apply envelope joining pairs with linear segments
  let mut counter = 1
  for k in 0..<n {
    while true {
      let x1 = share_sound__flo(car(nth(counter - 1, args)))
      let x2 = share_sound__flo(car(nth(counter, args)))
      if x1 <= x && x < x2 {
        let y1 = share_sound__flo(cadr(nth(counter - 1, args)))
        let y2 = share_sound__flo(cadr(nth(counter, args)))
        let m = (y2 - y1) / (x2 - x1)
        let y = y1 + m * (x - x1)
        aset(samp, [k], num_mul(aref(samp, [k]), Flo(y))) |> ignore
        break
      }
      counter += 1
    }
    x = x + d
  }
  Nil
}

///|
fn function_envelope(samp : Value) -> Value raise {
  let n = array_dimension(samp, 0)
  let args = cdr(d_args(get_sound_option(q_d_envelope)))
  let fcn = car(args)
  let var_ = cadr(args)
  let lim1 = share_sound__flo(caddr(args))
  let lim2 = share_sound__flo(cadddr(args))
  let d = (lim2 - lim1) / n.to_double()
  let mut xx = lim1
  let fcn = coerce_float_fun(
    meval(list([list1(q_d_float), fcn])),
    list1(list([list1(q_mlist), var_])),
  )
  for k in 0..<n {
    let y = funcall(fcn, [Flo(xx)])
    aset(samp, [k], num_mul(aref(samp, [k]), y)) |> ignore
    xx = xx + d
  }
  Nil
}

///|
fn apply_envelope(samp : Value) -> Value raise {
  if !equal(get_sound_option(q_d_envelope), q_d_none) {
    let env = get_sound_option(q_d_envelope)
    let op = d_op(env)
    if eq(op, sym("$pairs")) {
      return pairs_envelope(samp)
    } else if eq(op, q_d_function) {
      return function_envelope(samp)
    }
  }
  Nil
}

// Noise functions

///|
fn share_sound__add_noise(samp : Value, fun : Value) -> Value raise {
  let n = array_dimension(samp, 0)
  let param = cdr(get_sound_option(q_d_noise_generator))
  let noise = cdr(mfuncall(fun, list([car(param), cadr(param), int(n)])))
  for k in 0..<n {
    aset(samp, [k], num_add(aref(samp, [k]), nth(k, noise))) |> ignore
  }
  Nil
}

///|
fn gaussian_noise(samp : Value) -> Value raise {
  share_sound__add_noise(samp, q_d_random_normal)
}

///|
fn uniform_noise(samp : Value) -> Value raise {
  share_sound__add_noise(samp, q_d_random_continuous_uniform)
}

///|
fn apply_noise(samp : Value) -> Value raise {
  if !equal(get_sound_option(q_d_noise_generator), q_d_none) {
    let noise = get_sound_option(q_d_noise_generator)
    let op = d_op(noise)
    if eq(op, sym("$gaussian")) {
      return gaussian_noise(samp)
    } else if eq(op, sym("$uniform")) {
      return uniform_noise(samp)
    }
  }
  Nil
}

// Oscillator functions

///|
fn apply_oscillator_model(
  samp : Value,
  per1_samp : Value,
  ampl : Value,
) -> Value raise {
  let mut xx = 0.0
  let osc = get_sound_option(q_d_oscillator)
  let op = d_op(osc)
  let per1 = to_int(per1_samp)
  if eq(op, q_d_sine) {
    let harmonics = cdr(d_args(osc))
    let pi = 3.141592653589793
    let d = 2.0 * pi / per1.to_double()
    for k in 0..<per1 {
      let mut s = 0.0
      for h in harmonics.iter() {
        let (harm, rampl) = if floatp(h) {
          // user gives only the harmonic number
          (to_double(h), 1.0)
        } else {
          // user gives a list with harmonic number and amplitude fraction
          (to_double(cadr(h)), to_double(caddr(h)))
        }
        s = s + rampl * @math.sin(harm * xx)
      }
      aset(samp, [k], Flo(to_double(num_mul(ampl, Flo(s))))) |> ignore
      xx = xx + d
    }
  } else if eq(op, sym("$rectangle")) {
    let param = to_double(d_float(cadr(d_args(osc))))
    let d = 1.0 / per1.to_double()
    for k in 0..<per1 {
      aset(
        samp,
        [k],
        Flo(
          to_double(
            if xx < param {
              num_neg(ampl)
            } else {
              ampl
            },
          ),
        ),
      )
      |> ignore
      xx = xx + d
    }
  } else if eq(op, sym("$triangle")) {
    let param = to_double(d_float(cadr(d_args(osc))))
    let d = 1.0 / per1.to_double()
    let a = to_double(ampl)
    for k in 0..<per1 {
      let v = if xx < param {
        2.0 * a * xx / param - a
      } else {
        2.0 * a * (xx - 1.0) * (1.0 / (param - 1.0)) - a
      }
      aset(samp, [k], Flo(v)) |> ignore
      xx = xx + d
    }
  }
  Nil
}

// Auxiliary functions

///|
/// Calculates the frequency associated to a note, according to the equal
/// tempered scale: 55 2^(oct + (note - 10)/12 - 1), where the notes are
/// 1 = DO = C, 2 = DO# = C#, ..., 10 = LA = A, 11 = LA# = A#, 12 = SI = B.
fn d_note_freq(note : Value, oct : Value) -> Value raise {
  if !integerp(oct) || num_lt(oct, Fix(1L)) || num_gt(oct, Fix(8L)) {
    merr("sound (note_freq): octave is not correct", []) |> ignore
  }
  if !stringp(note) {
    merr("sound (note_freq): note must be a string", []) |> ignore
  }
  let tone = string_upcase(share_mathml__str(note))
  let tail_length = (names : Array[String]) => {
    let mut i = 0
    while i < names.length() && names[i] != tone {
      i += 1
    }
    names.length() - i
  }
  let mut freq = 13 -
    tail_length([
      "C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B",
    ])
  if freq == 13 {
    freq = 13 -
      tail_length([
        "DO", "DO#", "RE", "RE#", "MI", "FA", "FA#", "SOL", "SOL#", "LA", "LA#",
        "SI",
      ])
  }
  if freq == 13 {
    merr("sound (note_freq): illegal note", []) |> ignore
  }
  mk(q_mtimes, [
    Fix(55L),
    mk(q_mexpt, [
      Fix(2L),
      mk(q_mplus, [
        Fix(-1L),
        mk(q_mtimes, [
          mk(q_rat, [Fix(1L), Fix(12L)]),
          mk(q_mplus, [Fix(-10L), int(freq)]),
        ]),
        oct,
      ]),
    ]),
  ])
}

// Sound objects

///|
/// (map 'list (lambda (z) (ceiling (* z rate))) (sort (map 'list #'$float
/// positions) #'<))
fn share_sound__wave_initials(sample_positions : Value) -> Value raise {
  let positions = if sample_positions is Nil {
    list1(Fix(0L))
  } else {
    sample_positions
  }
  let sorted = sort_list(mapcar(z => d_float(z), positions), (a, b) => num_lt(
    a, b,
  ))
  let rate = symval(q_d_sound_sample_rate)
  mapcar(z => ceiling1(num_mul(z, rate)), sorted)
}

///|
fn share_sound__finish_wave(samples : Value, wave_initials : Value) -> Value raise {
  apply_noise(samples) |> ignore
  apply_envelope(samples) |> ignore
  share_sound__make_a_wave(
    samples,
    get_sound_option(q_d_channel),
    cdr(get_sound_option(q_d_attenuation_coef)),
    wave_initials,
  )
}

///|
fn wave(
  fcn : Value,
  var_ : Value,
  ini : Value,
  end : Value,
  sample_positions : Value,
) -> Value raise {
  with_specials([(q_d_numer, t), (q_d__pctenumer, t)], () => {
    let nsec = num_sub(d_float(end), d_float(ini))
    let mut xx = to_double(d_float(ini))
    let rate = symval(q_d_sound_sample_rate)
    let d = to_double(num_div(Flo(1.0), rate))
    let num_samples = to_int(round1(num_mul(nsec, rate)))
    let samples = make_array([num_samples], initial=Flo(0.0))
    let wave_initials = share_sound__wave_initials(sample_positions)
    let fcn = coerce_float_fun(
      meval(list([list1(q_d_float), fcn])),
      list1(list([list1(q_mlist), var_])),
    )
    for k in 0..<num_samples {
      let funxx = funcall(fcn, [Flo(xx)])
      aset(samples, [k], Flo(to_double(funxx))) |> ignore
      xx = xx + d
    }
    share_sound__finish_wave(samples, wave_initials)
  })
}

///|
fn note(
  freq : Value,
  ampl : Value,
  dur : Value,
  sample_positions : Value,
) -> Value raise {
  with_specials([(q_d_numer, t), (q_d__pctenumer, t)], () => {
    let fdur = d_float(dur)
    let ffreq = d_float(freq)
    let rate = symval(q_d_sound_sample_rate)
    // sample size for one period
    let per1_samples = round1(num_div(rate, ffreq))
    // total samples for dur seconds
    let tot_samples = to_int(round1(num_mul(rate, fdur)))
    let samples = make_array([tot_samples], initial=Flo(0.0))
    if num_lt(num_mul(ffreq, fdur), Fix(1L)) {
      merr(
        "sound (note): frequence times duration must be greater than 1",
        [],
      )
      |> ignore
    }
    let wave_initials = share_sound__wave_initials(sample_positions)
    apply_oscillator_model(samples, per1_samples, ampl) |> ignore
    // fill the complete sample repeating the basic period
    let per1 = to_int(per1_samples)
    let mut k = 0
    let mut m = per1
    while m != tot_samples {
      aset(samples, [m], aref(samples, [k % per1])) |> ignore
      k += 1
      m += 1
    }
    share_sound__finish_wave(samples, wave_initials)
  })
}

///|
fn sample_from_list(dat : Value, pos : Value) -> Value raise {
  let tot_samples = to_int(d_length(dat))
  let samples = make_array([tot_samples], initial=Flo(0.0))
  d_fillarray(samples, d_float(dat)) |> ignore
  share_sound__finish_wave(samples, share_sound__wave_initials(pos))
}

///|
fn sample_from_array(dat : Value, pos : Value) -> Value raise {
  let tot_samples = array_dimension(dat, 0)
  // (adjust-array (make-array tot-samples :displaced-to dat) tot-samples):
  // a copy of the first TOT-SAMPLES elements of DAT
  let samples = make_array([tot_samples], initial=Flo(0.0))
  for i in 0..<tot_samples {
    aset(samples, [i], aref1(dat, i)) |> ignore
  }
  share_sound__finish_wave(samples, share_sound__wave_initials(pos))
}

///|
fn sample(data : Value, sample_positions : Value) -> Value raise {
  if d_listp(data).truthy() {
    sample_from_list(data, sample_positions)
  } else if arrayp(data) {
    sample_from_array(data, sample_positions)
  } else {
    merr("sound: unknown format for sampled data", [])
  }
}

// Play and its auxiliary functions

///|
/// Adds another wave to the complete sample.
/// guest: data array; chn: channel number; att: attenuation coefficient;
/// ini: starting point
fn add_wave(guest : Value, chn : Value, att : Value, ini : Value) -> Value raise {
  let chn_1 = to_int(chn) - 1
  let ini = to_int(ini)
  let samp = share_sound__sample_array()
  let n = array_dimension(guest, 0)
  for i in 0..<n {
    let indx = i + ini
    aset(
      samp,
      [chn_1, indx],
      num_add(aref(samp, [chn_1, indx]), num_mul(att, aref(guest, [i]))),
    )
    |> ignore
  }
  Nil
}

///|
fn sound_normalize() -> Value raise {
  let mut fa = d_float(get_sound_option(q_d_normalize))
  let mut max_abs_sample : Value = Flo(0.0)
  let samp = share_sound__sample_array()
  let num_chn = array_dimension(samp, 0)
  let num_sam = array_dimension(samp, 1)
  if !equal(fa, q_d_none) {
    if equal(fa, q_d_auto) {
      fa = Flo(32767.0)
    }
    for c in 0..<num_chn {
      for s in 0..<num_sam {
        let value = num_abs(aref(samp, [c, s]))
        if num_gt(value, max_abs_sample) {
          max_abs_sample = value
        }
      }
    }
    for c in 0..<num_chn {
      for s in 0..<num_sam {
        if num_eq(max_abs_sample, Flo(0.0)) {
          raise LispError::Condition(
            intern("division-by-zero"),
            "arithmetic error DIVISION-BY-ZERO signalled",
            Nil,
          )
        }
        aset(
          samp,
          [c, s],
          Flo(to_double(num_mul(fa, num_div(aref(samp, [c, s]), max_abs_sample)))),
        )
        |> ignore
      }
    }
  }
  Nil
}

///|
fn d_play(args : Value) -> Value raise {
  ini_sound_options() |> ignore
  sound_user_defaults() |> ignore
  let mut wave_storage : Value = Nil
  let mut total_samples = 0
  let mut num_channels = 1
  // see what we have to play
  for x in args.iter() {
    if equal(d_op(x), Str("=")) {
      // update play option
      update_sound_option(d_lhs(x), d_rhs(x)) |> ignore
    } else {
      // create sound
      let op = caar(x)
      let w = if eq(op, q_d_wave) {
        wave(
          nth(1, x),
          nth(2, x),
          nth(3, x),
          nth(4, x),
          nthcdr(5, x),
        )
      } else if eq(op, q_d_note) {
        note(nth(1, x), nth(2, x), nth(3, x), nthcdr(4, x))
      } else if eq(op, q_d_sample) {
        sample(nth(1, x), nthcdr(2, x))
      } else {
        merr("sound: sound object ~M is not recognized", [x])
      }
      wave_storage = cons(w, wave_storage)
      // adjust total number of samples
      let first = car(wave_storage)
      let latest_wave_sample = to_int(car(last(share_sound__a_wave_repeat_at(first)))) +
        array_dimension(share_sound__a_wave_sample(first), 0)
      if total_samples < latest_wave_sample {
        total_samples = latest_wave_sample
      }
      // update number of channels
      let chn = to_int(share_sound__a_wave_channel(first))
      if chn > num_channels {
        num_channels = chn
      }
    }
  }
  // now compose the complete wave
  set(
    q_d_sound_sample,
    make_array([num_channels, total_samples], initial=Flo(0.0)),
  )
  |> ignore
  for awave in wave_storage.iter() {
    let repeat_at = share_sound__a_wave_repeat_at(awave)
    for k in 0..<length(repeat_at) {
      let att = share_sound__a_wave_att_coef(awave)
      let len_1 = length(att) - 1
      add_wave(
        share_sound__a_wave_sample(awave),
        share_sound__a_wave_channel(awave),
        nth(if k < len_1 { k } else { len_1 }, att),
        nth(k, repeat_at),
      )
      |> ignore
    }
  }
  // normalize sample
  sound_normalize() |> ignore
  // save sound sample
  save_sound() |> ignore
  // draw the wave in case we want to see the waveform
  if get_sound_option(q_d_draw_wave).truthy() {
    d_draw_sound() |> ignore
  }
  // call the player in case we want to hear the sound
  d_play_sound() |> ignore
  q_d_done
}

///|
/// get $draw_wave from user defaults
fn get_draw_wave_from_user_defaults() -> Value raise {
  remove_if(
    x => !equal(q_d_draw_wave, nth(1, x)),
    symval(q_ear_user_sound_default_options),
  )
}

///|
/// get other options from user defaults
fn get_others_from_user_defaults() -> Value raise {
  remove_if(
    x => equal(q_d_draw_wave, nth(1, x)),
    symval(q_ear_user_sound_default_options),
  )
}

///|
/// play & draw_sound for wxMaxima
fn d_wxplay(args : Value) -> Value raise {
  if nth(2, nth(0, get_draw_wave_from_user_defaults())).truthy() {
    set(
      q_ear_user_sound_default_options,
      append(
        list1(list([list([q_mequal, q_simp]), q_d_draw_wave, Nil])),
        get_others_from_user_defaults(),
      ),
    )
    |> ignore
    d_play(args) |> ignore
    set(
      q_ear_user_sound_default_options,
      append(
        list1(list([list([q_mequal, q_simp]), q_d_draw_wave, t])),
        get_others_from_user_defaults(),
      ),
    )
    |> ignore
  } else {
    d_play(args) |> ignore
  }
  // always draw the waveform
  d_wxdraw_sound()
}
