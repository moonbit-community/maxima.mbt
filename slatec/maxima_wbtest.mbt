// Checks against the reference Maxima 5.50.0 (SBCL 2.6.9) installed on the
// development machine.  Each expected string is what
//   maxima --very-quiet --batch-string='display2d:false$ <expr>;'
// printed; the MoonBit side makes the same SLATEC call Maxima's Lisp glue
// makes (src/bessel.lisp, src/airy.lisp, src/gamma.lisp, src/specfn.lisp,
// src/csimp2.lisp, src/expintegral.lisp, numerical/slatec/quadpack.lisp).

///|
fn quad_list(r : (Double, Double, Int, Int, Int)) -> String {
  let (result, abserr, neval, ier, _last) = r
  "[\{result},\{abserr},\{neval},\{ier}]"
}

///|
test "maxima: real Bessel functions" {
  // bessel_j(0,1.5), bessel_j(1,2.5)
  assert_eq(dbesj0(1.5).to_string(), "0.511827671735918")
  assert_eq(dbesj1(2.5).to_string(), "0.497094102464274")
  // bessel_j(2.3,4.0): (floor 2.3) = 2, alpha = 0.3 (as SBCL's FLOOR computes it)
  let y : FixedArray[Double] = FixedArray::make(3, 0.0)
  let alpha = 2.3 - 2.0
  let _ = dbesj(4.0, alpha, 3, y, 0)
  assert_eq(y[2].to_string(), "0.4221958969679884")
  assert_eq(dbesy0(1.5).to_string(), "0.38244892379775886")
  assert_eq(dbesy1(2.5).to_string(), "0.14591813796678582")
  dbesy(4.0, alpha, 3, y)
  assert_eq(y[2].to_string(), "0.09698935989757604")
  assert_eq(dbesi0(1.5).to_string(), "1.646723189772891")
  assert_eq(dbesi1(2.5).to_string(), "2.5167162452886984")
  let _ = dbesi(4.0, alpha, 1, 3, y, 0)
  assert_eq(y[2].to_string(), "5.400774123600524")
  assert_eq(dbesk0(1.5).to_string(), "0.2138055626475257")
  assert_eq(dbesk1(2.5).to_string(), "0.07389081634774707")
  let _ = dbesk(4.0, alpha, 1, 3, y, 0)
  assert_eq(y[2].to_string(), "0.0200363707046902")
  // scaled_bessel_i0(1.5), scaled_bessel_i1(2.5), scaled_bessel_i(2.3,4.0)
  assert_eq(dbsi0e(1.5).to_string(), "0.36743360905415834")
  assert_eq(dbsi1e(2.5).to_string(), "0.20658464953126657")
  let _ = dbesi(4.0, alpha, 2, 3, y, 0)
  assert_eq(y[2].to_string(), "0.09891862856748702")
}

///|
test "maxima: complex Bessel and Hankel functions" {
  let cyr : FixedArray[Double] = FixedArray::make(2, 0.0)
  let cyi : FixedArray[Double] = FixedArray::make(2, 0.0)
  // bessel_j(1.5,2.0+%i) => 0.17208064589464422*%i+0.6467524361178919
  let (nz, ierr) = zbesj(2.0, 1.0, 0.5, 1, 2, cyr, cyi, 0, 0)
  assert_eq((nz, ierr), (0, 0))
  assert_eq(cyr[1].to_string(), "0.6467524361178919")
  assert_eq(cyi[1].to_string(), "0.17208064589464422")
  // bessel_y(0.5,2.0+%i) => 0.4762103386692482*%i+0.46447163413219067
  let wr : FixedArray[Double] = FixedArray::make(1, 0.0)
  let wi : FixedArray[Double] = FixedArray::make(1, 0.0)
  let _ = zbesy(2.0, 1.0, 0.5, 1, 1, cyr, cyi, 0, wr, wi, 0)
  assert_eq(cyr[0].to_string(), "0.46447163413219067")
  assert_eq(cyi[0].to_string(), "0.4762103386692482")
  // bessel_i(1.5,2.0+%i) => 1.0553049312656906*%i+0.5866920484027932
  let _ = zbesi(2.0, 1.0, 0.5, 1, 2, cyr, cyi, 0, 0)
  assert_eq(cyr[1].to_string(), "0.5866920484027932")
  assert_eq(cyi[1].to_string(), "1.0553049312656906")
  // bessel_k(0.5,2.0+%i) => 0.03771759290947044-0.10697560550198204*%i
  let _ = zbesk(2.0, 1.0, 0.5, 1, 1, cyr, cyi, 0, 0)
  assert_eq(cyr[0].to_string(), "0.03771759290947044")
  assert_eq(cyi[0].to_string(), "-0.10697560550198204")
  // hankel_1(0.5,2.0) => 0.23478571040624843*%i+0.5130161365618275
  let _ = zbesh(2.0, 0.0, 0.5, 1, 1, 1, cyr, cyi, 0, 0)
  assert_eq(cyr[0].to_string(), "0.5130161365618275")
  assert_eq(cyi[0].to_string(), "0.23478571040624843")
  // hankel_2(1.5,3.0+%i) => 1.090424258452697-0.38699131067249254*%i
  let _ = zbesh(3.0, 1.0, 0.5, 1, 2, 2, cyr, cyi, 0, 0)
  assert_eq(cyr[1].to_string(), "1.090424258452697")
  assert_eq(cyi[1].to_string(), "-0.38699131067249254")
}

///|
test "maxima: Bessel functions of large order" {
  // Maxima passes the fractional part of the order and asks for
  // floor(order) + 1 members of the sequence.
  // bessel_k(90.5,3.0+2.0*%i) => -(8.410794624773775e112*%i)-5.234265763668377e113
  let cyr : FixedArray[Double] = FixedArray::make(91, 0.0)
  let cyi : FixedArray[Double] = FixedArray::make(91, 0.0)
  let _ = zbesk(3.0, 2.0, 0.5, 1, 91, cyr, cyi, 0, 0)
  assert_eq(cyr[90].to_string(), "-5.234265763668377e+113")
  assert_eq(cyi[90].to_string(), "-8.410794624773775e+112")
  // bessel_j(30.25,7.0+3.0*%i) => 3.3884277117588375e-16-2.6176802046289877e-16*%i
  let _ = zbesj(7.0, 3.0, 0.25, 1, 31, cyr, cyi, 0, 0)
  assert_eq(cyr[30].to_string(), "3.3884277117588375e-16")
  assert_eq(cyi[30].to_string(), "-2.6176802046289877e-16")
  // bessel_y(12.5,30.0) => -0.0522244589312304
  let _ = dbesy(30.0, 0.5, 13, cyr)
  assert_eq(cyr[12].to_string(), "-0.0522244589312304")
  // bessel_i(75.5,35.0) => 1.6276276659901609e-15
  let _ = dbesi(35.0, 0.5, 1, 76, cyr, 0)
  assert_eq(cyr[75].to_string(), "1.6276276659901609e-15")
}

///|
test "maxima: Airy functions" {
  assert_eq(dai(1.5).to_string(), "0.07174949700810543")
  assert_eq(dbi(1.5).to_string(), "1.878941503747895")
  // airy_dai(1.5), airy_dbi(1.5): rz = sqrt(|z|), c = 2/3*|z|^(3/2)
  let z = 1.5
  let rz = z.abs().sqrt()
  let c = 2.0 / 3.0 * f_pow(z.abs(), 1.5)
  let (_, dai_val) = djairy(z, rz, c, 0.0, 0.0)
  assert_eq(dai_val.to_string(), "-0.09738201284230132")
  let (_, _, _, dbi_val) = dyairy(z, rz, c, 0.0, 0.0)
  assert_eq(dbi_val.to_string(), "1.8862122548481688")
  // airy_ai(1.0+%i) => 0.06045830837183806-0.15188956587718158*%i
  let (air, aii, nz, ierr) = zairy(1.0, 1.0, 0, 1, 0.0, 0.0, 0, 0)
  assert_eq((nz, ierr), (0, 0))
  assert_eq(air.to_string(), "0.06045830837183806")
  assert_eq(aii.to_string(), "-0.15188956587718158")
  // airy_bi(1.0+%i) => 0.6198892904008446*%i+0.7166580733827683
  let (bir, bii, ierr) = zbiry(1.0, 1.0, 0, 1, 0.0, 0.0, 0)
  assert_eq(ierr, 0)
  assert_eq(bir.to_string(), "0.7166580733827683")
  assert_eq(bii.to_string(), "0.6198892904008446")
  // airy_dai(-2.0+0.5*%i) => 0.7458883289066514-0.27431948858168664*%i
  let (air, aii, _, _) = zairy(-2.0, 0.5, 1, 1, 0.0, 0.0, 0, 0)
  assert_eq(air.to_string(), "0.7458883289066514")
  assert_eq(aii.to_string(), "-0.27431948858168664")
  // airy_dbi(0.5*%i+3.0) => 17.68240465792401*%i+13.505674734330569
  let (bir, bii, _) = zbiry(3.0, 0.5, 1, 1, 0.0, 0.0, 0)
  assert_eq(bir.to_string(), "13.505674734330569")
  assert_eq(bii.to_string(), "17.68240465792401")
  // airy_ai(100.0) => 0.0: Maxima 5.50.0 calls dai, which underflows and
  // reports "X SO BIG AI UNDERFLOWS" through XERMSG
  assert_eq(dai(100.0).to_string(), "0")
  assert_eq(daie(100.0).to_string(), "0.08919692093633041")
}

///|
test "maxima: erf, expint, li[2], gamma" {
  assert_eq(derf(0.3).to_string(), "0.3286267594591274")
  // expint(1.5)
  assert_eq(de1(1.5).to_string(), "0.10001958240663265")
  // li[2](0.5)
  assert_eq(dspenc(0.5).to_string(), "0.5822405264650125")
  // gamma(4.5) (GAMMAFLOAT, 0 < a < 10)
  assert_eq(dgamma(4.5).to_string(), "11.63172839656745")
  // gamma(12.5) (GAMMAFLOAT, a >= 10):
  //   c = sqrt(2*pi)*exp(d9lgmc(a)); v = a^(0.5*a - 0.25); v*(v/exp(a))*c
  let a = 12.5
  let pi = 3.141592653589793
  let c = (2.0 * pi).sqrt() * f_exp(d9lgmc(a))
  let v = f_pow(a, 0.5 * a - 0.25)
  assert_eq((v * (v / f_exp(a)) * c).to_string(), "136843365.46556586")
}

///|
test "maxima: QUADPACK" {
  let limit = 200
  let lenw = 4 * limit
  let work : FixedArray[Double] = FixedArray::make(lenw, 0.0)
  let iwork : FixedArray[Int] = FixedArray::make(limit, 0)
  let qags = fn(f : (Double) -> Double raise, a : Double, b : Double, limit : Int) raise {
    dqags(f, a, b, 0.0, 1.0e-8, 0.0, 0.0, 0, 0, limit, 4 * limit, 0, iwork, work)
  }
  // quad_qags(x^2,x,0,1)
  assert_eq(
    quad_list(qags(x => x * x, 0.0, 1.0, limit)),
    "[0.33333333333333337,3.70074341541719e-15,21,0]",
  )
  // quad_qags(1/sqrt(x),x,0,1): Maxima's compiled integrand computes
  // x^(-1/2) as 1/sqrt(x)
  assert_eq(
    quad_list(qags(x => 1.0 / x.sqrt(), 0.0, 1.0, limit)),
    "[1.9999999999999984,5.773159728050814e-15,231,0]",
  )
  // quad_qags(sin(1/x),x,0,1,limit=3) => ier = 1 (prints an XERMSG report)
  assert_eq(
    quad_list(qags(x => f_sin(f_pow(x, -1.0)), 0.0, 1.0, 3)),
    "[0.49883001303732516,0.16191087259256032,105,1]",
  )
  // quad_qag(exp(-x^2),x,-3,2,3)
  assert_eq(
    quad_list(
      dqag(
        x => f_exp(-1.0 * f_pow(x, 2.0)),
        -3.0,
        2.0,
        0.0,
        1.0e-8,
        3,
        0.0,
        0.0,
        0,
        0,
        limit,
        lenw,
        0,
        iwork,
        work,
      ),
    ),
    "[1.7682887390219428,7.545931804907519e-12,31,0]",
  )
  // quad_qagi(exp(-x),x,0,inf)
  assert_eq(
    quad_list(
      dqagi(
        x => f_exp(-1.0 * x),
        0.0,
        1,
        0.0,
        1.0e-8,
        0.0,
        0.0,
        0,
        0,
        limit,
        lenw,
        0,
        iwork,
        work,
      ),
    ),
    "[1.0000000000000002,5.842606742906004e-11,135,0]",
  )
  // quad_qagi(1/(1+x^2),x,minf,inf)
  assert_eq(
    quad_list(
      dqagi(
        x => f_pow(f_pow(x, 2.0) + 1.0, -1.0),
        0.0,
        2,
        0.0,
        1.0e-8,
        0.0,
        0.0,
        0,
        0,
        limit,
        lenw,
        0,
        iwork,
        work,
      ),
    ),
    "[3.141592653589793,5.155583041103855e-10,90,0]",
  )
  // quad_qawc(1/(1+x^2),x,0.0,-1,5)
  let (result, abserr, neval, ier, _) = {
    let (_, r, e, n, i, l) = dqawc(
      x => f_pow(f_pow(x, 2.0) + 1.0, -1.0),
      -1.0,
      5.0,
      0.0,
      0.0,
      1.0e-8,
      0.0,
      0.0,
      0,
      0,
      limit,
      lenw,
      0,
      iwork,
      work,
    )
    (r, e, n, i, l)
  }
  assert_eq(
    quad_list((result, abserr, neval, ier, 0)),
    "[0.3269632337033319,1.3078627722802811e-11,265,0]",
  )
  // quad_qaws(1,x,0,1,-0.5,-0.5,1)
  let (_, _, _, _, _, r, e, n, i, _) = dqaws(
    _x => 1.0,
    0.0,
    1.0,
    -0.5,
    -0.5,
    1,
    0.0,
    1.0e-8,
    0.0,
    0.0,
    0,
    0,
    limit,
    lenw,
    0,
    iwork,
    work,
  )
  assert_eq(
    quad_list((r, e, n, i, 0)),
    "[3.141592653589794,1.0125233984581428e-13,50,0]",
  )
}

///|
test "maxima: QUADPACK oscillatory and singular points" {
  // quad_qawf(exp(-x),x,0,1,cos): limit 200, maxp1 100, limlst 10
  let leniw = 200
  let maxp1 = 100
  let lenw = 2 * leniw + 25 * maxp1
  let work : FixedArray[Double] = FixedArray::make(lenw, 0.0)
  let iwork : FixedArray[Int] = FixedArray::make(leniw, 0)
  let (_, r, e, n, i, _) = dqawf(
    x => f_exp(-1.0 * x),
    0.0,
    1.0,
    1,
    1.0e-10,
    0.0,
    0.0,
    0,
    0,
    10,
    0,
    leniw,
    maxp1,
    lenw,
    iwork,
    work,
  )
  assert_eq(
    quad_list((r, e, n, i, 0)),
    "[0.49999999999999967,2.19026633171533e-12,200,0]",
  )
  // quad_qawo(exp(-x),x,0,2,10,cos)
  let (_, r, e, n, i, _) = dqawo(
    x => f_exp(-1.0 * x),
    0.0,
    2.0,
    10.0,
    1,
    0.0,
    1.0e-8,
    0.0,
    0.0,
    0,
    0,
    leniw,
    maxp1,
    lenw,
    0,
    iwork,
    work,
  )
  assert_eq(
    quad_list((r, e, n, i, 0)),
    "[0.02158721920245689,4.559569483733909e-15,25,0]",
  )
  // quad_qagp(log(abs(x-0.3)),x,0,1,[0.3]): npts2 = 3,
  // leniw = max(limit, 3*npts2-2), lenw = 2*leniw - npts2
  let limit = 200
  let npts2 = 3
  let leniw = if limit > 3 * npts2 - 2 { limit } else { 3 * npts2 - 2 }
  let lenw = 2 * leniw - npts2
  let p : FixedArray[Double] = [0.3, 0.0, 0.0]
  let work : FixedArray[Double] = FixedArray::make(lenw, 0.0)
  let iwork : FixedArray[Int] = FixedArray::make(leniw, 0)
  assert_eq(
    quad_list(
      dqagp(
        x => f_log((x + -0.3).abs()),
        0.0,
        1.0,
        npts2,
        p,
        0.0,
        1.0e-8,
        0.0,
        0.0,
        0,
        0,
        leniw,
        lenw,
        0,
        iwork,
        work,
      ),
    ),
    "[-1.610864302054893,1.7884186376880753e-15,462,0]",
  )
}

///|
suberror IntegrandFailed

///|
test "QUADPACK propagates errors raised by the integrand" {
  let work : FixedArray[Double] = FixedArray::make(800, 0.0)
  let iwork : FixedArray[Int] = FixedArray::make(200, 0)
  let mut calls = 0
  let f = fn(x : Double) -> Double raise {
    calls += 1
    if calls > 30 {
      raise IntegrandFailed
    }
    f_pow(x, -0.5)
  }
  let raised = try {
    let _ = dqags(f, 0.0, 1.0, 0.0, 1.0e-8, 0.0, 0.0, 0, 0, 200, 800, 0, iwork, work)
    false
  } catch {
    IntegrandFailed => true
    _ => false
  }
  assert_true(raised)
  assert_eq(calls, 31)
}

///|
test "j4save controls XERMSG" {
  // quad_control(control) / max_message defaults
  assert_eq(j4save(2, 0, false), 2)
  assert_eq(j4save(4, 0, false), 10)
}
