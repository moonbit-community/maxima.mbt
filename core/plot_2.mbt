// Port of src/plot.lisp (part 2): computing the points of 2d plots
// (implicit, parametric, discrete and explicit functions, with adaptive
// sampling), temporary files and the plot options parser.

///|
/// Implicit expressions of two variables, for instance, x and y, where expr
/// is of the form f(x,y) = g(x,y).  The result is a series of separated
/// line segments.
fn draw2d_implicit(expr : Value, options : Value) -> Value raise {
  let xmin = first(getf(options, q_d_x))
  let ymin = first(getf(options, q_d_y))
  let xmax = second(getf(options, q_d_x))
  let ymax = second(getf(options, q_d_y))
  let gridx = {
    let g = first(getf(options, q_d_sample))
    if g.truthy() { g } else { Fix(47L) }
  }
  let gridy = {
    let g = second(getf(options, q_d_sample))
    if g.truthy() { g } else { Fix(47L) }
  }
  let eps = {
    let e = getf(options, q_d_plotepsilon)
    if e.truthy() { e } else { Flo(1.0e-6) }
  }
  let ngx = to_int(gridx)
  let ngy = to_int(gridy)
  let f : Array[Array[Value]] = Array::makei(ngx + 1, _ => Array::make(
    ngy + 1,
    Nil,
  ))
  let dx = num_div(num_sub(xmax, xmin), gridx)
  let dy = num_div(num_sub(ymax, ymin), gridy)
  let vx = getf(options, q_d_xvar)
  let vy = getf(options, q_d_yvar)
  let fun0 = if getf(options, q_d_contour).truthy() {
    expr
  } else {
    sub_star(d_lhs(expr), d_rhs(expr))
  }
  let fun = coerce_float_fun(
    fun0,
    list2(list3(list1(q_mlist), vx, vy), Str("plot2d")),
  )
  let mut fmin : Value = Nil
  let mut fmax : Value = Nil
  // sets up array f with values of the function at corners of sample grid.
  // finds maximum and minimum values in that array.
  for i in 0..=ngx {
    for j in 0..=ngy {
      let faux = funcall(fun, [
        num_add(xmin, num_mul(int(i), dx)),
        num_add(ymin, num_mul(int(j), dy)),
      ])
      f[i][j] = faux
      if numberp(faux) && i > 0 && j > 0 && i < ngx && j < ngy {
        if numberp(fmin) {
          if numberp(fmax) {
            if num_lt(faux, fmin) {
              fmin = faux
            }
            if num_gt(faux, fmax) {
              fmax = faux
            }
          } else if num_lt(faux, fmin) {
            fmax = fmin
            fmin = faux
          } else {
            fmax = faux
          }
        } else if numberp(fmax) {
          if num_gt(faux, fmax) {
            fmin = fmax
            fmax = faux
          } else {
            fmin = faux
          }
        } else {
          fmin = faux
        }
      }
    }
  }
  // checks that the function has a minimum and a maximum
  if !numberp(fmin) || !numberp(fmax) || !num_gt(fmax, fmin) {
    merr("plot2d: nothing to plot for ~M.~%", [expr]) |> ignore
  }
  // sets up the levels for contour plots
  let levels = if getf(options, q_d_contour).truthy() {
    let lv = getf(options, q_d_levels)
    if lv.truthy() {
      if !listp(lv) {
        getlevels(fmin, fmax, lv)
      } else {
        lv
      }
    } else {
      getlevels(fmin, fmax, Fix(8L))
    }
  } else {
    list1(Flo(0.0))
  }
  //
  // Algorithm for implicit functions, by Jaime Villate. 2021
  //
  // The points at each rectangle in the sample grid are labeled as follows:
  //
  // ij+ ______ i+j+
  //     |    |
  //     |    |    function fun has the following values at those points:
  //     |    |
  //  ij |____| i+j     fij, fi+j, fij+, fi+j+
  //
  let mut result : Value = Nil
  let mut results : Value = Nil
  let mut values : Value = Nil
  let level = () => symval(q_level)
  let ffun = (x : Value, y : Value) => num_sub(funcall(fun, [x, y]), level())
  // (dotimes (n 2 (if (< ... 1.5) (list xp yp) nil)) ...)
  let accept = (fi : Value, fi1 : Value, fp : Value, xp : Value, yp : Value) => if num_lt(
      num_div(
        num_add(num_abs(num_sub(fi, fp)), num_abs(num_sub(fi1, fp))),
        num_abs(num_sub(fi, fi1)),
      ),
      Flo(1.5),
    ) {
    list2(xp, yp)
  } else {
    Nil
  }
  // interp+ and interp- (SIGN 1 or -1): along the diagonals
  let interp_diag = fn(
    sign : Int,
    i : Int,
    j : Int,
    fi : Value,
    fi1 : Value,
  ) -> Value raise {
    if !minusp(num_mul(fi, fi1)) {
      return Nil
    }
    let mut f1 = fi
    let mut f2 = fi1
    let mut x1 = num_add(xmin, num_mul(dx, int(i)))
    let mut x2 = num_add(x1, dx)
    let mut y1 = num_add(ymin, num_mul(dy, int(j)))
    let mut y2 = if sign > 0 { num_add(y1, dy) } else { num_sub(y1, dy) }
    let mut xp : Value = Nil
    let mut yp : Value = Nil
    let mut fp : Value = Nil
    for _ in 0..<2 {
      xp = num_div(num_add(x1, x2), Flo(2.0))
      yp = num_div(num_add(y1, y2), Flo(2.0))
      fp = ffun(xp, yp)
      if !numberp(fp) {
        return Nil
      }
      if plusp(num_mul(f1, fp)) {
        x1 = xp
        y1 = yp
        f1 = fp
      } else {
        x2 = xp
        y2 = yp
        f2 = fp
      }
      xp = num_div(
        num_sub(num_mul(f1, x2), num_mul(f2, x1)),
        num_sub(f1, f2),
      )
      yp = num_div(
        num_sub(num_mul(f1, y2), num_mul(f2, y1)),
        num_sub(f1, f2),
      )
      fp = ffun(xp, yp)
      if !numberp(fp) {
        return Nil
      }
      if plusp(num_mul(f1, fp)) {
        x1 = xp
        y1 = yp
        f1 = fp
      } else {
        x2 = xp
        y2 = yp
        f2 = fp
      }
    }
    accept(fi, fi1, fp, xp, yp)
  }
  let interp_p = (i : Int, j : Int, fi : Value, fi1 : Value) => interp_diag(
    1,
    i,
    j,
    fi,
    fi1,
  )
  let interp_m = (i : Int, j : Int, fi : Value, fi1 : Value) => interp_diag(
    -1,
    i,
    j,
    fi,
    fi1,
  )
  let interpx = fn(i : Int, j : Int, fi : Value, fi1 : Value) -> Value raise {
    if !minusp(num_mul(fi, fi1)) {
      return Nil
    }
    let mut f1 = fi
    let mut f2 = fi1
    let mut x1 = num_add(xmin, num_mul(dx, int(i)))
    let mut x2 = num_add(x1, dx)
    let yp = num_add(ymin, num_mul(dy, int(j)))
    let mut xp : Value = Nil
    let mut fp : Value = Nil
    for _ in 0..<2 {
      xp = num_div(num_add(x1, x2), Flo(2.0))
      fp = ffun(xp, yp)
      if !numberp(fp) {
        return Nil
      }
      if plusp(num_mul(f1, fp)) {
        x1 = xp
        f1 = fp
      } else {
        x2 = xp
        f2 = fp
      }
      xp = num_div(
        num_sub(num_mul(f1, x2), num_mul(f2, x1)),
        num_sub(f1, f2),
      )
      fp = ffun(xp, yp)
      if !numberp(fp) {
        return Nil
      }
      if plusp(num_mul(f1, fp)) {
        x1 = xp
        f1 = fp
      } else {
        x2 = xp
        f2 = fp
      }
    }
    accept(fi, fi1, fp, xp, yp)
  }
  let interpy = fn(i : Int, j : Int, fj : Value, fj1 : Value) -> Value raise {
    if !minusp(num_mul(fj, fj1)) {
      return Nil
    }
    let mut f1 = fj
    let mut f2 = fj1
    let xp = num_add(xmin, num_mul(dx, int(i)))
    let mut y1 = num_add(ymin, num_mul(dy, int(j)))
    let mut y2 = num_add(y1, dy)
    let mut yp : Value = Nil
    let mut fp : Value = Nil
    for _ in 0..<2 {
      yp = num_div(num_add(y1, y2), Flo(2.0))
      fp = ffun(xp, yp)
      if !numberp(fp) {
        return Nil
      }
      if plusp(num_mul(f1, fp)) {
        y1 = yp
        f1 = fp
      } else {
        y2 = yp
        f2 = fp
      }
      yp = num_div(
        num_sub(num_mul(f1, y2), num_mul(f2, y1)),
        num_sub(f1, f2),
      )
      fp = ffun(xp, yp)
      if !numberp(fp) {
        return Nil
      }
      if plusp(num_mul(f1, fp)) {
        y1 = yp
        f1 = fp
      } else {
        y2 = yp
        f2 = fp
      }
    }
    accept(fj, fj1, fp, xp, yp)
  }
  let coords = (i : Int, j : Int) => list2(
    num_add(xmin, num_mul(int(i), dx)),
    num_add(ymin, num_mul(int(j), dy)),
  )
  let draw_line = (p1 : Value, p2 : Value) => {
    result = cons(first(p1), result)
    result = cons(second(p1), result)
    result = cons(first(p2), result)
    result = cons(second(p2), result)
    result = cons(q_moveto, result)
    result = cons(q_moveto, result)
  }
  let draw_lines = (p1 : Value, p2 : Value, p3 : Value) => {
    result = cons(first(p1), result)
    result = cons(second(p1), result)
    result = cons(first(p2), result)
    result = cons(second(p2), result)
    result = cons(first(p3), result)
    result = cons(second(p3), result)
    result = cons(q_moveto, result)
    result = cons(q_moveto, result)
  }
  let small = (v : Value) => num_lt(num_abs(v), eps)
  let shifted = (v : Value) => if numberp(v) { num_sub(v, level()) } else { v }
  for lv in reverse(levels).iter() {
    with_special(q_level, lv, () => {
      for i in 0..<ngx {
        for j in 0..<ngy {
          let fij = shifted(f[i][j])
          let fij_ = shifted(f[i][j + 1])
          let fi_j = shifted(f[i + 1][j])
          let fi_j_ = shifted(f[i + 1][j + 1])
          let mut next = true
          let mut p1 : Value = Nil
          let mut p2 : Value = Nil
          let mut p3 : Value = Nil
          let mut p4 : Value = Nil
          // 1. undefined at ij
          if !numberp(fij) {
            next = false
            // if undefined also at i+j or ij+, continue to next rectangle
            if numberp(fi_j) && numberp(fij_) {
              if small(fi_j) {
                if small(fij_) {
                  // real and 0 at i+j and ij+
                  draw_line(coords(i + 1, j), coords(i, j + 1))
                } else if numberp(fi_j_) &&
                  {
                    p2 = interpx(i, j + 1, fij_, fi_j_)
                    p2.truthy()
                  } {
                  // real at i+j, ij+ and i+j+, 0 at i+j and segment ij+ i+j+
                  draw_line(coords(i + 1, j), p2)
                }
              } else if numberp(fi_j_) {
                if small(fij_) {
                  p2 = interpy(i + 1, j, fi_j, fi_j_)
                  if p2.truthy() {
                    // real at i+j, and i+j+, 0 at ij+ and segment i+j i+j+
                    draw_line(coords(i, j + 1), p2)
                  }
                } else if {
                    p1 = interpx(i, j + 1, fij_, fi_j_)
                    p1.truthy()
                  } &&
                  {
                    p2 = interpy(i + 1, j, fi_j, fi_j_)
                    p2.truthy()
                  } {
                  // real at i+j, ij+ and i+j+, 0 at segments ij+ i+j+ and
                  // i+j i+j+
                  draw_line(p1, p2)
                }
              }
            }
          }
          // 2. real at ij and undefined at i+j
          if next && !numberp(fi_j) {
            next = false
            // if undefined at ij+, continue to next rectangle
            if numberp(fij_) {
              if small(fij) {
                if small(fij_) {
                  // zero at ij and ij+
                  draw_line(coords(i, j), coords(i, j + 1))
                } else if numberp(fi_j_) &&
                  {
                    p2 = interpx(i, j + 1, fij_, fi_j_)
                    p2.truthy()
                  } {
                  // real at ij+ and i+j+, 0 at ij and segment ij+ i+j+
                  draw_line(coords(i, j), p2)
                }
              } else if numberp(fi_j_) &&
                {
                  p1 = interpy(i, j, fij, fij_)
                  p1.truthy()
                } &&
                {
                  p2 = interpx(i, j + 1, fij_, fi_j_)
                  p2.truthy()
                } {
                // real at ij, ij+ and i+j+, 0 at segments ij ij+ and ij+ i+j+
                draw_line(p1, p2)
              }
            }
          }
          // 3. real at fi+j and 0 at ij
          if next && small(fij) {
            next = false
            if numberp(fij_) {
              if small(fij_) {
                // real at i+j, 0 at ij and ij+
                draw_line(coords(i, j), coords(i, j + 1))
              } else {
                p1 = interp_m(i, j + 1, fij_, fi_j)
                if p1.truthy() && numberp(fi_j_) {
                  if small(fi_j_) {
                    // real at i+j and ij, 0 at ij, i+j+ and diagonal ij+ i+j
                    draw_lines(coords(i, j), p1, coords(i + 1, j + 1))
                  } else {
                    // real at i+j, ij+ and i+j+, 0 at ij, diagonal ij+ i+j
                    // and segment ij+ i+j+
                    p2 = interpx(i, j + 1, fij_, fi_j_)
                    if p2.truthy() {
                      draw_lines(coords(i, j), p1, p2)
                    }
                    // real at i+j, ij+ and i+j+, 0 at ij, diagonal ij+ i+j
                    // and segment i+j i+j+
                    p2 = interpy(i + 1, j, fi_j, fi_j_)
                    if p2.truthy() {
                      draw_lines(coords(i, j), p1, p2)
                    }
                  }
                }
              }
            } else if numberp(fi_j_) {
              if small(fi_j) {
                // undefined at ij+, real at fi+j+, 0 at ij and i+j
                draw_line(coords(i, j), coords(i + 1, j))
              } else {
                p2 = interpy(i + 1, j, fi_j, fi_j_)
                if p2.truthy() {
                  // undefined at ij+, real at fi+j and fi+j+, 0 at ij and
                  // segment i+j i+j+
                  draw_line(coords(i, j), p2)
                }
              }
            } else if small(fi_j) {
              // undefined at ij+ and i+j+, 0 at ij and i+j
              draw_line(coords(i, j), coords(i + 1, j))
            }
          }
          // 4. real at ij and 0 at i+j
          if next && small(fi_j) {
            next = false
            if numberp(fij_) {
              if numberp(fi_j_) {
                // if 0 at i+j but undefined at ij+ or there's no zero in
                // diagonal ij i+j+, continue to next rectangle
                p1 = interp_p(i, j, fij, fi_j_)
                if p1.truthy() {
                  if small(fij_) {
                    // 0 at i+j, ij+ and diagonal ij i+j+
                    draw_lines(coords(i + 1, j), p1, coords(i, j + 1))
                  } else {
                    p2 = interpy(i, j, fij, fij_)
                    if p2.truthy() {
                      // 0 at i+j, diagonal ij i+j+ and segment ij ij+
                      draw_lines(coords(i + 1, j), p1, p2)
                    }
                    p2 = interpx(i, j + 1, fij_, fi_j_)
                    if p2.truthy() {
                      // 0 at i+j, diagonal ij i+j+ and segment ij+ i+j+
                      draw_lines(coords(i + 1, j), p1, p2)
                    }
                  }
                }
              } else {
                p2 = interpy(i, j, fij, fij_)
                if p2.truthy() {
                  // undefined at i+j+, 0 at i+j and segment ij ij+
                  draw_line(coords(i + 1, j), p2)
                }
              }
            }
          }
          // 5. real at ij and i+j but undefined at ij+
          if next && !numberp(fij_) {
            next = false
            if numberp(fi_j_) &&
              {
                p1 = interpx(i, j, fij, fi_j)
                p1.truthy()
              } &&
              {
                p2 = interpy(i + 1, j, fi_j, fi_j_)
                p2.truthy()
              } {
              // 0 at segments ij i+j and i+j i+j+
              draw_line(p1, p2)
            }
          }
          // 6. real at ij, i+j and ij+, but undefined at i+j+
          if next && !numberp(fi_j_) {
            next = false
            if {
                p1 = interpy(i, j, fij, fij_)
                p1.truthy()
              } &&
              {
                p2 = interpx(i, j, fij, fi_j)
                p2.truthy()
              } {
              // 0 at segments ij ij+ and ij i+j
              draw_line(p1, p2)
            }
          }
          // 7. real at the four corners and 0 at ij+
          if next && small(fij_) {
            next = false
            p1 = interp_p(i, j, fij, fi_j_)
            if p1.truthy() {
              p2 = interpx(i, j, fij, fi_j)
              if p2.truthy() {
                // 0 at diagonal ij i+j+ and segment ij i+j
                draw_lines(p2, p1, coords(i, j + 1))
              }
              p2 = interpy(i + 1, j, fi_j, fi_j_)
              if p2.truthy() {
                // 0 at diagonal ij i+j+ and segment i+j i+j+
                draw_lines(p2, p1, coords(i, j + 1))
              }
            }
          }
          // 8. real at the four corners and 0 at i+j+
          if next && small(fi_j_) {
            next = false
            p1 = interp_m(i, j + 1, fij_, fi_j)
            if p1.truthy() {
              p2 = interpx(i, j, fij, fi_j)
              if p2.truthy() {
                // 0 at diagonal ij+ i+j and segment ij i+j
                draw_lines(p2, p1, coords(i + 1, j + 1))
              }
              p2 = interpy(i, j, fij, fij_)
              if p2.truthy() {
                // 0 at diagonal ij+ i+j and segment ij ij+
                draw_lines(p2, p1, coords(i + 1, j + 1))
              }
            }
          }
          // 9. real at the four corners and 0 at segment ij i+j
          if next &&
            {
              p1 = interpx(i, j, fij, fi_j)
              p1.truthy()
            } {
            next = false
            p2 = interpy(i, j, fij, fij_)
            if p2.truthy() {
              p3 = interpx(i, j + 1, fij_, fi_j_)
              if p3.truthy() {
                p4 = interpy(i + 1, j, fi_j, fi_j_)
                if p4.truthy() {
                  // 0 at the four sides
                  draw_line(p1, p3)
                  draw_line(p2, p4)
                }
              } else {
                p3 = interp_p(i, j, fij, fi_j_)
                if p3.truthy() {
                  // 0 at segments ij i+j, ij ij+ and diagonal ij i+j+
                  draw_lines(p1, p3, p2)
                }
              }
            } else {
              p4 = interpy(i + 1, j, fi_j, fi_j_)
              if p4.truthy() {
                p2 = interp_m(i, j + 1, fij_, fi_j)
                if p2.truthy() {
                  // 0 at segments ij i+j, i+j i+j+ and diagonal ij+ i+j
                  draw_lines(p1, p2, p4)
                }
              } else if {
                  p3 = interpx(i, j + 1, fij_, fi_j_)
                  p3.truthy()
                } &&
                {
                  p2 = interp_p(i, j, fij, fi_j_)
                  p2.truthy()
                } {
                // 0 at segments ij i+j, ij+ i+j+ and diagonal ij i+j+
                draw_lines(p1, p2, p3)
              }
            }
          }
          // 10. real at the four corners, without zero in segment ij i+j
          if next {
            p2 = interpy(i, j, fij, fij_)
            if p2.truthy() {
              p3 = interpx(i, j + 1, fij_, fi_j_)
              if p3.truthy() {
                p4 = interp_m(i, j + 1, fij_, fi_j)
                if p4.truthy() {
                  // 0 at segments ij ij+ and ij+ i+j+ and diagonal ij+ i+j
                  draw_lines(p2, p4, p3)
                }
              } else if {
                  p4 = interpy(i + 1, j, fi_j, fi_j_)
                  p4.truthy()
                } &&
                {
                  p3 = interp_p(i, j, fij, fi_j_)
                  p3.truthy()
                } {
                // 0 at segments ij ij+ and i+j i+j+ and diagonal ij i+j+
                draw_lines(p2, p3, p4)
              }
            } else if {
                p3 = interpx(i, j + 1, fij_, fi_j_)
                p3.truthy()
              } &&
              {
                p4 = interpy(i + 1, j, fi_j, fi_j_)
                p4.truthy()
              } &&
              {
                p1 = interp_p(i, j, fij, fi_j_)
                p1.truthy()
              } {
              // 0 at segments ij+ i+j+ and i+j i+j+ and diagonal ij i+j+
              draw_lines(p4, p1, p3)
            }
          }
        }
      }
      if getf(options, q_d_contour).truthy() && result.truthy() {
        results = cons(cons(list1(q_mlist), reverse(result)), results)
        values = cons(lv, values)
        result = Nil
      }
    })
  }
  // When called for a single implicit expression, returns a Maxima list of
  // points. When called for contours of an expression, returns a Maxima
  // list whose first element is another Maxima list with the values of the
  // contours, followed by Maxima lists of points for each contour.
  if getf(options, q_d_contour).truthy() {
    cons(list1(q_mlist), cons(cons(list1(q_mlist), values), results))
  } else {
    cons(list1(q_mlist), reverse(result))
  }
}

///|
/// The post-processing common to DRAW2D and DRAW2D-PARAMETRIC-ADAPTIVE:
/// filter out any MOVETO's which do not precede a number (code elsewhere
/// expects MOVETO's to come in pairs, so leave two MOVETO's before a
/// number), warn about clipped or non-numeric values and return the Maxima
/// list of the remaining points.
fn plot__finish_points(
  result : Value,
  n_clipped : Int,
  n_non_numeric : Int,
) -> Value raise {
  let n = length(result)
  for i in 0..<n {
    if i % 2 == 0 &&
      eq(nth(i, result), q_moveto) &&
      eq(nth(i + 1, result), q_moveto) &&
      (i == n - 2 || eq(nth(i + 2, result), q_moveto)) {
      rplaca(nthcdr(i, result), Nil) |> ignore
      rplaca(nthcdr(i + 1, result), Nil) |> ignore
    }
  }
  let result_sans_nil = delete(Nil, result)
  if result_sans_nil is Nil {
    if n_non_numeric == 0 {
      mtell(list1(Str("plot2d: all values will be clipped.~%"))) |> ignore
    } else if n_clipped == 0 {
      mtell(
        list1(
          Str(
            "plot2d: expression evaluates to non-numeric value everywhere in plotting range.~%",
          ),
        ),
      )
      |> ignore
    } else {
      mtell(list1(Str("plot2d: all values are non-numeric, or clipped.~%")))
      |> ignore
    }
  } else {
    if n_non_numeric > 0 {
      mtell(
        list1(
          Str(
            "plot2d: expression evaluates to non-numeric value somewhere in plotting range.~%",
          ),
        ),
      )
      |> ignore
    }
    if n_clipped > 0 {
      mtell(list1(Str("plot2d: some values will be clipped.~%"))) |> ignore
    }
  }
  cons(list1(q_mlist), result_sans_nil)
}

///|
/// parametric ; [parametric,xfun,yfun,[t,tlow,thigh],[nticks ..]]
/// the rest of the parametric list after the list will add to the plot
/// options
fn draw2d_parametric_adaptive(param : Value, options : Value) -> Value raise {
  if !num_eq(d_length(param), Fix(4L)) {
    merr(
      "plot2d: parametric plots must include two expressions and an interval",
      [],
    )
    |> ignore
  }
  let range = nth(4, param)
  if !(
      d_listp(range).truthy() &&
      symbolp(second(range)) &&
      eql(d_length(range), Fix(3L))
    ) {
    merr("plot2d: wrong interval for parametric plot: ~M", [range]) |> ignore
  }
  let range = check_range(range)
  let nticks = getf(options, q_d_nticks)
  let trange = cddr(range)
  let tvar = second(range)
  let xrange = {
    let v = getf(options, q_d_x)
    if v.truthy() { v } else { getf(options, q_d_xbounds) }
  }
  let yrange = {
    let v = getf(options, q_d_y)
    if v.truthy() { v } else { getf(options, q_d_ybounds) }
  }
  let tmin = coerce_float(first(trange))
  let tmax = coerce_float(second(trange))
  let xmin = coerce_float(first(xrange))
  let xmax = coerce_float(second(xrange))
  let ymin = coerce_float(first(yrange))
  let ymax = coerce_float(second(yrange))
  plot__check_flonum(ymin, "YMIN")
  plot__check_flonum(ymax, "YMAX")
  plot__check_flonum(xmin, "XMIN")
  plot__check_flonum(xmax, "XMAX")
  plot__check_flonum(tmin, "TMIN")
  plot__check_flonum(tmax, "TMAX")
  let f1 = coerce_float_fun(
    third(param),
    list2(list2(list1(q_mlist), tvar), Str("plot2d")),
  )
  let f2 = coerce_float_fun(
    fourth(param),
    list2(list2(list1(q_mlist), tvar), Str("plot2d")),
  )
  let mut n_clipped = 0
  let mut n_non_numeric = 0
  let t_step = num_div(
    num_div(num_sub(tmax, tmin), coerce_float(nticks)),
    Fix(2L),
  )
  let mut t_samples : Value = Nil
  let mut x_samples : Value = Nil
  let mut y_samples : Value = Nil
  let mut result : Value = Nil
  // Divide the range into 2*NTICKS regions that we then adaptively plot
  // over.
  for k in 0..<(1 + 2 * to_int(nticks)) {
    let tpar = num_add(tmin, num_mul(int(k), t_step))
    t_samples = cons(tpar, t_samples)
    x_samples = cons(funcall(f1, [tpar]), x_samples)
    y_samples = cons(funcall(f2, [tpar]), y_samples)
  }
  t_samples = nreverse(t_samples)
  x_samples = nreverse(x_samples)
  y_samples = nreverse(y_samples)
  // Adaptively plot over each region
  let mut t_start = t_samples
  let mut t_mid = cdr(t_samples)
  let mut t_end = cddr(t_samples)
  let mut x_start = x_samples
  let mut x_mid = cdr(x_samples)
  let mut x_end = cddr(x_samples)
  let mut y_start = y_samples
  let mut y_mid = cdr(y_samples)
  let mut y_end = cddr(y_samples)
  while t_end.truthy() {
    let pts = adaptive_parametric_plot(
      f1,
      f2,
      car(t_start),
      car(t_mid),
      car(t_end),
      car(x_start),
      car(x_mid),
      car(x_end),
      car(y_start),
      car(y_mid),
      car(y_end),
      getf(options, q_d_adapt_depth),
      Flo(1.0e-5),
    )
    result = if result.truthy() { append(result, cddr(pts)) } else { pts }
    t_start = cddr(t_start)
    t_mid = cddr(t_mid)
    t_end = cddr(t_end)
    x_start = cddr(x_start)
    x_mid = cddr(x_mid)
    x_end = cddr(x_end)
    y_start = cddr(y_start)
    y_mid = cddr(y_mid)
    y_end = cddr(y_end)
  }
  // Fix up out-of-range values and clobber non-numeric values.
  let mut x = result
  let mut y = cdr(result)
  while y.truthy() {
    if numberp(car(x)) && numberp(car(y)) {
      // Let clipping to the graphic program. See the comment in DRAW2D.
      if !(
          num_le(ymin, car(y)) &&
          num_le(car(y), ymax) &&
          num_le(xmin, car(x)) &&
          num_le(car(x), xmax)
        ) {
        n_clipped = n_clipped + 1
      }
    } else {
      n_non_numeric = n_non_numeric + 1
      rplaca(x, q_moveto) |> ignore
      rplaca(y, q_moveto) |> ignore
    }
    x = cddr(x)
    y = cddr(y)
  }
  plot__finish_points(result, n_clipped, n_non_numeric)
}

///|
/// draw2d-discrete. Accepts [discrete,[x1,x2,...],[y1,y2,...]] or
/// [discrete,[[x1,y1]...] and returns [x1,y1,...] or nil, if none of the
/// points have real values.  Currently there are no plot options relevant
/// to draw2d-discrete.
fn draw2d_discrete(f : Value) -> Value raise {
  let x = third(f)
  let y = fourth(f)
  let mut data : Value = Nil
  if d_listp(x).truthy() {
    // x is a list
    if d_listp(cadr(x)).truthy() {
      // x1 is a list
      if length(cadr(x)) == 3 {
        // x1 is a 2D point
        data = parse_points_xy(x)
      } else {
        // x1 is not a 2D point
        merr(
          "draw2d-discrete: Expecting a point with 2 coordinates; found ~M~%",
          [cadr(x)],
        )
        |> ignore
      }
    } else if d_listp(y).truthy() {
      // x1 is not a list; y is a list
      if symbolp(coerce_float(cadr(y))) {
        // y is an option
        data = parse_points_y(x)
      } else if d_listp(cadr(y)).truthy() {
        // y1 is a list
        merr("draw2d-discrete: Expecting a y coordinate; found ~M~%", [cadr(y)])
        |> ignore
      } else if length(x) == length(y) {
        // case [x][y]
        data = parse_points_x_y(x, y)
      } else {
        merr(
          "draw2d-discrete: The number of x and y coordinates do not match.~%",
          [],
        )
        |> ignore
      }
    } else {
      // y is not a list
      data = parse_points_y(x)
    }
  } else {
    // x is not a list
    merr(
      "draw2d-discrete: Expecting a list of x coordinates or points; found ~M~%",
      [x],
    )
    |> ignore
  }
  // checks for non-real values
  if some(v => realp(v), data) {
    let gaps = count_if(v => eq(v, q_moveto), data)
    if gaps == 2 {
      // one point has non-real value
      mtell(list1(Str("Warning: excluding 1 point with non-numerical value.~%")))
      |> ignore
    }
    if gaps > 2 {
      // some points have non-real values
      mtell(
        list2(
          Str("Warning: excluding ~M points with non-numerical values.~%"),
          num_div(int(gaps), Fix(2L)),
        ),
      )
      |> ignore
    }
  } else {
    // none of the points have real values
    mtell(list1(Str("Warning: none of the points have numerical values.~%")))
    |> ignore
    data = Nil
  }
  data
}

///|
/// Two lists [x1...xn] and [y1...yn] are joined as [x1 y1...xn yn],
/// converting all expressions to real numbers.  If either xi or yi are not
/// real, both are replaced by 'moveto
fn parse_points_x_y(x : Value, y : Value) -> Value raise {
  let mut a = cdr(x)
  let mut b = cdr(y)
  let mut c : Value = Nil
  while b.truthy() {
    let af = coerce_float(car(a))
    let bf = coerce_float(car(b))
    if !realp(af) || !realp(bf) {
      c = cons(q_moveto, cons(q_moveto, c))
    } else {
      c = cons(bf, cons(af, c))
    }
    a = cdr(a)
    b = cdr(b)
  }
  cons(list1(q_mlist), reverse(c))
}

///|
/// One list [y1...yn] becomes the list [1 y1...n yn], converting all
/// expressions to real numbers.  If yi is not real, both i and yi are
/// replaced by 'moveto
fn parse_points_y(y : Value) -> Value raise {
  let mut a = 1
  let mut b = cdr(y)
  let mut c : Value = Nil
  while b.truthy() {
    let bf = coerce_float(car(b))
    if !realp(bf) {
      c = cons(q_moveto, cons(q_moveto, c))
    } else {
      c = cons(bf, cons(int(a), c))
    }
    a = a + 1
    b = cdr(b)
  }
  cons(list1(q_mlist), reverse(c))
}

///|
/// List [[x1,y1]...[xn,yn]] is transformed into [x1 y1...xn yn], converting
/// all expressions to real numbers.  If either xi or yi are not real, both
/// are replaced by 'moveto
fn parse_points_xy(xy : Value) -> Value raise {
  let mut ab = cdr(xy)
  let mut c : Value = Nil
  while ab.truthy() {
    let af = coerce_float(cadar(ab))
    let bf = coerce_float(caddar(ab))
    if !realp(af) || !realp(bf) {
      c = cons(q_moveto, cons(q_moveto, c))
    } else {
      c = cons(bf, cons(af, c))
    }
    ab = cdr(ab)
  }
  cons(list1(q_mlist), reverse(c))
}

// Adaptive plotting, based on the adaptive plotting code from YACAS. See
// http://yacas.sourceforge.net/Algo.html#c3s1 for a description of the
// algorithm.  More precise details can be found in the file
// yacas/scripts/plots.rep/plot2d.ys.

///|
/// Determine if we have a slow oscillation of the function.  Basically, for
/// each 3 consecutive function values, we check to see if the function is
/// monotonic or not.  There are 3 such sets, and the function is considered
/// slowly oscillating if at most 2 of them are not monotonic.
fn slow_oscillation_p(
  f0 : Value,
  f1 : Value,
  f2 : Value,
  f3 : Value,
  f4 : Value,
) -> Value raise {
  let sign_change = (x : Value, y : Value, z : Value) => if !(
      numberp(x) && numberp(y) && numberp(z)
    ) {
    // Something is not a number.  Assume the oscillation is not slow.
    2
  } else if (num_gt(y, x) && num_gt(y, z)) || (num_lt(y, x) && num_lt(y, z)) {
    1
  } else {
    0
  }
  lbool(sign_change(f0, f1, f2) + sign_change(f1, f2, f3) + sign_change(f2, f3, f4) <=
    2)
}

///|
/// Determine if the function values are smooth enough.  This means that
/// integrals of the functions on the left part and the right part of the
/// range are approximately the same.
fn smooth_enough_p(
  f_a : Value,
  f_a1 : Value,
  f_b : Value,
  f_b1 : Value,
  f_c : Value,
  eps : Value,
) -> Value raise {
  if numberp(f_a) &&
    numberp(f_a1) &&
    numberp(f_b) &&
    numberp(f_b1) &&
    numberp(f_c) {
    let quad = num_div(
      num_add(
        num_add(
          num_add(
            num_add(f_a, num_mul(Fix(-5L), f_a1)),
            num_mul(Fix(9L), f_b),
          ),
          num_mul(Fix(-7L), f_b1),
        ),
        num_mul(Fix(2L), f_c),
      ),
      Fix(24L),
    )
    let quad_b = num_div(
      num_sub(num_add(num_mul(Fix(5L), f_b), num_mul(Fix(8L), f_b1)), f_c),
      Fix(12L),
    )
    // According to the Yacas source code, quad is the Simpson quadrature
    // for the (fb,fb1) subinterval (using points b,b1,c), subtracted from
    // the 4-point Newton-Cotes quadrature for the (fb,fb1) subinterval
    // (using points a, a1, b, b1.
    //
    // quad-b is the Simpson quadrature for the (fb,f1) subinterval.
    //
    // This used to test for diff <= 0.  But in some situations, like
    // plot2d(0.99,[x,0,5]), roundoff prevents this from happening.  So we
    // do diff < delta instead, for some value of delta.
    let fmin = num_min(num_min(num_min(num_min(f_a, f_a1), f_b), f_b1), f_c)
    let diff = num_sub(
      num_abs(quad),
      num_mul(eps, num_sub(quad_b, fmin)),
    )
    let delta = num_mul(Fix(150L), Flo(1.1102230246251568e-16))
    lbool(num_le(diff, delta))
  } else {
    // Something is not a number, so assume it's not smooth enough.
    Nil
  }
}

///|
fn adaptive_plot(
  fcn : Value,
  a : Value,
  b : Value,
  c : Value,
  f_a : Value,
  f_b : Value,
  f_c : Value,
  depth : Value,
  eps : Value,
) -> Value raise {
  // Step 1:  Split the interval [a, c] into 5 points
  let a1 = num_div(num_add(a, b), Fix(2L))
  let b1 = num_div(num_add(b, c), Fix(2L))
  let f_a1 = funcall(fcn, [a1])
  let f_b1 = funcall(fcn, [b1])
  if !plusp(depth) ||
    (
      slow_oscillation_p(f_a, f_a1, f_b, f_b1, f_c).truthy() &&
      smooth_enough_p(f_a, f_a1, f_b, f_b1, f_c, eps).truthy()
    ) {
    // Everything is nice and smooth so we're done.  Don't refine anymore.
    list([a, f_a, a1, f_a1, b, f_b, b1, f_b1, c, f_c])
  } else if !symval(q_ear_plot_realpart).truthy() &&
    f_a is Nil &&
    f_a1 is Nil &&
    f_b is Nil &&
    f_b1 is Nil &&
    f_c is Nil {
    // We are not plotting the real part of the function and the function is
    // undefined at all points - assume it has complex value on [a,b].  Maybe
    // we should refine it a couple of times just to make sure?
    list([a, f_a, a1, f_a1, b, f_b, b1, f_b1, c, f_c])
  } else {
    // Need to refine.  Split the interval in half, and try to plot each
    // half.
    let left = adaptive_plot(
      fcn,
      a,
      a1,
      b,
      f_a,
      f_a1,
      f_b,
      num_sub(depth, Fix(1L)),
      num_mul(Fix(2L), eps),
    )
    let right = adaptive_plot(
      fcn,
      b,
      b1,
      c,
      f_b,
      f_b1,
      f_c,
      num_sub(depth, Fix(1L)),
      num_mul(Fix(2L), eps),
    )
    append(left, cddr(right))
  }
}

///|
fn adaptive_parametric_plot(
  x_fcn : Value,
  y_fcn : Value,
  a : Value,
  b : Value,
  c : Value,
  x_a : Value,
  x_b : Value,
  x_c : Value,
  y_a : Value,
  y_b : Value,
  y_c : Value,
  depth : Value,
  eps : Value,
) -> Value raise {
  // Step 1:  Split the interval [a, c] into 5 points
  let a1 = num_div(num_add(a, b), Fix(2L))
  let b1 = num_div(num_add(b, c), Fix(2L))
  let x_a1 = funcall(x_fcn, [a1])
  let x_b1 = funcall(x_fcn, [b1])
  let y_a1 = funcall(y_fcn, [a1])
  let y_b1 = funcall(y_fcn, [b1])
  if !plusp(depth) ||
    (
      // Should we have a different algorithm to determine slow oscillation
      // and smooth-enough for parametric plots?
      slow_oscillation_p(y_a, y_a1, y_b, y_b1, y_c).truthy() &&
      slow_oscillation_p(x_a, x_a1, x_b, x_b1, x_c).truthy() &&
      smooth_enough_p(y_a, y_a1, y_b, y_b1, y_c, eps).truthy() &&
      smooth_enough_p(x_a, x_a1, x_b, x_b1, x_c, eps).truthy()
    ) {
    // Everything is nice and smooth so we're done.  Don't refine anymore.
    list([x_a, y_a, x_a1, y_a1, x_b, y_b, x_b1, y_b1, x_c, y_c])
  } else if !symval(q_ear_plot_realpart).truthy() &&
    y_a is Nil &&
    y_a1 is Nil &&
    y_b is Nil &&
    y_b1 is Nil &&
    y_c is Nil &&
    x_a is Nil &&
    x_a1 is Nil &&
    x_b is Nil &&
    x_b1 is Nil &&
    x_c is Nil {
    // We are not plotting the real part of the function and the function is
    // undefined at all points - assume it has complex value on [a,b].
    list([x_a, y_a, x_a1, y_a1, x_b, y_b, x_b1, y_b1, x_c, y_c])
  } else {
    // Need to refine.  Split the interval in half, and try to plot each
    // half.
    let left = adaptive_parametric_plot(
      x_fcn,
      y_fcn,
      a,
      a1,
      b,
      x_a,
      x_a1,
      x_b,
      y_a,
      y_a1,
      y_b,
      num_sub(depth, Fix(1L)),
      num_mul(Fix(2L), eps),
    )
    let right = adaptive_parametric_plot(
      x_fcn,
      y_fcn,
      b,
      b1,
      c,
      x_b,
      x_b1,
      x_c,
      y_b,
      y_b1,
      y_c,
      num_sub(depth, Fix(1L)),
      num_mul(Fix(2L), eps),
    )
    // (cddr right) to skip over the point that is duplicated between the
    // right end-point of the left region and the left end-point of the
    // right
    append(left, cddr(right))
  }
}

///|
fn draw2d(fcn : Value, range : Value, plot_options : Value) -> Value raise {
  if d_listp(fcn).truthy() && equal(q_d_parametric, cadr(fcn)) {
    return draw2d_parametric_adaptive(fcn, plot_options)
  }
  if d_listp(fcn).truthy() && equal(q_d_discrete, cadr(fcn)) {
    return draw2d_discrete(fcn)
  }
  if d_listp(fcn).truthy() && equal(q_d_contour, cadr(fcn)) {
    let plot_options = plot__putf(plot_options, q_d_contour, t)
    return draw2d_implicit(caddr(fcn), plot_options)
  }
  if listp(fcn) && eq(q_mequal, caar(fcn)) {
    let plot_options = plot__putf(plot_options, q_d_contour, Nil)
    return draw2d_implicit(fcn, plot_options)
  }
  let nticks = getf(plot_options, q_d_nticks)
  let yrange = getf(plot_options, q_d_ybounds)
  let depth = getf(plot_options, q_d_adapt_depth)
  let fcn = coerce_float_fun(
    fcn,
    list2(list2(list1(q_mlist), second(range)), Str("plot2d")),
  )
  let mut x_start = coerce_float(third(range))
  let mut xend = coerce_float(fourth(range))
  let mut x_step = num_div(
    num_div(num_sub(xend, x_start), coerce_float(nticks)),
    Fix(2L),
  )
  let ymin = coerce_float(first(yrange))
  let ymax = coerce_float(second(yrange))
  plot__check_flonum(ymin, "YMIN")
  plot__check_flonum(ymax, "YMAX")
  let mut n_clipped = 0
  let mut n_non_numeric = 0
  let mut x_samples : Value = Nil
  let mut y_samples : Value = Nil
  let mut result : Value = Nil
  // Divide the region into NTICKS regions.  Each region has a start, mid
  // and endpoint. Then adaptively plot over each of these regions.  So it's
  // probably a good idea not to make NTICKS too big.  Since adaptive
  // plotting splits the sections in half, it's also probably not a good
  // idea to have NTICKS be a power of two.
  if getf(plot_options, q_d_logx).truthy() {
    x_start = llog(x_start)
    xend = llog(xend)
    x_step = num_div(
      num_div(num_sub(xend, x_start), coerce_float(nticks)),
      Fix(2L),
    )
  }
  let fun = lfunc("draw2d-fun", args => {
    let x = arg(args, 0)
    let y = if getf(plot_options, q_d_logx).truthy() {
      funcall(fcn, [lexp(x)])
    } else {
      funcall(fcn, [x])
    }
    if getf(plot_options, q_d_logy).truthy() && numberp(y) {
      if num_gt(y, Fix(0L)) {
        llog(y)
      } else {
        q_d_und
      }
    } else {
      y
    }
  })
  for k in 0..<(1 + 2 * to_int(nticks)) {
    let x = num_add(x_start, num_mul(int(k), x_step))
    x_samples = cons(x, x_samples)
    y_samples = cons(funcall(fun, [x]), y_samples)
  }
  x_samples = nreverse(x_samples)
  y_samples = nreverse(y_samples)
  // For each region, adaptively plot it.
  let mut xs = x_samples
  let mut x_mid = cdr(x_samples)
  let mut x_end = cddr(x_samples)
  let mut ys = y_samples
  let mut y_mid = cdr(y_samples)
  let mut y_end = cddr(y_samples)
  while x_end.truthy() {
    // The region is x-start to x-end, with mid-point x-mid.
    //
    // The cddr is to remove the one extra sample (x and y value) that
    // adaptive plot returns. But on the first iteration, result is empty,
    // so we don't want the cddr because we want all the samples returned
    // from adaptive-plot.  On subsequent iterations, it's a duplicate of the
    // last point of the previous interval.
    let pts = adaptive_plot(
      fun,
      car(xs),
      car(x_mid),
      car(x_end),
      car(ys),
      car(y_mid),
      car(y_end),
      depth,
      Flo(1.0e-5),
    )
    result = if result.truthy() { append(result, cddr(pts)) } else { pts }
    xs = cddr(xs)
    x_mid = cddr(x_mid)
    x_end = cddr(x_end)
    ys = cddr(ys)
    y_mid = cddr(y_mid)
    y_end = cddr(y_end)
  }
  // Fix up out-of-range values and clobber non-numeric values.
  let mut x = result
  let mut y = cdr(result)
  while y.truthy() {
    if numberp(car(y)) {
      // We can let graphic program do the clipping for us.  This results in
      // better looking plots. For example:
      //     plot2d(x-floor(x),[x,0,5], [y,0,.5])
      // has lines going all the way to the limits.  Previously, the lines
      // would stop before the limit.
      if !(num_le(ymin, car(y)) && num_le(car(y), ymax)) {
        n_clipped = n_clipped + 1
      }
    } else {
      n_non_numeric = n_non_numeric + 1
      rplaca(x, q_moveto) |> ignore
      rplaca(y, q_moveto) |> ignore
    }
    if getf(plot_options, q_d_logx).truthy() && numberp(car(x)) {
      rplaca(x, lexp(car(x))) |> ignore
    }
    if getf(plot_options, q_d_logy).truthy() && numberp(car(y)) {
      rplaca(y, lexp(car(y))) |> ignore
    }
    x = cddr(x)
    y = cddr(y)
  }
  plot__finish_points(result, n_clipped, n_non_numeric)
}

///|
fn get_range(lis : Value) -> Value raise {
  let mut ymin : Value = Flo(1.7976931348623157e308)
  let mut ymax : Value = Flo(-1.7976931348623157e308)
  let mut l = lis
  while l.truthy() {
    if !floatp(car(l)) {
      rplaca(l, lfloat(car(l))) |> ignore
    }
    if num_lt(car(l), ymin) {
      ymin = car(l)
    }
    if num_lt(ymax, car(l)) {
      ymax = car(l)
    }
    l = cddr(l)
  }
  list3(list1(q_mlist), ymin, ymax)
}

///|
/// The state of CL's *RANDOM-STATE* as used by RANDOM-NAME, which reseeds it
/// with (make-random-state t) on every call.
let plot__random_counter : Ref[Int] = Ref(0)

///|
/// random-file-name
/// Creates a random word of 'count' alphanumeric characters
fn random_name(count : Value) -> Value raise {
  let chars = "0123456789abcdefghijklmnopqrstuvwxyz"
  // (setf *random-state* (make-random-state t))
  plot__random_counter.val = plot__random_counter.val + 1
  let seed = num_add(
    mt_generate_seed(),
    int(process_id() * 1000 + plot__random_counter.val),
  )
  let state = mt__make_random_object(mt_init_random_state(seed~))
  let sb = StringBuilder::new()
  for _ in 0..<to_int(count) {
    let k = to_int(mt_random(Fix(36L), state~))
    sb.write_char(chars.get_char(k).unwrap_or('0'))
  }
  Str(sb.to_string())
}

///|
fn plot_temp_file0(file : Value, preserve_file? : Value = Nil) -> Value raise {
  let tmp = symval(q_ear_maxima_tempdir)
  let filename = if tmp.truthy() {
    format(Nil, "~a/~a", [tmp, file])
  } else {
    file
  }
  if !preserve_file.truthy() {
    sethash(filename, symval(q_ear_temp_files_list), t) |> ignore
  }
  format(Nil, "~a", [filename])
}

///|
fn plot_temp_file(
  file : Value,
  preserve_file? : Value = Nil,
  plot_options? : Value = Nil,
) -> Value raise {
  let script_name_or_fun = if plot_options.truthy() {
    getf(plot_options, q_d_gnuplot_script_file)
  } else {
    Nil
  }
  if script_name_or_fun is Nil {
    plot_temp_file0(file, preserve_file~)
  } else {
    let script_name = if symbolp(script_name_or_fun) {
      mfuncall(script_name_or_fun, list1(file))
    } else {
      script_name_or_fun
    }
    if plot__has_directory(script_name) {
      script_name
    } else {
      plot_temp_file0(script_name, preserve_file~)
    }
  }
}

///|
/// If no file path is given, uses temporary directory path
fn plot_file_path(
  file : Value,
  preserve_file? : Value = Nil,
  plot_options? : Value = Nil,
) -> Value raise {
  if plot__has_directory(file) {
    file
  } else {
    plot_temp_file(file, preserve_file~, plot_options~)
  }
}

///|
/// The value of a one-argument option after "if (cddr opt) (setf (cddr opt)
/// (mapcar #'coerce-float (cddr opt)))".
fn plot__coerce_float_tail(opt : Value) -> Unit raise {
  if cddr(opt).truthy() {
    rplacd(cdr(opt), mapcar(x => coerce_float(x), cddr(opt))) |> ignore
  }
}

///|
/// PLOT OPTIONS PARSING
/// plot-options-parser puts the plot options given into a property list.
/// maxopts: a list (not a Maxima list!) with plot options.
/// options: a property list, or an empty list.
/// Example:
///  (plot-options-parser (list #$[x,-2,2]$ #$[nticks,30]$) '($xlabel "t"))
/// returns:
///  ($NTICKS 30 $X (-2.0 2.0) $XLABEL "t")
fn plot_options_parser(maxopts : Value, options : Value) -> Value raise {
  let mut options = options
  let put = (k : Value, v : Value) => options = plot__putf(options, k, v)
  let rem = (k : Value) => options = plot__remf(options, k).0
  let realp_ = plot__pred("realp", v => realp(v))
  let naturalp_ = plot__pred("naturalp", v => naturalp(v).truthy())
  let stringp_ = plot__pred("stringp", v => stringp(v))
  let plotcolorp_ = plot__pred("plotcolorp", v => plotcolorp(v).truthy())
  let string_ = plot__pred("string", v => {
    plot__string_designator(v) |> ignore
    true
  })
  let nonneg_int = plot__pred("non-negative-integer", n => integerp(n) &&
    num_ge(n, Fix(0L)))
  for opt in maxopts.iter() {
    if !(d_listp(opt).truthy() || symbolp(opt)) {
      merr(
        "plot-options-parser: option \"~M\" should be a list or a symbol",
        [opt],
      )
      |> ignore
    }
    if d_listp(opt).truthy() {
      let name = second(opt)
      if !d_symbolp(name).truthy() {
        merr(
          "plot-options-parser: Expecting option name as a symbol, found: \"~M\"",
          [opt],
        )
        |> ignore
      }
      let nm = match name {
        Sym(s) => s.name
        Nil => "nil"
        _ => ""
      }
      match nm {
        "$adapt_depth" =>
          put(
            q_d_adapt_depth,
            check_option(
              cdr(opt),
              // N should be a non-negative integer
              nonneg_int,
              Str("a non-negative integer"),
              count=Fix(1L),
            ),
          )
        "$axes" =>
          put(
            q_d_axes,
            check_option_b(
              cdr(opt),
              plot__pred("axesoptionp", v => axesoptionp(v).truthy()),
              Str("x, y, solid"),
              count=Fix(1L),
            ),
          )
        "$azimuth" => {
          if caddr(opt).truthy() {
            rplaca(cddr(opt), parse_azimuth(caddr(opt))) |> ignore
          }
          put(
            q_d_azimuth,
            check_option(cdr(opt), realp_, Str("a real number"), count=Fix(1L)),
          )
        }
        "$background_color" =>
          put(
            q_d_background_color,
            check_option_b(cdr(opt), plotcolorp_, Str("a color"), count=Fix(1L)),
          )
        "mbox" => put(q_mbox, check_option_boole(cdr(opt)))
        "$color" =>
          put(q_d_color, check_option(cdr(opt), plotcolorp_, Str("a color")))
        "$color_bar" => put(q_d_color_bar, check_option_boole(cdr(opt)))
        "$color_bar_tics" => {
          plot__coerce_float_tail(opt)
          put(
            q_d_color_bar_tics,
            check_option_b(cdr(opt), realp_, Str("a real number"), count=Fix(3L)),
          )
        }
        "$elevation" => {
          if caddr(opt).truthy() {
            rplaca(cddr(opt), parse_elevation(caddr(opt))) |> ignore
          }
          put(
            q_d_elevation,
            check_option(cdr(opt), realp_, Str("a real number"), count=Fix(1L)),
          )
        }
        "$grid" =>
          put(
            q_d_grid,
            check_option(
              cdr(opt),
              naturalp_,
              Str("a natural number"),
              count=Fix(2L),
            ),
          )
        "$grid2d" => put(q_d_grid2d, check_option_boole(cdr(opt)))
        "$iterations" =>
          put(
            q_d_iterations,
            check_option(
              cdr(opt),
              naturalp_,
              Str("a natural number"),
              count=Fix(1L),
            ),
          )
        "$label" => put(q_d_label, check_option_label(cdr(opt)))
        "$legend" =>
          put(q_d_legend, {
            let x = check_option_b(cdr(opt), stringp_, Str("a string"))
            if listp(x) {
              x
            } else {
              cons(x, Nil)
            }
          })
        "$levels" => put(q_d_levels, check_option_levels(cdr(opt)))
        "$lighting" => put(q_d_lighting, check_option_boole(cdr(opt)))
        "$logx" => put(q_d_logx, check_option_boole(cdr(opt)))
        "$logy" => put(q_d_logy, check_option_boole(cdr(opt)))
        "$mesh_lines_color" =>
          put(
            q_d_mesh_lines_color,
            check_option_b(cdr(opt), plotcolorp_, Str("a color"), count=Fix(1L)),
          )
        "$nticks" =>
          put(
            q_d_nticks,
            check_option(
              cdr(opt),
              naturalp_,
              Str("a natural number"),
              count=Fix(1L),
            ),
          )
        "$palette" => put(q_d_palette, check_option_palette(cdr(opt)))
        "$plotepsilon" =>
          put(
            q_d_plotepsilon,
            check_option(cdr(opt), realp_, Str("a real number"), count=Fix(1L)),
          )
        "$plot_format" => put(q_d_plot_format, check_option_format(cdr(opt)))
        "$plot_realpart" => put(q_d_plot_realpart, check_option_boole(cdr(opt)))
        "$point_type" =>
          put(
            q_d_point_type,
            check_option(
              cdr(opt),
              plot__pred("pointtypep", v => pointtypep(v).truthy()),
              Str("a point type"),
            ),
          )
        "$pdf_file" =>
          put(
            q_d_pdf_file,
            check_option(cdr(opt), stringp_, Str("a string"), count=Fix(1L)),
          )
        "$png_file" =>
          put(
            q_d_png_file,
            check_option(cdr(opt), stringp_, Str("a string"), count=Fix(1L)),
          )
        "$ps_file" =>
          put(
            q_d_ps_file,
            check_option(cdr(opt), stringp_, Str("a string"), count=Fix(1L)),
          )
        "$run_viewer" => put(q_d_run_viewer, check_option_boole(cdr(opt)))
        "$same_xy" => put(q_d_same_xy, check_option_boole(cdr(opt)))
        "$same_xyz" => put(q_d_same_xyz, check_option_boole(cdr(opt)))
        "$sample" =>
          put(
            q_d_sample,
            check_option(
              cdr(opt),
              naturalp_,
              Str("a natural number"),
              count=Fix(2L),
            ),
          )
        "$style" => put(q_d_style, check_option_style(cdr(opt)))
        "$svg_file" =>
          put(
            q_d_svg_file,
            check_option(cdr(opt), stringp_, Str("a string"), count=Fix(1L)),
          )
        "$t" => put(q_d_t, cddr(check_range(opt)))
        "$title" =>
          put(
            q_d_title,
            check_option(cdr(opt), stringp_, Str("a string"), count=Fix(1L)),
          )
        "$transform_xy" =>
          put(
            q_d_transform_xy,
            check_option_b(
              cdr(opt),
              plot__pred("functionp", v => functionp_(v).truthy()),
              Str("a function make_transform"),
              count=Fix(1L),
            ),
          )
        "$window" =>
          put(
            q_d_window,
            check_option(
              cdr(opt),
              nonneg_int,
              Str("a non-negative integer"),
              count=Fix(1L),
            ),
          )
        "$x" => put(q_d_x, cddr(check_range(opt)))
        "$xbounds" => put(q_d_xbounds, cddr(check_range(opt)))
        "$xlabel" =>
          put(
            q_d_xlabel,
            check_option(cdr(opt), string_, Str("a string"), count=Fix(1L)),
          )
        "$xtics" => {
          plot__coerce_float_tail(opt)
          put(
            q_d_xtics,
            check_option_b(cdr(opt), realp_, Str("a real number"), count=Fix(3L)),
          )
        }
        "$xy_scale" => {
          plot__coerce_float_tail(opt)
          put(
            q_d_xy_scale,
            check_option(
              cdr(opt),
              plot__pred("realpositivep", v => realpositivep(v).truthy()),
              Str("a positive real number"),
              count=Fix(2L),
            ),
          )
        }
        "$y" => put(q_d_y, cddr(check_range(opt)))
        "$ybounds" => put(q_d_ybounds, cddr(check_range(opt)))
        "$ylabel" =>
          put(
            q_d_ylabel,
            check_option(cdr(opt), string_, Str("a string"), count=Fix(1L)),
          )
        "$ytics" => {
          plot__coerce_float_tail(opt)
          put(
            q_d_ytics,
            check_option_b(cdr(opt), realp_, Str("a real number"), count=Fix(3L)),
          )
        }
        "$yx_ratio" => {
          if caddr(opt).truthy() {
            rplaca(cddr(opt), coerce_float(caddr(opt))) |> ignore
          }
          put(
            q_d_yx_ratio,
            check_option(cdr(opt), realp_, Str("a real number"), count=Fix(1L)),
          )
        }
        "$z" => put(q_d_z, cddr(check_range(opt)))
        "$zlabel" =>
          put(
            q_d_zlabel,
            check_option(cdr(opt), string_, Str("a string"), count=Fix(1L)),
          )
        "$zmin" => {
          if caddr(opt).truthy() {
            rplaca(cddr(opt), coerce_float(caddr(opt))) |> ignore
          }
          put(
            q_d_zmin,
            check_option_b(cdr(opt), realp_, Str("a real number"), count=Fix(1L)),
          )
        }
        "$ztics" => {
          plot__coerce_float_tail(opt)
          put(
            q_d_ztics,
            check_option_b(cdr(opt), realp_, Str("a real number"), count=Fix(3L)),
          )
        }
        "$gnuplot_4_0" => put(q_d_gnuplot_4_0, check_option_boole(cdr(opt)))
        "$gnuplot_curve_titles" =>
          put(
            q_d_gnuplot_curve_titles,
            check_option(cdr(opt), stringp_, Str("a string")),
          )
        "$gnuplot_curve_styles" =>
          put(
            q_d_gnuplot_curve_styles,
            check_option(cdr(opt), stringp_, Str("a string")),
          )
        "$gnuplot_default_term_command" =>
          put(
            q_d_gnuplot_default_term_command,
            check_option(cdr(opt), stringp_, Str("a string"), count=Fix(1L)),
          )
        "$gnuplot_dumb_term_command" =>
          put(
            q_d_gnuplot_dumb_term_command,
            check_option(cdr(opt), stringp_, Str("a string"), count=Fix(1L)),
          )
        "$gnuplot_out_file" =>
          put(
            q_d_gnuplot_out_file,
            check_option(cdr(opt), stringp_, Str("a string"), count=Fix(1L)),
          )
        "$gnuplot_script_file" => {
          put(
            q_d_gnuplot_script_file,
            check_option(
              cdr(opt),
              plot__pred("string-or-symbol", x => stringp(x) || symbolp(x)),
              Str("a string or symbol"),
              count=Fix(1L),
            ),
          )
          put(q_d_plot_format, q_d_gnuplot)
        }
        "$gnuplot_pm3d" => put(q_d_gnuplot_pm3d, check_option_boole(cdr(opt)))
        "$gnuplot_strings" =>
          put(q_d_gnuplot_strings, check_option_boole(cdr(opt)))
        "$gnuplot_svg_background" =>
          put(
            q_d_background_color,
            check_option_b(cdr(opt), plotcolorp_, Str("a color"), count=Fix(1L)),
          )
        "$gnuplot_preamble" =>
          put(
            q_d_gnuplot_preamble,
            check_option(cdr(opt), stringp_, Str("a string"), count=Fix(1L)),
          )
        "$gnuplot_postamble" =>
          put(
            q_d_gnuplot_postamble,
            check_option(cdr(opt), stringp_, Str("a string"), count=Fix(1L)),
          )
        "$gnuplot_pdf_term_command" =>
          put(
            q_d_gnuplot_pdf_term_command,
            check_option(cdr(opt), stringp_, Str("a string"), count=Fix(1L)),
          )
        "$gnuplot_png_term_command" =>
          put(
            q_d_gnuplot_png_term_command,
            check_option(cdr(opt), stringp_, Str("a string"), count=Fix(1L)),
          )
        "$gnuplot_ps_term_command" =>
          put(
            q_d_gnuplot_ps_term_command,
            check_option(cdr(opt), stringp_, Str("a string"), count=Fix(1L)),
          )
        "$gnuplot_svg_term_command" =>
          put(
            q_d_gnuplot_svg_term_command,
            check_option(cdr(opt), stringp_, Str("a string"), count=Fix(1L)),
          )
        // gnuplot_term is a tricky one: when it is just default, dumb or ps,
        // we want it to be a symbol, but when it is more complicated, i.e.
        // "ps; size 16cm, 12cm", it must be a string and not a symbol
        "$gnuplot_term" => {
          let mut s = caddr(opt)
          match s {
            Str("default") => s = q_d_default
            Str("dumb") => s = q_d_dumb
            Str("ps") => s = q_d_ps
            _ => ()
          }
          if atom(s) {
            put(q_d_gnuplot_term, s)
          } else {
            merr(
              "Wrong argument for plot option \"gnuplot_term\". Expecting a string or a symbol but found \"~M\".",
              [s],
            )
            |> ignore
          }
        }
        _ =>
          merr("plot-options-parser: unknown plot option: ~M", [opt]) |> ignore
      }
    } else if symbolp(opt) {
      let nm = match opt {
        Sym(s) => s.name
        _ => "nil"
      }
      match nm {
        "$axes" => put(q_d_axes, t)
        "mbox" => put(q_mbox, t)
        "$color_bar" => put(q_d_color_bar, t)
        "$color_bar_tics" => rem(q_d_color_bar_tics)
        "$cylindrical" => put(q_d_transform_xy, q_d_polar_to_xy)
        "$geomview" => put(q_d_plot_format, q_d_geomview)
        "$grid2d" => put(q_d_grid2d, t)
        "$legend" => rem(q_d_legend)
        "$mesh_lines_color" => rem(q_d_mesh_lines_color)
        "$lighting" => put(q_d_lighting, t)
        "$logx" => put(q_d_logx, t)
        "$logy" => put(q_d_logy, t)
        "$palette" => rem(q_d_palette)
        "$plot_realpart" => put(q_d_plot_realpart, t)
        "$run_viewer" => put(q_d_run_viewer, t)
        "$same_xy" => put(q_d_same_xy, t)
        "$same_xyz" => put(q_d_same_xyz, t)
        "$xmaxima" => put(q_d_plot_format, q_d_xmaxima)
        "$xtics" => rem(q_d_xtics)
        "$ytics" => rem(q_d_ytics)
        "$zmin" => rem(q_d_zmin)
        "$gnuplot" => put(q_d_plot_format, q_d_gnuplot)
        "$gnuplot_4_0" => put(q_d_gnuplot_4_0, t)
        "$gnuplot_pipes" => put(q_d_plot_format, q_d_gnuplot_pipes)
        "$gnuplot_pm3d" => put(q_d_gnuplot_pm3d, t)
        "$gnuplot_strings" => put(q_d_gnuplot_strings, t)
        "$noaxes" => put(q_d_axes, Nil)
        "$nobox" => put(q_mbox, Nil)
        "$nocolor_bar" => put(q_d_color_bar, Nil)
        "$nocolor_bat_tics" => put(q_d_color_bat_tics, Nil)
        "$nogrid2d" => put(q_d_grid2d, Nil)
        "$nolegend" => put(q_d_legend, Nil)
        "$nolighting" => put(q_d_lighting, Nil)
        "$nologx" => put(q_d_logx, Nil)
        "$nology" => put(q_d_logy, Nil)
        "$nomesh_lines" => put(q_d_mesh_lines_color, Nil)
        "$nopalette" => put(q_d_palette, Nil)
        "$noplot_realpart" => put(q_d_plot_realpart, Nil)
        "$norun_viewer" => put(q_d_run_viewer, Nil)
        "$noxlabel" => put(q_d_xlabel, Str(""))
        "$nosame_xy" => put(q_d_same_xy, Nil)
        "$nosame_xyz" => put(q_d_same_xyz, Nil)
        "$notransform_xy" => rem(q_d_transform_xy)
        "$noxtics" => put(q_d_xtics, Nil)
        "$noylabel" => put(q_d_ylabel, Str(""))
        "$noytics" => put(q_d_ytics, Nil)
        "$noztics" => put(q_d_ztics, Nil)
        "$nozlabel" => put(q_d_zlabel, Str(""))
        "$nognuplot_strings" => put(q_d_gnuplot_strings, Nil)
        "$nognuplot_svg_background" => put(q_d_gnuplot_svg_background, Nil)
        "$spherical" => put(q_d_transform_xy, q_d_spherical_to_xyz)
        _ => merr("Unknown plot option \"~M\".", [opt]) |> ignore
      }
    }
  }
  options
}

///|
/// natural numbers predicate
fn naturalp(n : Value) -> Value raise {
  lbool(integerp(n) && num_gt(n, Fix(0L)))
}

///|
/// positive real numbers predicate
fn realpositivep(x : Value) -> Value raise {
  lbool(realp(x) && num_gt(x, Fix(0L)))
}

///|
/// possible values for the axes option
fn axesoptionp(o : Value) -> Value raise {
  lbool(member(o, list3(q_d_x, q_d_y, q_d_solid)).truthy())
}

///|
/// the 13 possibilities for the point types
fn pointtypep(p : Value) -> Value raise {
  lbool(
    member(
      p,
      list([
        q_d_bullet, q_d_circle, q_d_plus, q_d_times, q_d_asterisk, q_mbox, q_d_square,
        q_d_triangle, q_d_delta, q_d_wedge, q_d_nabla, q_d_diamond, q_d_lozenge,
      ]),
    ).truthy(),
  )
}

///|
/// tries to convert az into a floating-point number between 0 and 360
fn parse_azimuth(az : Value) -> Value raise {
  num_mod(coerce_float(meval(az)), Fix(360L))
}

///|
/// tries to convert el into a floating-poitn number between -180 and 180
fn parse_elevation(el : Value) -> Value raise {
  num_sub(
    num_mod(num_add(Fix(180L), coerce_float(meval(el))), Fix(360L)),
    Fix(180L),
  )
}

// The following functions check the value of an option returning an atom
// when there is only one argument or a list when there are several
// arguments

///|
/// Checks for one or more items of the same type, using the test given.
/// If count is given, the number of arguments must be exactly count.
fn check_option(
  option : Value,
  test_ : Value,
  type_ : Value,
  count? : Value = Nil,
) -> Value raise {
  if count.truthy() {
    if !num_eq(int(length(option) - 1), count) {
      merr(
        "Wrong number of arguments for plot option \"~M\". Expecting ~M but found ~M.",
        [car(option), count, int(length(option) - 1)],
      )
      |> ignore
    }
  }
  for item in cdr(option).iter() {
    if !funcall(test_, [item]).truthy() {
      merr(
        "Wrong argument for plot option \"~M\". Expecting ~M but found \"~M\".",
        [car(option), type_, item],
      )
      |> ignore
    }
  }
  if length(option) == 2 {
    cadr(option)
  } else {
    cdr(option)
  }
}

///|
/// Accepts one or more items of the same type or false.  When given, count
/// is the maximum number of items.
fn check_option_b(
  option : Value,
  test_ : Value,
  type_ : Value,
  count? : Value = Nil,
) -> Value raise {
  let n = length(option) - 1
  if count.truthy() {
    if !(n < to_int(count) + 1) {
      merr("Plot option ~M must have ~M arguments, not ~M.", [
        car(option),
        count,
        int(length(option) - 1),
      ])
      |> ignore
    }
  }
  if n == 0 {
    // (merror "Option ~M should be given ..." option): OPTION is a Lisp
    // list, which the error message display cannot handle.
    raise LispError::SimpleError(
      "The value\n  " + prin1_to_string(car(option)) + "\nis not of type\n  LIST",
    )
  } else if n == 1 {
    if funcall(test_, [cadr(option)]).truthy() ||
      cadr(option) is Nil ||
      eq(cadr(option), t) {
      cadr(option)
    } else {
      merr("Value of option ~M. should be ~M or false, not \"~M\".", [
        car(option),
        type_,
        cadr(option),
      ])
    }
  } else if n > 1 {
    for i in 0..<n {
      if !funcall(test_, [nth(i + 1, option)]).truthy() {
        merr("Value of option ~M should be ~M, not \"~M\".", [
          car(option),
          type_,
          nth(i + 1, option),
        ])
        |> ignore
      }
    }
    cdr(option)
  } else {
    Nil
  }
}

///|
/// Boolean options can be [option], [option,true] or [option,false]
fn check_option_boole(option : Value) -> Value raise {
  if length(option) == 1 {
    t
  } else if length(option) == 2 && (eq(cadr(option), t) || cadr(option) is Nil) {
    cadr(option)
  } else {
    merr("plot option ~M must be either true or false.", [car(option)])
  }
}

///|
/// label can be either [label, string, real, real] or
/// [label, [string_1, real, real],...,[string_n, real, real]]
fn check_option_label(option : Value) -> Value raise {
  let opt = if !d_listp(cadr(option)).truthy() {
    list1(cons(list1(q_mlist), cdr(option)))
  } else {
    cdr(option)
  }
  for item in opt.iter() {
    let ok = d_listp(item).truthy() &&
      length(item) == 4 &&
      stringp(second(item)) &&
      {
        rplaca(cddr(item), coerce_float(third(item))) |> ignore
        realp(third(item))
      } &&
      {
        rplaca(cdddr(item), coerce_float(fourth(item))) |> ignore
        realp(fourth(item))
      }
    if !ok {
      merr(
        "Wrong argument ~M for option ~M. Must be either [label,\"text\",x,y] or [label, [\"text 1\",x1,y1],...,[\"text n\",xn,yn]]",
        [item, car(option)],
      )
      |> ignore
    }
  }
  opt
}

///|
/// one of the possible formats
fn check_option_format(option : Value) -> Value raise {
  let formats = list([q_d_geomview, q_d_gnuplot, q_d_gnuplot_pipes, q_d_xmaxima])
  if !member(cadr(option), formats).truthy() {
    merr(
      "Wrong argument ~M for option ~M. Must one of the following symbols: geomview, gnuplot, xmaxima (or gnuplot_pipes in Unix)",
      [cadr(option), car(option)],
    )
    |> ignore
  }
  cadr(option)
}

///|
/// Checks that a palette option is either a valid color, a maxima list of
/// valid colors, or the name of a predfined palette.  For backward
/// compatibily, it is also accepted a maxima list starting with the keyword
/// $hue, $saturation, $value or $gradient; the first three types must be
/// followed by 4 floating-point numbers, while gradient must be followed by
/// a list of at least two valid colors.  It returns the definition of the
/// palette, if it is valid, or nil.
fn check_option_palette(option : Value) -> Value raise {
  let mut palette = cadr(option)
  if atom(palette) {
    if !getf(symval(q_ear_plot_palettes), palette).truthy() {
      if !plotcolorp(palette).truthy() {
        merr("Palette: ~M is not a predefined palette or a valid color.", [
          palette,
        ])
        |> ignore
      }
    }
  } else if d_listp(palette).truthy() {
    if member(
        cadr(palette),
        list([q_d_hue, q_d_saturation, q_d_value, q_d_gradient]),
      ).truthy() {
      if eq(cadr(palette), q_d_gradient) {
        if length(cddr(palette)) < 2 {
          merr("Palette: gradient needs at least 2 colors.", []) |> ignore
        }
        for c in cddr(palette).iter() {
          if !plotcolorp(c).truthy() {
            merr("Palette: ~M is not a valid color", [c]) |> ignore
          }
        }
      } else {
        rplacd(cdr(palette), mapcar(x => coerce_float(x), cddr(palette)))
        |> ignore
        check_option(
          butlast(cdr(maxima_lit("[value,0.2,0,0,10]"))),
          plot__pred("real01p", v => real01p(v).truthy()),
          Str("a number between 0 and 1"),
          count=Fix(3L),
        )
        |> ignore
        check_option(
          cons(cadr(palette), last(cdr(palette))),
          plot__pred("realp", v => realp(v)),
          Str("a real number"),
          count=Fix(1L),
        )
        |> ignore
      }
    } else {
      if length(cdr(palette)) < 2 {
        merr("Palette: at least 2 colors are required.", []) |> ignore
      }
      for c in cdr(palette).iter() {
        if !plotcolorp(c).truthy() {
          merr("Palette: ~M is not a valid color", [c]) |> ignore
        }
      }
    }
    palette = cdr(palette)
  } else {
    merr("Palette: expecting a valid palette, found ~M.", [palette]) |> ignore
  }
  palette
}

///|
/// style can be one or several of the names of the styles or one or several
/// Maxima lists starting with the name of one of the styles.
fn check_option_style(option : Value) -> Value raise {
  if length(option) == 2 && cadr(option) is Nil {
    Nil
  } else {
    let mut parsed : Value = Nil
    for item in cdr(option).iter() {
      let name = if d_listp(item).truthy() { second(item) } else { item }
      if !member(
          name,
          list([q_d_lines, q_d_points, q_d_linespoints, q_d_dots, q_d_impulses]),
        ).truthy() {
        merr("Wrong argument ~M for option ~M. Not a valid style", [
          name,
          car(option),
        ])
        |> ignore
      }
      parsed = cons(item, parsed)
    }
    reverse(parsed)
  }
}

///|
/// Transform can be false or the name of a function for the transformation.
fn check_option_transform(option : Value) -> Value raise {
  if length(option) == 2 && (atom(cadr(option)) || cadr(option) is Nil) {
    cadr(option)
  } else {
    merr(
      "Wrong argument ~M for option ~M. Should be either false or the name of function for the transformation",
      [option, car(option)],
    )
  }
}

///|
/// levels can be a single natural number (requested number of levels) or
/// two or more floating-point numbers.
fn check_option_levels(option : Value) -> Value raise {
  if length(option) < 3 {
    check_option(
      option,
      plot__pred("naturalp", v => naturalp(v).truthy()),
      Str("a natural number"),
      count=Fix(1L),
    )
  } else {
    mapcar(x => coerce_float(x), cdr(option)) |> ignore
    check_option(
      option,
      plot__pred("realp", v => realp(v)),
      Str("a real number"),
      count=int(length(option) - 1),
    )
  }
}

///|
/// Tries to get n numbers between fmin and fmax of the form d*10^e, where d
/// is either 1, 2 or 5.  It returns a list with n or less numbers (adapted
/// from procedure getticks of Xmaxima)
fn getlevels(fmin : Value, fmax : Value, n : Value) -> Value raise {
  let len = num_sub(fmax, fmin)
  let mut best = 0
  let mut ans : Value = Nil
  for v in [Value::Flo(0.1), Value::Flo(0.2), Value::Flo(0.5)] {
    let val = ceiling1(
      num_div(llog(num_div(num_div(len, n), v)), llog(Fix(10L))),
    )
    let fac = num_div(num_div(Fix(1L), v), expt(Fix(10L), val))
    let j1 = ceiling1(num_mul(fmin, fac))
    let j2 = floor1(num_mul(fmax, fac))
    let mut levels : Value = Nil
    let mut j = j1
    while !num_gt(j, j2) {
      levels = cons(num_div(j, fac), levels)
      j = num_add(j, Fix(1L))
    }
    if length(levels) > best {
      best = length(levels)
      ans = copy_list(levels)
    }
  }
  reverse(ans)
}
