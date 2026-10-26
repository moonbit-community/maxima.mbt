// Rendering helpers for the SBCL reference tests: doubles are written as
// their IEEE bit patterns so that comparisons are bit-for-bit.

///|
trait Render {
  render_to(Self, StringBuilder) -> Unit
}

///|
impl Render for Double with render_to(self, s) {
  s.write_string(" d" + self.reinterpret_as_int64().to_string())
}

///|
impl Render for Int with render_to(self, s) {
  s.write_string(" i" + self.to_string())
}

///|
impl Render for Unit with render_to(_self, _s) {

}

///|
impl[A : Render, B : Render] Render for (A, B) with render_to(self, s) {
  self.0.render_to(s)
  self.1.render_to(s)
}

///|
impl[A : Render, B : Render, C : Render] Render for (A, B, C) with render_to(
  self,
  s,
) {
  self.0.render_to(s)
  self.1.render_to(s)
  self.2.render_to(s)
}

///|
impl[A : Render, B : Render, C : Render, D : Render] Render for (A, B, C, D) with render_to(
  self,
  s,
) {
  self.0.render_to(s)
  self.1.render_to(s)
  self.2.render_to(s)
  self.3.render_to(s)
}

///|
impl[A : Render, B : Render, C : Render, D : Render, E : Render] Render for (
  A,
  B,
  C,
  D,
  E,
) with render_to(self, s) {
  self.0.render_to(s)
  self.1.render_to(s)
  self.2.render_to(s)
  self.3.render_to(s)
  self.4.render_to(s)
}

///|
impl[A : Render, B : Render, C : Render, D : Render, E : Render, F : Render] Render for (
  A,
  B,
  C,
  D,
  E,
  F,
) with render_to(self, s) {
  self.0.render_to(s)
  self.1.render_to(s)
  self.2.render_to(s)
  self.3.render_to(s)
  self.4.render_to(s)
  self.5.render_to(s)
}

///|
impl[
  A : Render,
  B : Render,
  C : Render,
  D : Render,
  E : Render,
  F : Render,
  G : Render,
] Render for (A, B, C, D, E, F, G) with render_to(self, s) {
  self.0.render_to(s)
  self.1.render_to(s)
  self.2.render_to(s)
  self.3.render_to(s)
  self.4.render_to(s)
  self.5.render_to(s)
  self.6.render_to(s)
}

///|
impl[
  A : Render,
  B : Render,
  C : Render,
  D : Render,
  E : Render,
  F : Render,
  G : Render,
  H : Render,
  I : Render,
  J : Render,
] Render for (A, B, C, D, E, F, G, H, I, J) with render_to(self, s) {
  self.0.render_to(s)
  self.1.render_to(s)
  self.2.render_to(s)
  self.3.render_to(s)
  self.4.render_to(s)
  self.5.render_to(s)
  self.6.render_to(s)
  self.7.render_to(s)
  self.8.render_to(s)
  self.9.render_to(s)
}

///|
fn[T : Render] render(s : StringBuilder, v : T) -> Unit {
  v.render_to(s)
}

///|
fn[T : Render] render_array(s : StringBuilder, a : FixedArray[T]) -> Unit {
  s.write_string(" |")
  for v in a {
    v.render_to(s)
  }
}
