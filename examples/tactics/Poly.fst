module Poly

open CanonCommSemiring
open FStar.Tactics
open FStar.Mul

// These assumptions are proven in https://github.com/project-everest/vale/blob/fstar/src/lib/math/Math.Lemmas.Int_i.fsti
assume val modulo_addition_lemma (a:int) (n:pos) (b:int) : Lemma ((a + b * n) % n = a % n)
assume val lemma_div_mod (a:int) (n:pos) : Lemma (a == (a / n) * n + a % n)

[@tcdecltime]
let lemma_poly_multiply_canon n p r h r0 r1 h0 h1 h2 s1 d0 d1 d2 hh =
  let r1_4 = r1 / 4 in
  let h_r_expand = (h2 * (n * n) + h1 * n + h0) * ((r1_4 * 4) * n + r0) in
  let hh_expand = (h2 * r0) * (n * n) + (h0 * (r1_4 * 4) + h1 * r0 + h2 * (5 * r1_4)) * n
    + (h0 * r0 + h1 * (5 * r1_4)) in
  let b = ((h2 * n + h1) * r1_4) in
  //modulo_addition_lemma hh_expand p b;
  assert (h_r_expand == hh_expand + b * (n * n * 4 + (-5)))
      by (canon_semiring int_cr)
