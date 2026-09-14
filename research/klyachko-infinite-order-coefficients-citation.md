---
rg: 2
id: klyachko-infinite-order-coefficients-citation
kind: route
title: Import Klyachko's Theorem A from the published paper and check the syllable transfer
target: klyachko-kl-holds-when-all-coefficients-have-infinite-order
requires: []
artifacts:
  - research/artifacts/hl-kl-torsion-pins-2026-09-13.md
---

**Imported.** A. A. Klyachko, Comm. Algebra 21(7) (1993), 2555--2575, read from
the publisher PDF on 2026-09-13; the pins are in section 1 of the artifact.
Theorem A (p. 2556): "C1 is true, if all the coefficients of w have infinite
order, in particular, if G is torsion-free." Theorem 4 (p. 2573) proves it at
exponent sum one, and its proof concludes that the natural map `G -> K` is a
monomorphism. Exponent sum `-1` follows by replacing `w` with `w^(-1)`.

The car-crash propositions (Proposition 1 and 1a) and Lemma 2 are taken as
published and were not re-verified.

**Checked here: the hypothesis reaches Lemma 2.** Theorem 4 feeds Lemma 2 the
factors `a_i, b_i, c` of the form (1) from Lemma 3. It verifies the Lemma 2
hypotheses by the "simple fact": if `u in (A * B) \ A` and each factor of `u`
has infinite order, then `gp(A, u) = A * <u>`. Two points connect "each
coefficient of `w` has infinite order" to "each factor of `a_i` has infinite
order", with `A = P_(m-1)`, `B = G^[m]` (and symmetrically `G^[0] * R_m` for
`b_i`).

1. *Syllables are coefficients.* Rewrite `w t^(-1)` as a product of
   conjugates `t^(-j) g t^j`. Consecutive coefficients of a reduced word are
   separated by a nonzero power of `t`, so they land in different free factors
   `G^[j]` and never merge. The syllables of `v` in `*_j G^[j]` are therefore
   copies of the coefficients.

   Lemma 3 splits `v` into alternating factors of the amalgam
   `P_(s-1) *_(R_(s-1)) R_s` and shifts the `R_s`-factors by `phi^(-1)`. Both
   steps can be done on consecutive runs of syllables:
   - split between the last index-0 syllable of one run and the first
     index-`s` syllable of the next;
   - every run then contains a marked syllable, so it lies outside `R_(s-1)`;
   - the decomposition is reduced, so its length is the amalgam length and is
     minimal.

   Shifting indices never merges syllables. So each `a_i` has a normal form in
   `*_(j<=m) G^[j]` whose syllables are coefficient copies.

2. *Runs have infinite order.* A factor of `a_i` in `A * B` is either one
   syllable in `B` (a coefficient copy), or a run in the free product `A` of
   coefficient copies. In a free product, a nontrivial element of finite order
   is conjugate into a factor, `x = y z y^(-1)` with `z` of finite order. Merge
   the last syllable of `y` with `z` repeatedly; the normal form of `x` then
   contains a syllable conjugate in its factor to `z`, hence of finite order.
   So an element whose syllables all have infinite order has infinite order.

The simple fact itself is Klyachko's. A reduced word in `A` and powers of `u`
stays reduced because `u` is not in `A` and its factors do not cancel against
`A`; this is standard and was not re-derived.

**Trust surface.** Proposition 1a, Lemma 1a (Howie's van Kampen lemma) and
Lemma 2, as published. The syllable transfer above is written out. No novelty
is claimed: the import restores the scope of Klyachko's own Theorem A, which
main recorded only in its torsion-free form.
