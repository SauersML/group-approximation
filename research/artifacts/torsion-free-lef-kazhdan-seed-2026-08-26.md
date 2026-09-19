# Torsion-free LEF Kazhdan non-RF seed — source and construction audit

Date: 2026-08-26

## Primary sources checked

1. Andreas Thom, *Examples of hyperlinear groups without factorization
   property*, arXiv:0810.2180, Section 2.1 and Lemmas 2.1 and 2.3:
   https://arxiv.org/abs/0810.2180

   Thom constructs the positive-characteristic parabolic quotient, proves
   property `(T)`, and proves LEF by replacing the Laurent variable with a
   long root of unity in a finite ring.  His central kernel has order `p`.

2. Yoshikata Kida and Robin Tucker-Drob, *Groups with infinite FC-center
   have the Schmidt property*, arXiv:1901.08735, Appendix A:
   https://arxiv.org/abs/1901.08735

   The appendix writes the characteristic-zero `5x5` parabolic explicitly
   and proves, using the universal-lattice and relative-`(T)` inputs, that it
   has property `(T)`.  It also observes that quotienting an arbitrary
   subgroup of its additive centre preserves property `(T)` and realizes any
   prescribed countable abelian centre.

3. Mikhail Ershov and Andrei Jaikin-Zapirain, *Property (T) for
   noncommutative universal lattices*, Invent. Math. 179 (2010), arXiv source:
   https://arxiv.org/abs/0809.4095

   This supplies property `(T)` for the elementary rank-three group over the
   finitely generated Laurent ring.  Kassabov's relative-`(T)` input is the
   same one used explicitly in the Kida--Tucker-Drob appendix.

## New assembly

Take `R=Z[t,t^(-1)]`, the appendix parabolic `H(R)`, its central root
`C=(R,+)`, and the pure subgroup `C_+=Z[t]`.  The quotient `J=H/C_+` is
Kazhdan.  Thom's periodic-window proof works over characteristic zero after
also reducing coefficients modulo a sufficiently large prime, so `J` is LEF.

The diagonal Laurent shift induces a surjective noninjective endomorphism of
`J`; its kernel contains the infinite-order class of `t^(-1)`.  The usual
repetition of equal-index kernels puts that class in the finite residual.

The quotient by the complete central root is the linear semidirect product
`EL_3(R) semidirect (R^3 x R^3)`.  Choose a torsion-free finite-index subgroup
there and take its preimage in `J`.  The preimage is an extension of that
torsion-free group by the free abelian negative Laurent tail, hence is
torsion-free.  It remains finite-index Kazhdan and LEF.  The central invisible
element remains finite-residually invisible by the finite-index core argument.

## Trust boundary

This is a paper-level construction, not a new Lean development.  The only
adaptations beyond the cited texts are elementary:

- reduce integer coefficients modulo a large prime in Thom's finite-window
  model;
- apply Selberg's lemma to the explicit linear centre-free quotient; and
- use the core of a finite-index subgroup to retain a central
  finite-residual element.

No claim is made here that the seed is finitely presented, has full MF
radical, or already carries the automorphism/compression package needed by
`torsion-free-sofic-exact-mf-radical-over-z`.
