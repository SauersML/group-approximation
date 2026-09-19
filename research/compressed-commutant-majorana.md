---
rg: 2
id: compressed-commutant-majorana
kind: claim
title: A Majorana in the compressed relative commutant moved anticommutingly by Gamma
distinct_from:
  kun-thom-clifford-relative-wall: That is the finite matrix endpoint stated with two normalized-Hilbert--Schmidt conditions on a family of almost representations; this is its exact algebraic content after the compressor automorphism has been divided out, a single involution in one relative commutant with a one-step Gamma-conjugation.
  kun-thom-clifford-crossed-product-ce: That asks for Connes embeddability of the whole Clifford crossed product; this asks only for one involution in one relative commutant of an arbitrary Connes-embeddable model.
artifacts:
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

Find a Connes-embeddable finite tracial von Neumann algebra `M`, a
homomorphism `pi:G->U(M)`, an element `gamma in Gamma`, and a self-adjoint
involution

```text
w in M cap pi(t Gamma t^(-1))'
```

such that `w` anticommutes with `pi(gamma) w pi(gamma)^*`.

The compressor `t` enters only through the subgroup `Gamma_1=t Gamma t^(-1)`,
whose `Gamma`-coset space is the orbit `Gamma/Gamma_1` of the distinguished
site.  By `commutator-compressor-carries-no-wall` the resulting commutant
growth must have infinite index at some positive elementary transvection
compressor, so `w` cannot be a finite lamp over a finite orbit.  The
model-side mechanism is available: `compressor-fixed-site-growth-infinite`
shows both candidate compressors gain infinitely many `Gamma`-fixed sites,
for every invariant graph.

## Acceptance test for block-monomial candidates

I asked the wreath lane whether `block-monomial-coordinate-collapse` extends
from abelian lamps in a coarse diagonal to Clifford lamps.  It was answered
(`clifford-diagonal-lamp-subspace`, proof in
`notes/TRUE_CLIFFORD_BLOCK_MONOMIAL_LAMP_SUBSPACE.md`): **half extends, and
the half that fails is the informative one.**  The result is a constraint on
this target, not a refutation of it.

*What extends.*  The permutation-part estimate never uses commutativity, so
permutation parts still form a homomorphism, and since the Clifford sign is
scalar hence diagonal it factors through the wreath.  The site action is
recoverable that far.

*What fails.*  In the abelian case faithfulness on the lamps was free,
because the lamps *were* diagonal and their permutation parts trivial.
Clifford lamps are monomial with **nontrivial** permutation parts, so the
permutation-part map can kill lamp words and no separated pair survives to
contradict anything.  Under Jordan--Wigner this is structural, not a bad
choice of coordinates: the two Majoranas at a site differ by `X` versus `Y`
against a common `Z`-tail, so they share a permutation part and their product
is killed.

*The test.*  The obstruction is the single computable invariant

```text
S = {finite F <= X : the product of the lamp images over F is diagonal},
```

a `G`-submodule of `F_2[X]` under symmetric difference.  Every block-monomial
Clifford model has `S != 0`.  If `S` contains a singleton it is everything, by
transitivity; and the augmentation kernel is the natural proper candidate, in
which case the induced map factors through `C_2 x G` and is again lamp-blind.
So a candidate model of this kind must be checked by computing `S`, and in
both structurally available cases the permutation part carries no lamp
information — meaning whatever hyperlinearity such a model witnesses is
carried entirely by the fiber unitaries, which returns the question to
`fiber-masa-free-cocycle` one level up.
