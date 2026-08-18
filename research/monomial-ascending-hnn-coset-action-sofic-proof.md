---
rg: 2
id: monomial-ascending-hnn-coset-action-sofic-proof
kind: route
title: Separate every monomial self-image iterate by finite ring truncations, then invoke the all-iterates criterion
target: monomial-ascending-hnn-coset-action-sofic
requires: [ascending-hnn-action-iff-iterated-cosets]
artifacts:
  - research/artifacts/ascending-hnn-iterated-coset-solution-2026-08-18.md
  - docs/FALSE_POSITIVE_CORE_IS_SOFIC.md
---

## Why sufficient

For each `m`, write `R_m=k[A^m N^d]`.  Because `A` is injective on `Z^d`,
`A^m N^d` is a free commutative monoid and `R_m` is a polynomial ring.
The image of the elementary group is `EL_r(R_m)=SL_r(R_m)`.

Given `g` outside this subgroup, some entry `f` lies outside `R_m`.  Choose a
monomial in the support of `f` whose exponent is outside `A^m N^d`, and reduce
modulo `(x_1^M,...,x_d^M)` with `M` larger than every exponent coordinate in
`f`.  The chosen monomial survives as a basis vector outside the image of
`R_m`, so the resulting finite matrix quotient separates `g` from the whole
self-image.  Hence `alpha_A^m(Gamma)` is separable in `Gamma` for every `m`.

Separable stabilizers give exact finite Schreier models of each
`Gamma/alpha_A^m(Gamma)`.  The prerequisite theorem converts those models into
a sofic model of the full ascending-HNN coset action.  Section 5 of the
artifact gives the entry-by-entry proof.
