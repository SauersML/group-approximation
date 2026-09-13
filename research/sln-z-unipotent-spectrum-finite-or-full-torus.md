---
rg: 2
id: sln-z-unipotent-spectrum-finite-or-full-torus
kind: claim
title: For d >= 3, every representation of SL_d(Z) has column unipotent spectrum either the full torus or finite, and finite spectrum means a congruence quotient
distinct_from:
  bms-sln-z-representations-agree-with-algebraic-ones: that recovers algebraic representations from rational ones on finite-index subgroups; this is a spectral dichotomy for arbitrary unitary and C-star representations.
  sl4z-representations-have-sl2-invariant-vectors: that is the Magee-de la Salle theorem for finite-dimensional representations; this says which infinite-dimensional representations reduce to finite quotients, with no invariant-vector conclusion.
artifacts:
  - research/artifacts/sl4z-mf-corona-reduction-2026-09-13-part2.md
---

ESTABLISHED (unreviewed).  Setup:
- `d >= 3`.
- `sigma : C*(SL_d(Z)) -> B` is a unital *-homomorphism into a unital C*-algebra.  This
  covers unitary representations on Hilbert spaces and maps into matrix coronas.
- `Y subset T^(d-1)` is the joint spectrum of
  `sigma(u(v))`, `u(v) = I + sum_(i<d) v_i e_(i,d)`.

Then either `Y = T^(d-1)`, or `Y` is a finite set of torsion points.  In the second case
`sigma` factors through `C*(SL_d(Z/NZ))` for `N` the lcm of their orders.

**Model tests.**
- Finite-dimensional representations have finite `Y` and factor through congruence
  quotients, the Bass--Milnor--Serre fact that Magee--de la Salle use.
- The regular representation has Haar spectrum `Y = T^(d-1)`.
- The trivial representation has `Y = {0}`, with `N = 1`.

No novelty is claimed; the ingredients are elementary or classical.

Proof: `sln-z-unipotent-spectrum-finite-or-full-torus-proof`.
