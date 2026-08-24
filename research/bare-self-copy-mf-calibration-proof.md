---
rg: 2
id: bare-self-copy-mf-calibration-proof
kind: route
title: Combine the exact self-copy kill with the amenable amalgam and fiber-swap model
target: bare-self-copy-mf-calibration
requires:
  - compression-defect-dies-in-finite-dimensions
  - amenable-amalgams-have-mf-full-cstar
  - amalgam-torsion-permanence-needs-no-cyclic-reduction
artifacts:
  - notes/FINITE_PACKET_SELF_COPY_COLLAPSE.md
  - GroupApproximation/Criterion/FiniteDimensionalKill.lean
  - GroupApproximation/Algebra/DyadicRationals.lean
  - experiments/verify_bs12_calibration.py
---

Use the amalgam presentation

```text
BS(1,2) *_<a²> <a²,p | [p,a²]=1>.
```

The second factor is `Z²`; amalgam normal form makes `[p,a]` nontrivial, and
torsion-freeness follows from the existing unconditional torsion-permanence
theorem.  The exact compression detector applies to `<a>` and its child
`<a²>`, so every finite-dimensional representation kills `[p,a]`.  Both
factors are amenable, hence Shulman's theorem makes the full group C-star
algebra MF.

For the coordinate escape, take `zeta_m=exp(pi i/m)`, let
`A_m e_j=zeta_m^j e_j`, let `T_m` send `e_(2r)` to `e_r` and `e_(2r+1)` to
`e_(m+r)`, put `B_m=T_m A_m T_m*`, and let `P_m` swap the two `m`-point
fibers.  Direct evaluation gives

```text
||B_m-A_m²|| = 2 sin(pi/(2m)),
[P_m,A_m²]=1,
||[P_m,B_m]-1|| = 2 sin(pi/(2m)),
P_m A_m P_m* = -A_m.
```

Both clocks have simple spectrum consisting of all `2m`-th roots, so their
generated C-star algebras are literally the same diagonal algebra.  The
surviving `-1` commutator proves that algebra equality and approximate child
commutation still do not control distance to the full commutant.
