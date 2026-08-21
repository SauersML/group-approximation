---
rg: 2
id: leavitt-whitehead-20x20-compression-cell
kind: claim
title: A 20-by-20 Whitehead word implements the binary Leavitt corner endomorphism
artifacts:
  - research/artifacts/hilbert-hotel-st20-full-mf-radical-2026-08-21.md
  - GroupApproximation/Leavitt/Whitehead.lean
  - GroupApproximation/Leavitt/LeavittMatrixCompression.lean
---

For `R=L_2(F_2)` and `m=5`, the explicit inverse pair
`U=[[s0 I,s1 t0 I],[0,t1 I]]`,
`V=[[t0 I,0],[s0 t1 I,s1 I]]` satisfies `UV=VU=I`, and
`T=diag(U,V)` lies in `E_20(R)`.  It conjugates `diag(g,I)` to
`diag(qI+s0*g*t0,I)`, and conjugates `diag(I,h)` to
`diag(pI+q*h,h)` whenever `h` has central `F_2` coefficients.

The nonunital map `a |-> s0*a*t0` is additive and multiplicative, so it
induces `alpha:St_5(R)->St_5(R)` rootwise.  Consequently a finite family of
transport relators on a finite generating set forces conjugation by a lifted
`T` to equal `alpha` on the entire rank-five domain.
