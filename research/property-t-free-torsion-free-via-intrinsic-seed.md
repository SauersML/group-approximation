---
rg: 2
id: property-t-free-torsion-free-via-intrinsic-seed
kind: route
title: Route an intrinsically torsion-free MF-radical word and saturate it
target: property-t-free-torsion-free-full-mf-radical
requires:
  - torsion-free-fp-ah-mf-radical-seed
  - internal-torsion-free-single-word-router
  - torsion-free-mf-radical-routing-saturation
---

Choose `(E,d)` from the intrinsic seed and apply the internal router while
protecting `d`.  It supplies `q:E->>Q` with `q(d)!=1`,
`normalClosure_Q(q(d))=Q`, and all required two-generation, finite
presentation, torsion-free, and acylindrical-hyperbolicity clauses.

Apply `torsion-free-mf-radical-routing-saturation`.  It gives
`Rad_MF(Q)=Q` and the same conclusion for every nontrivial quotient of `Q`.
Every dependency in this route is stated without Property `(T)` and without
a caller-supplied literature premise.
