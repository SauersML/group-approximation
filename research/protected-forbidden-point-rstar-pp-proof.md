---
rg: 2
id: protected-forbidden-point-rstar-pp-proof
kind: route
title: Protect one affine branch while excluding every forbidden source point
target: affine-safe-support-admits-a-tailored-rstar-cap-pp-lift
requires:
  - fano-cap-witness-sections-force-source-affine-safety
  - rstar-fano-ghost-affine-hull-criterion
  - dfnqxy-nonverify-rows-have-cap-safe-rstar-pp-compilers
---

Necessity is the established affine-hull sandwich.  For sufficiency put
`A=Aff(S)`.  For each `b notin C`, separate the affine translate `A+b` from
zero by a linear character `lambda=1` on that translate.  Define
`s=lambda(x+b)` with fixed-cap xor rows and express the equivalent clause
`s OR (x_1+b_1) OR ... OR (x_n+b_n)` by a 3-CNF chain.  On `A`, set every
chain witness to zero, so each 3-clause has a fixed true literal.  Encode a
3-clause by `exists t, R_*(t,a,b,c)`.  Every protected row is then an affine
map from `A` into `R_*`, hence has Fano-cap range.  Conjoining these private
gadgets over all forbidden `b` defines exactly `C` and concatenates their
cap-valued sections.

