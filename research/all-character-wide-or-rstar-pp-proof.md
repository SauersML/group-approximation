---
rg: 2
id: all-character-wide-or-rstar-pp-proof
kind: route
title: Route every affine support through one character of a universal wide OR
target: boolean-relations-have-affine-complete-rstar-pp-gadgets
requires:
  - affine-safe-support-admits-a-tailored-rstar-cap-pp-lift
  - dfnqxy-nonverify-rows-have-cap-safe-rstar-pp-compilers
  - fano-cap-witness-sections-force-source-affine-safety
  - rstar-fano-ghost-affine-hull-criterion
---

For each forbidden source point `b`, compute all nonzero characters of
`u=x+b` and take their wide OR.  This is exactly `u!=0`.  In its fixed 3-CNF
chain, an affine set avoiding zero has one character constantly equal to
one; set chain bits to one before that literal and zero after it.  Each
ternary clause then has a fixed true literal.  The encoding
`exists t, R_*(t,a,b,c)` is exact for ternary OR, and its protected row is an
affine image into `R_*`, hence a cap.  Conjoin the gadgets over all forbidden
points.  Necessity is the affine-hull sandwich.
