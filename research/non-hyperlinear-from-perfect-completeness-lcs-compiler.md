---
rg: 2
id: non-hyperlinear-from-perfect-completeness-lcs-compiler
kind: route
title: Feed a perfect-completeness LCS compiler through an explicit proof-search fixed point
target: non-hyperlinear-group
requires:
  - perfect-completeness-constant-soundness-lcs-compiler
  - re-oriented-lcs-compiler-gives-nonhyperlinear-group
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

With `(PC1)` and `(PC2)` in hand,
`re-oriented-lcs-compiler-gives-nonhyperlinear-group` effectively constructs
a nonhalting machine whose solution group keeps `J` and has quantum value
strictly below one; `perfect-lcs-gap-implies-nonhyperlinear` makes that group
nonhyperlinear.  This is the Taller--Vidick route with its missing
hypothesis isolated.  The fixed point enumerates group proofs only; it does
not search matrices or depend on an unknown quantitative threshold.
