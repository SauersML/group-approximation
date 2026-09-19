---
rg: 2
id: non-hyperlinear-from-perfect-completeness-lcs-compiler
kind: route
title: Feed a perfect-completeness LCS compiler through the halting co-r.e. argument
target: non-hyperlinear-group
requires:
  - perfect-completeness-constant-soundness-lcs-compiler
  - re-oriented-lcs-compiler-gives-nonhyperlinear-group
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

With `(PC1)` and `(PC2)` in hand,
`re-oriented-lcs-compiler-gives-nonhyperlinear-group` produces a nonhalting
machine whose solution group keeps `J` and has quantum value at most
`1 - delta`; `perfect-lcs-gap-implies-nonhyperlinear` makes that group
nonhyperlinear.  This is the Taller--Vidick route with its missing
hypothesis isolated and its self-reference removed.
