---
rg: 2
id: sturmian-language-is-turing-equivalent-to-angle-proof
kind: route
title: Letter counts approximate α; circular order of −tα cuts the circle into gaps with constant codings
target: sturmian-language-is-turing-equivalent-to-angle
requires: [continuum-many-infinite-minimal-binary-subshifts]
artifacts:
  - research/artifacts/un-open-5-word-problem-degrees-2026-09-13.md
---

Artifact §2.
1. **α from the language.** By the counting identity (route of `continuum-many-infinite-minimal-binary-subshifts`,
   item 3), a legal word of length `n` has `k` ones with `|k/n − α| < 1/n`. Query all `2^n` words, take a legal
   one, and read `k`. For irrational `α`, rational approximations with known error compute the binary expansion.
2. **The language from α.** The points `p_t = −tα mod 1`, `0 ≤ t ≤ n`, are distinct. Their circular order is
   computable relative to `α`.
   - On each open gap, `y + tα mod 1` avoids `0` and `1−α` for `t < n`, since those would force `y = p_t` or
     `y = p_(t+1)`. So `c(y)_[0,n)` is constant there, and is computed from a rational interior point by strict
     comparisons.
   - Nonempty cylinder sets are unions of half-open gap arcs, so they contain open gaps. By shift invariance,
     `L_n(X_α)` is exactly the list of gap codings.
