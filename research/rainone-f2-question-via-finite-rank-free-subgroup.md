---
rg: 2
id: rainone-f2-question-via-finite-rank-free-subgroup
kind: route
title: Induce a free minimal action of F_n up to F_2 through the index n-1 embedding
target: rainone-free-minimal-f2-action-not-almost-unperforated
requires: [free-minimal-fn-cantor-action-not-almost-unperforated, induced-cantor-action-type-semigroup-matches-subgroup]
---

Let `F_n`, `2 <= n < infinity`, act freely and minimally on a Cantor space `X`
with `S(X, F_n)` not almost unperforated.  The Schreier formula gives a
subgroup of index `n - 1` in `F_2` that is free of rank
`(n - 1)(2 - 1) + 1 = n`, so `F_n` embeds in `F_2` with finite index.  By
`induced-cantor-action-type-semigroup-matches-subgroup` the induced action of
`F_2` on `F_2 x_(F_n) X` is a free minimal action on a Cantor space whose type
semigroup is isomorphic to `S(X, F_n)`, hence not almost unperforated.
