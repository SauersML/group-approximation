---
rg: 2
id: rank-models-give-no-hamming-models-through-vector-actions-proof
kind: route
title: Counting the fixed vectors of a linear map
target: rank-models-give-no-hamming-models-through-vector-actions
requires: []
artifacts:
  - research/artifacts/sk-sofic-embedding-a-rank-route-2026-09-13.md
---

1. **Fixed points.** For `g ∈ GL_N(F_q)` acting on `V = F_q^N`, `gv = v` says `(g−1)v = 0`, so the fixed set is the
   subspace `ker(g−1)`, of size `q^(N − r)` with `r = rk(g−1)`. The normalized Hamming distance from `g` to the identity
   in `Sym(V)`, `|V|` points, is therefore `1 − q^(−r)`. For `g ≠ 1` we have `r ≥ 1`, so the distance is at least
   `1 − 1/q`.
2. **The defect.** Put `g = Φ_i(st)^(-1) Φ_i(s) Φ_i(t)`. Then `g − 1 = Φ_i(st)^(-1)(Φ_i(s)Φ_i(t) − Φ_i(st))`, and
   multiplying by an invertible matrix does not change the rank, so `rk(g−1) = rk(Φ_i(s)Φ_i(t) − Φ_i(st))`. Applying 1,
   the permutation defect is `1 − q^(−rk)`, which is at least `1 − 1/q` whenever the rank is positive, however small the
   normalized rank `rk/N_i` is.
3. **The dichotomy.** A sofic approximation needs the permutation defect to go to `0`, so for each pair `s,t` in the
   finite set and all large `i` the rank defect is exactly `0`, i.e. `Φ_i` is multiplicative on that finite set. The
   same argument with `Φ_i(s) ≠ 1` in place of the defect gives injectivity. So the maps are local embeddings into
   `GL_(N_i)(F_q)` and the group is LEF.

**Model tests.** `q = 2`, `N = 1`: the group is trivial and the statement is vacuous. An exactly multiplicative model of
a LEF group has rank defect `0` and Hamming defect `0`, as it must. A rank model of a non-LEF group, for instance the
Følner models of an amenable non-residually-finite crossed product, has some nonzero rank defect at every stage, and the
vector action then has Hamming defect at least `1/2` there, so it is not a sofic approximation.
