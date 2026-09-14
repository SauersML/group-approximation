---
rg: 2
id: rank-models-give-no-hamming-models-through-vector-actions
kind: claim
title: A rank-approximate matrix model becomes a Hamming-useless permutation model on vectors
distinct_from:
  gap-sofic-approximations-are-local-embeddings: that says a sofic approximation inside gapped targets forces local embeddability; this computes the defect of the vector action and shows rank models never enter that regime at all.
artifacts:
  - research/artifacts/sk-sofic-embedding-a-rank-route-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `q` be a prime power and `g ∈ GL_N(F_q)`. In the permutation action of `GL_N(F_q)` on
`F_q^N`, the fixed-point set of `g` is `ker(g − 1)`, so the normalized Hamming distance from `g` to the identity is
`1 − q^(−rk(g−1))`. In particular every `g ≠ 1` moves at least a fraction `1 − 1/q` of the points.

**Consequence.** Let `Φ_i : S → GL_(N_i)(F_q)` have vanishing normalized rank defect,
`rk(Φ_i(st) − Φ_i(s)Φ_i(t))/N_i → 0` for `s,t` in a finite set. Whenever `Φ_i(st) ≠ Φ_i(s)Φ_i(t)`, the induced maps into
`Sym(F_q^(N_i))` have Hamming defect at least `1 − 1/q`. So a rank model of a group produces a sofic approximation only
when it is, for large `i`, an exact local embedding into the finite groups `GL_(N_i)(F_q)`, in which case the group is
LEF.

This is the reason linear soficity of the elementary groups over crossed products does not upgrade to soficity: the
approximations live in the rank metric, and the only algebraic way to make permutations out of them collapses the
information. It is the quantitative half of `gap-sofic-approximations-are-local-embeddings`.

Route: `rank-models-give-no-hamming-models-through-vector-actions-proof`.
