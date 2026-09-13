---
rg: 2
id: marked-subshift-elementary-group-determines-language
kind: claim
title: The marked group EL_3(LC(X,F_q)⋊Z)/Z with its standard generators determines the language of the minimal subshift X
artifacts:
  - research/artifacts/un-open-5-marked-subshift-groups-2026-09-13.md
---

Fix a prime power `q` and a finite alphabet `A`. For an infinite minimal subshift `X ⊆ A^Z`, put
`R_X = LC(X,F_q) ⋊ Z`, `G_X = EL_3(R_X)` and `S_X = G_X/Z(G_X)`. Let `σ_X = (e_ij(s) Z)_(i≠j, s ∈ S_0)` with
`S_0 = {1, u, u^(-1), χ_[x_0=a] (a ∈ A)}`, plus a primitive element of `F_q` when `q` is not prime. Its index set
depends only on `(A, q)`.

For every word `w ∈ A^*` there is a group word `W_w` in those indices, independent of `X`, such that for every
infinite minimal `X ⊆ A^Z`:

`W_w(σ_X) = 1` in `S_X` iff `w ∉ L(X)`.

Concretely, `W_w` is a nested commutator word evaluating to `e_12(χ_[x_[0,|w|) = w])`. That element is central,
hence trivial in `S_X`, iff the cylinder of `w` is empty.

Consequence: `(S_X, σ_X)` determines `L(X)`, hence `X`.
