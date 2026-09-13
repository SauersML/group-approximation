---
rg: 2
id: marked-subshift-elementary-group-determines-language
kind: claim
title: The marked group EL_3(LC(X,F_q)⋊Z)/Z with its standard generators determines the language of the minimal subshift X
distinct_from:
  binary-subshifts-embed-in-three-marked-kazhdan-groups: that marks EL_3(LC(X,F_2)⋊Z) by three fixed matrix formulas and proves X ⊂ Y iff there is a marked epimorphism, so over F_2 the marking already determines X; this uses the standard elementary generators over every F_q and one fixed commutator word per cylinder.
  subshift-elementary-group-word-problem-degree: that already reduces L(X) to the word problem through computable cylinder-root words; this isolates that reduction as a statement about the marked group.
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

**Review (un-verify-open, 2026-09-13, `research/artifacts/un-review-open-2026-09-13-part1.md` §1.1): PASS.**
Lemma 1.1, the recursion `ω_ik(s m') = [ω_ij(s), ω_jk(m')]`, Lemma 2.2 (`u^(-t) χ_a u^t = χ_[x_t=a]` from
`u f u^(-1) = f∘T^(-1)`) and the scalar-centre step were re-derived. The substance is already on main over `F_2`
(both `distinct_from` entries); the new part is the arbitrary-`q`, fixed-word form.
