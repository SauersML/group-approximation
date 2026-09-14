---
rg: 2
id: subshift-elementary-group-simple-via-local-annihilation
kind: route
title: The subshift crossed product has local annihilation, so the ring criterion gives simplicity with no towers
target: subshift-elementary-group-is-simple-modulo-centre
requires: [local-annihilation-makes-projective-el-simple, minimal-subshift-algebra-is-simple-lef-ring]
artifacts:
  - research/artifacts/sk-general-master-proposal-2026-09-13.md
---

A third derivation of the target, with no tower subrings and no finite simple groups.
- Lane: sk-general-master, 2026-09-13.
- Status: UNREVIEWED, queued with sk-referee-1.
- It matches the Lemma 2 check in `research/artifacts/sk-proof-minimal-conceptual-proposal-2026-09-13.md`.

Put `R = LC(X,F_q) ⋊ Z` and `G = EL_3(R)`.

1. **`R` is simple, with centre `F_q`.** This is item 2 of `minimal-subshift-algebra-is-simple-lef-ring`. Item 1 gives
   a finite ring generating set.
2. **`R` has local annihilation, in the additive form.** Let `F ⊆ R` be finite, with `u`-exponents at most `w`.
   - For `x ∈ X`, pick `y ∉ {T^j x : |j| ≤ w}`, possible since `X` is infinite, and a clopen `W ∋ y` missing that
     finite set.
   - By continuity of the `T^j`, pick a clopen `V ∋ x` with `W ∩ T^jV = ∅` for all `|j| ≤ w`, `j = 0` included.
   - Every clopen subset of `V` keeps the property with the same `W`. By compactness, finitely many such `V` refine to
     a clopen partition `𝒫` of `X`.
   - For `V ∈ 𝒫` and `r ∈ R`, put `s = e_V r` and `t = e_W`. Then `ts = e_{W∩V} r = 0`. For `f = Σ_j f_j u^j ∈ F`,
     `tfs = Σ_j f_j e_W e_{T^jV} u^j r = 0`, since `u^j e_V = e_{T^jV} u^j`.
   - `Σ_{V∈𝒫} e_V = 1`, so the elements `e_V r` span `R` additively. So they generate `R` as a non-unital ring, which
     is the Lean predicate `LocalAnnihilation`.
3. **Normal subgroups.** By `local-annihilation-makes-projective-el-simple` with `n = 3`, every normal subgroup of
   `G` is central or `G`, and `Z(G) ⊆ Z(R)^× I_3 = F_q^× I_3`.
4. **The listed consequences.**
   - `G` is finitely generated: the `e_ij(s)`, with `s` running over the generating set of item 1, generate `G`, by
     `e_ij(r+s) = e_ij(r)e_ij(s)` and `e_ij(rs) = [e_ik(r), e_kj(s)]`.
   - `G/Z(G)` is infinite: `e_12(LC(X,F_q))` is infinite and meets `Z(G)` trivially.
   - So `G/Z(G)` is infinite, finitely generated and simple.
   - `G` has no nontrivial finite quotient. If `G → Q` is onto with `Q` finite, its kernel is central or all of `G`. A
     central kernel would make the infinite group `G/Z(G)` a quotient of `Q`. So the kernel is `G` and `Q` is trivial.

The explicit extraction behind step 3 is written out in `local-annihilation-el-simplicity-explicit-extraction`.
