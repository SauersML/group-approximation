---
rg: 2
id: cut-stabilizer-subgroups-of-el3-are-not-confined
kind: claim
title: The stabilizer of the half-orbit cut at a point, and so the locally finite tower unit groups, are not confined in EL_3(LC(X,F_2)⋊Z)
distinct_from:
  locally-constant-gl-n-subgroup-is-not-confined: that treats locally constant matrices through diagonal conjugators alone; this treats the larger cut stabilizer, which contains every Kakutani–Rokhlin tower unit group and needs a Neumann covering argument to remove diagonal survivors
---

**ESTABLISHED (unreviewed).**

**Setting.**
- `(X,T)` is an infinite minimal Cantor system, `R = LC(X,F_2) ⋊_T Z` and `G = EL_3(R)`.
- For `y ∈ X`, the orbit representation is `π_y(fu^k)δ_t = f(T^{t+k}y)δ_{t+k}` on `F_2^{(Z)}`.
- `S_y ≤ G` is the stabilizer of the two subspaces `V^{<0} ⊗ F_2^3` and `V^{≥0} ⊗ F_2^3`, where `V^{<0} = span{δ_t : t < 0}` and
  `V^{≥0} = span{δ_t : t ≥ 0}`. Equivalently, every entry `g_ij` maps `V^{<0}` into `V^{<0}` and `V^{≥0}` into `V^{≥0}`.

**Theorem.** `S_y` is not confined in `G`. So no subgroup of `S_y` is confined.

**Consequences.**
- Let `𝒫_n` be Kakutani–Rokhlin partitions whose bases contain `y`, and `A(𝒫_n)` the tower algebras spanned by
  `e_{T^aW}u^{a−b}`. Then `GL_3(A(𝒫_n)) ∩ G ≤ S_y`, because matrix units move orbit points within one column of the tower and
  `y` begins a column. So the locally finite groups `L_y = ⋃_n GL_3(A(𝒫_n)) ∩ G` are not confined. These are the unit groups
  `sk-characters-rigidity-b` uses.
- Together with `elementary-root-subgroups-over-crossed-products-are-not-confined`, `locally-constant-gl-n-subgroup-is-not-confined`
  and `topological-full-group-images-in-el3-are-not-confined`, none of the test subgroups listed in
  `subshift-elementary-groups-are-cstar-simple` is an obstruction to C*-simplicity (`cstar-simple-iff-amenable-subgroups-not-confined`).

**Proof:** `cut-stabilizer-subgroups-el3-not-confined-proof`.

**Review (sk-verify-13, 2026-09-13, `research/artifacts/sk-verify-13-2026-09-13-part1.md` §4):** PASS. Re-derived:
- the representation identity for `π_y`, and that `S_y` is a subgroup (the two subspaces are complementary);
- both cases of Lemma C, with window counts `|N_i − N_j| − w ≥ L+1`;
- Lemma D (B. H. Neumann's covering lemma), the conjugation formula of Lemma E, and the coset structure of the bad pairs;
- both cases of Lemma F, and the assembly `g = lc`;
- the inclusion `GL_3(A(𝒫)) ∩ G ≤ S_y` (`t` and `t+a−b` lie in one return interval, and `0` is an endpoint).

Wording: Lemma C uses that every `L+1` consecutive times contain a visit to `{r_{k_0} = 1}`.
