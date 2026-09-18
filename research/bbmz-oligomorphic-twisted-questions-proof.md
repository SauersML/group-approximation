---
rg: 2
id: bbmz-oligomorphic-twisted-questions-proof
kind: route
title: The clopen action of a finitely presented twisted Brin--Thompson group is oligomorphic with finitely presented finite-set stabilizers; Clapham handles the finitely presented hypothesis
target: bbmz-oligomorphic-and-twisted-questions-are-pbh-forms
requires:
  - twisted-btb-clopen-action-is-type-a
  - permutational-boone-higman-iff-full-cantor-hosts
  - twisted-brin-thompson-finite-presentation-criterion
  - clapham-fp-embedding-preserves-word-problem
  - bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh
  - boone-higman-implies-relative-permutational-bh
  - abstract-btb-pairs-fp-and-relatively-simple
  - a2-kernel-removal-iff-image-satisfies-pbh
---

**Step 1 (item 1).** Let `H ≤ Γ_0` with `Γ_0 ↷ S` of type (A). By
`twisted-brin-thompson-finite-presentation-criterion`, `D = SV_{Γ_0}` is finitely presented and
contains `Γ_0`, hence `H`. Let `Ω` be the proper nonempty clopen subsets of the Cantor cube `C^S`.
- *Oligomorphic.* By `twisted-btb-clopen-action-is-type-a` (item 3), two `k`-tuples in `Ω` lie in
  one `D`-orbit exactly when they have the same pattern of nonempty Boolean atoms. There are
  finitely many patterns for each `k`, so `D ↷ Ω` is oligomorphic. It is faithful (same node,
  item 2).
- *Finite-set stabilizers.* Let `F ⊆ Ω` be finite, and `P ≤ Stab_D(F)` the pointwise stabilizer;
  it has finite index, as `Stab_D(F)` acts on `F` through a finite group. The atoms
  `A_1, ..., A_m` of `F` partition `C^S` into nonempty clopen sets, and `P` is exactly the subgroup preserving every atom (a
  permutation preserving each `U ∈ F` preserves each Boolean combination, and conversely each
  `U` is a union of atoms). Since `D` is full (`permutational-boone-higman-iff-full-cantor-hosts`,
  proof Step 1), such `g` is the product of its restrictions, each extended by the identity, so
  `P = D(A_1) × ... × D(A_m)`, where `D(X)` is the subgroup supported in `X`. Since `D` is clopen
  transitive (same proof, Step 2), Step 3 of `fp-clopen-transitive-full-cantor-group-type-a-proof`
  gives `D(X) ≅ D` for every nonempty clopen `X`; it applies to each `A_i`
  because the atoms are nonempty clopen sets. So `P ≅ D^m` is finitely presented, and so is
  its finite-index overgroup `Stab_D(F)`.

**Step 2 (item 2).** *Question 1.5 ⇒ PBH.* Let `H` be finitely generated with solvable word
problem. By `clapham-fp-embedding-preserves-word-problem`, `H` embeds in a finitely presented group
`H'` with solvable word problem. A positive answer embeds `H'` in a finitely presented group acting
faithfully and oligomorphically with finitely generated finite-set stabilizers; oligomorphic
gives finitely many orbits of two-element subsets, and one-point stabilizers are finitely
generated, so this action is of type (A). *PBH ⇒ Question 1.5.* A finitely presented group with
solvable word problem is finitely generated, so PBH puts it in `B_A`, and Step 1 applies.

**Step 3 (item 3).** Let `S_0` be finitely presented and simple.
- If `S_0 ≤ SV_G` with `G ↷ S` faithful and `SV_G` finitely presented, then by
  `twisted-brin-thompson-finite-presentation-criterion` the action `G ↷ S` has finitely presented
  `G`, finitely generated stabilizers and finitely many orbits of two-element subsets, so it is of
  type (A). By `twisted-btb-clopen-action-is-type-a` so is `SV_G ↷ Ω`, hence `S_0 ∈ B_A`.
- Conversely, if `S_0 ≤ Γ_0` with `Γ_0 ↷ S` of type (A), then `S_0 ≤ SV_{Γ_0}`, which is finitely
  presented, simple, and a twisted Brin--Thompson group of a faithful action.

So the faithful reading of Question 1.6 is "every finitely presented simple group lies in `B_A`",
which is item 2 of `bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh`; the other equivalents are
listed there (BFFHZ Theorem C and their text around Question 3.4).

**Step 4 (items 4 and 5).** A finitely presented simple group satisfies Boone--Higman trivially, so
FFWZ Theorem C (`boone-higman-implies-relative-permutational-bh`) gives a type [A_2] action
`G ↷ S` with `S_0` sharply embedded in `(G, K)`, `K` the kernel.
`abstract-btb-pairs-fp-and-relatively-simple` makes the abstract `SV_G` finitely presented and
relatively simple over `SK_G`, and embeds `G`. When `K ≠ 1`, the proper normal subgroup `SK_G` contains `λ(K) ≠ 1`, so `SV_G`
is not simple. Item 5 is `a2-kernel-removal-iff-image-satisfies-pbh`
applied to this action.
