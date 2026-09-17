---
rg: 2
id: finite-cloning-undecidable-lamp-stabilizer-not-in-v
kind: route
title: "Q2 no: a coset-tree cloning system on finite groups with a non-recursive lamp stabilizer does not embed in V"
target: some-finite-cloning-system-group-does-not-embed-in-v
requires:
  - finite-cloning-groups-realize-every-lamplighter-over-thompson-f
---

This route uses the same witness as `finite-cloning-group-with-undecidable-lamp-stabilizer`
(section 3 there), which is restated here so that this route is self-contained.

1. Take `H_S = ⟨x_0^i y x_0^{-i} : i ∈ S⟩`, with `S ⊆ N` non-recursive and `y ≠ 1` in
   `F` supported in `[5/16, 7/16]`. Then `g_i := x_0^i y x_0^{-i} ∈ H_S ⇔ i ∈ S`,
   because the supports lie in the pairwise disjoint intervals `[2^{-i-2}, 2^{-i-1}]`.
2. The claim `finite-cloning-groups-realize-every-lamplighter-over-thompson-f` gives a
   cloning system on finite groups and `t ∈ T(G_*)` with `[t, f] = 1 ⇔ f ∈ H_S`.
   So `i ↦ [t, g_i]` is a computable family of words in `x_0, x_1, t`, and a word in the
   family is trivial iff `i ∈ S`. Hence `Γ_S = ⟨x_0, x_1, t⟩` has unsolvable word problem.
3. `V` is finitely generated with solvable word problem: elements act on finite binary
   words by prefix replacement, and there is an algorithm that multiplies reduced tree
   pair diagrams. A finitely generated subgroup of a group with solvable word problem has
   solvable word problem: write the generators as words in the generators of `V`.
   So `Γ_S` does not embed in `V`, and neither does `T(G_*) ⊇ Γ_S`.

This establishes `some-finite-cloning-system-group-does-not-embed-in-v`. Like the
coCF route, this route does not bear on Lehnert's conjecture: the witness is not coCF.
