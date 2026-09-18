---
rg: 2
id: ascending-hnn-of-free-groups-bh-proof
kind: route
title: Extend the endomorphism to an isomorphism of finite-index subgroups of F * Z by M. Hall's theorem, embed the mapping torus in the resulting generalised Baumslag--Solitar group over F_2, and apply BLIW
target: ascending-hnn-of-free-groups-satisfy-boone-higman
requires:
  - bliw-locally-finite-tree-actions-embed-in-fp-simple-groups
artifacts:
  - research/artifacts/gq-bh-bh-free-05-ascending-hnn.md
---

Full details, with the verbatim BLIW quotes and the source hash, are in the linked artifact.
Notation: `F = F(a_1..a_n)`, `n >= 1`, `K = φ(F)`, `Y = F * <b>`.

1. **Hall.** Fold the generators of `K` to a finite labelled graph `Γ_K` on vertex set `V`.
   Complete each letter's partial injection to a permutation of `V`. The result is a
   `|V|`-sheeted cover, so `C_2 := π_1` has index `d = |V|` in `Y`. A maximal tree of `Γ_K` is
   a maximal tree of the cover, so `C_2 = K * L`.
2. **Equal index.** `C_1 = ker(Y -> Z/d; a_i -> 0, b -> 1)`. Using the maximal tree of
   `b`-edges, `C_1 = F * R`.
3. **Extension.** By Schreier both groups have rank `dn + 1`, so `rank R = rank L`. Take
   `Φ = φ * α` for any isomorphism `α : R -> L`. Then `Φ : C_1 -> C_2` is an isomorphism with
   `Φ|_F = φ`.
4. **Class.** `H = Y*_Φ` has free vertex and edge groups of ranks `n + 1 >= 2` and
   `dn + 1 >= 2`, with both edge inclusions of index `d`. So `H ∈ BS_{F_2}`.
5. **Injective.** Let `θ(t) = s` and `θ|_F = id`. Then `θ` is injective on each
   `t^-k F t^k`, hence on the increasing union `B`. The map `H -> Z` (`s -> 1`, `Y -> 0`)
   composes with `θ` to `Γ -> Γ/B ≅ Z`, so `ker θ ⊆ B`, and therefore `ker θ = 1`.
6. **Conclude.** BLIW `thm:free-groups` embeds `H`, hence `Γ`, in a simple group of type
   `F_∞`. By `rem:burger-mozes`, `H` embeds in a finitely presented group with an action of
   type (A). These are the §12.5 results of the paper whose Theorems B, 10.5 and C are imported
   in `bliw-locally-finite-tree-actions-embed-in-fp-simple-groups`. They are read here at
   source from the TeX e-print. ∎
