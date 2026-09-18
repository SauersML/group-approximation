---
rg: 2
id: boone-higman-via-local-boone-higman
kind: route
title: Realize one finite system, the relators of a decidable finitely presented envelope and one element of its simple subgroup, in a finitely presented simple group
target: boone-higman-conjecture
requires:
  - local-boone-higman-conjecture
  - local-boone-higman-iff-boone-higman
---

Let `G` be finitely generated with solvable word problem. By
`local-boone-higman-iff-boone-higman` (the implication (b) ⇒ (a) with
`𝒦 = fps`):
1. `G × Z ≤ S ≤ H`, with `S` a finitely generated simple group with solvable
   word problem (Thompson) and `H = ⟨x | r⟩` finitely presented with solvable
   word problem (Clapham).
2. For one `g = w(x) ≠ 1` in `S`, the system `r(y) = 1, w(y) ≠ 1` has the
   decidable model `H`. `local-boone-higman-conjecture` gives a model in some
   finitely presented simple group `K`, hence a homomorphism `φ : H → K` with
   `φ(g) ≠ 1`.
3. `S` is simple, so `φ` is injective on `S`, and `G ≤ K`.

This route supersedes `boone-higman-via-isolated-overgroup-and-local-boone-higman`:
it has the same open premise and drops `every-decidable-group-embeds-in-an-isolated-group`.
