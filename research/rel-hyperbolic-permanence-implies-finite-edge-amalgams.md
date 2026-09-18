---
rg: 2
id: rel-hyperbolic-permanence-implies-finite-edge-amalgams
kind: claim
title: Boone--Higman permanence under relative hyperbolicity implies closure under amalgams and HNN extensions over finite subgroups, and its B_A form settles the open conjugacy step
distinct_from:
  rel-hyperbolic-bh-permanence-implies-free-product-closure: that derives free-product closure (trivial edge group); this derives closure over every finite edge group, and treats the B_A form too.
  free-permutational-products-preserve-pbh: that reduces B_A-closure over finite edge groups to a conjugacy step, which is open; this shows the relatively hyperbolic permanence statement would settle that step.
---

**ESTABLISHED** by the argument below (lane proof, elementary, not reviewed; no priority
claimed).

`𝓑` is the class of groups that embed in a finitely presented simple group. `B_A` is as in
`boone-higman-type-a-class-closed-under-finite-extensions`.

## Statement

1. If `rel-hyperbolic-groups-with-bh-peripherals-satisfy-bh` holds, then for finitely
   generated `A, B ∈ 𝓑` and a finite group `F` with embeddings `F → A`, `F → B`, the
   amalgam `A *_F B ∈ 𝓑`. Likewise, for an isomorphism `θ` between finite subgroups of `A`,
   the HNN extension `A *_θ ∈ 𝓑`.
2. The same holds with `𝓑` replaced by `B_A` throughout, for the **B_A form** of the
   permanence statement: `G` finitely generated with solvable word problem and hyperbolic
   relative to finitely generated `P_i ∈ B_A` implies `G ∈ B_A`. In particular that form
   implies the open conjugacy step of `free-permutational-products-preserve-pbh`, parts 4
   and 5: any `A, B ∈ B_A` embed in a common `B_A`-group compatibly with a given
   identification of finite subgroups.

So each form of the permanence statement is at least as hard as the corresponding
finite-edge amalgam closure. Neither of those closures is known.

## Proof

Let `Γ = A *_F B` or `A *_θ`, and let `T` be its Bass--Serre tree.
- `Γ` is finitely generated.
- `Γ` has solvable word problem. It is built from groups with solvable word problem along
  finite subgroups, whose membership is decidable, so normal forms can be computed
  (standard).
- `Γ` acts on `T` with finite edge stabilizers (conjugates of the finite edge groups) and
  with one or two orbits of edges.
- A tree is hyperbolic, and it is fine because it has no circuits. So by Bowditch's
  fine-graph definition of relative hyperbolicity (not re-read here), `Γ` is hyperbolic
  relative to its infinite vertex stabilizers. Up to conjugacy these are `A` and `B`
  (resp. `A`), with finite ones dropped.
- These peripheral subgroups are finitely generated and lie in `𝓑` (resp. `B_A`). If all
  of them are finite, then `Γ` is virtually free, hence hyperbolic, and
  `hyperbolic-groups-satisfy-boone-higman` (resp. `hyperbolic-groups-lie-in-the-permutational-class`)
  applies directly.

So the permanence statement applies to `Γ`. For item 2, the part 4 and 5 equivalences of
`free-permutational-products-preserve-pbh` then give the compatible embeddings.
