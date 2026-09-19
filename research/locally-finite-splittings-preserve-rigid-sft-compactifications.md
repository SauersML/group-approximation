---
rg: 2
id: locally-finite-splittings-preserve-rigid-sft-compactifications
kind: claim
title: A finite graph of groups with finite-index edge groups has a quantum-rigid SFT compactification as soon as one vertex group does; so BS(m,n), all GBS groups, mapping tori, polycyclic groups and finite-index overgroups lie in the class 𝒞
distinct_from:
  tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts: that glues over a free product, where vertex cosets have infinitely many edges and each needs a seed marking its exit, so every vertex group must be in 𝒞; this glues over a locally finite tree, where the exit is a finite pointer label, so only one vertex group needs a compactification and the others may be arbitrary.
  quantum-rigidity-is-product-stable: that closes 𝒞 under direct products; this closes it under finite-index HNN extensions and amalgams, which give non-product, non-residually-finite and exponentially distorted groups.
  decidable-groups-embed-in-rigid-sft-compactification-groups: that is premise (★𝒞) for all decidable groups, still open; this settles its listed test cases BS(1,2) and H_3(Z) and shows which splittings (★𝒞) can ignore.
---

**ESTABLISHED** by `locally-finite-splittings-rigid-compactification-proof` (lane bh-invent-03, 2026-09-18;
elementary lane proof, not reviewed; no priority claimed). The class `𝒞` and SFT compactifications (seed pattern,
conditions C1, C2) are as in `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`. Quantum rigidity is
Q1–Q3 of `fp-v-times-subshift-full-groups-force-quantum-rigidity`.

## Statement

Let `𝔾` be a finite connected graph of finitely generated groups. Assume each edge group has finite index in both
adjacent vertex groups, which is exactly the condition for a locally finite Bass–Serre tree `T`. Put
`Λ = π_1(𝔾)`, and suppose one vertex group `A` lies in `𝒞` via `(Y_A, π_A)`.

Then `Λ ∈ 𝒞`. There is an SFT `Y` over `Λ` with a seed such that:
- (C1) the seed cylinder is one point `y_*`, with trivial stabilizer;
- (C2) `Y` is the orbit closure of `y_*`;
- (R) `Y` is `D`-quantum rigid, for all large `D`, over every field over which `Y_A` is.

The other vertex groups need not be in `𝒞`. `Λ` is finitely presented iff the vertex groups are.

## Corollaries

The last one needs `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`.

1. **Finite-index overgroups.** If `A ∈ 𝒞` and `[B : A] < ∞`, then `B ∈ 𝒞`. Write `B = A *_A B`: the tree is a
   finite star.
2. **Mapping tori.** If `A ∈ 𝒞` and `φ ∈ Aut(A)`, then `A ⋊_φ Z ∈ 𝒞`: the tree is a line. Consequences:
   - `H_3(Z) = Z^2 ⋊ Z` is in `𝒞`, and so is every poly-`Z` group. With 1, so is every polycyclic-by-finite
     group.
   - Every `F_n ⋊ Z` is in `𝒞`, as is every `A ⋊ Z` over a free product of members of `𝒞`.
3. **Finite-index HNN extensions and amalgams.**
   - `A*_{φ : C -> C'} ∈ 𝒞` whenever `C, C'` have finite index in `A`.
   - Hence every `BS(m, n) = Z*_{mZ -> nZ}`, and every generalized Baumslag–Solitar group, is in `𝒞`. This
     includes non-residually-finite and non-Hopfian ones such as `BS(2, 3)`.
4. **Recovering the basic members.** `Z` (a loop at the trivial group), `F_n` and virtually free groups are the
   case where every vertex group is finite. For `Z` the construction reproduces `C_Z`.
5. **Minimal SFTs.** For every group `Λ` above, `Λ * Z` carries a minimal, topologically free, quantum-rigid SFT.

## What this means for (★𝒞)

(★𝒞) asks for a finitely presented `Λ_0 ≥ G` in `𝒞`.
- **Locally finite splittings are free.** They can be ignored. So can infinite-valence free products, by tree gluing.
- **Where coordinates are still needed.** A coordinate system is needed only on one vertex group of a splitting.
  What remains uncovered is:
  - (i) splittings over **infinite-index** edge groups other than the trivial group;
  - (ii) groups with **no** splitting, such as the canonical Kazhdan inputs `H_Γ`, lattices and one-ended hyperbolic
    groups.
- **Kazhdan inputs are untouched.** An (FA) subgroup lies in a vertex group, and here the vertex groups are
  commensurable with `A`. So this closure, like `×` and `*`, adds no new Kazhdan inputs.
- **What it does show.** `𝒞` is not tied to products, residual finiteness or undistorted geometry. The
  test cases `BS(1,2)` and `H_3(Z)` of `decidable-groups-embed-in-rigid-sft-compactification-groups` are in `𝒞`.

## Lesson for general BH

A coordinate system with a unique origin spreads for free along any **locally finite** tree. The pointer "which
neighbour leads to the origin" is a finite label, and each vertex coset carries that label unchanged along its own
group.
- **Rigidity along the tree.** It is compression along monotone chains, as in the free-group boundary shift.
- **Rigidity inside a coset.** One vertex group's own rigid compactification supplies it.
- **Condition (C).** In the language of `extension-rigidity-is-base-centrality-plus-pointwise-rigidity`, the
  tree-pointer base is automatically central.

So the E1′+E2 gate (★𝒞) lives entirely in two places: infinite-index edge groups, and groups with no splitting.
The natural next invention is a **relative seed**: an SFT on `A` whose seed-forced point has stabilizer exactly
`C ≤ A`, so that its orbit is `A/C`. With relative seeds, HNN extensions over infinite-index `C` would enter `𝒞`.
Those are the extensions that Higman-type embeddings are built from.
