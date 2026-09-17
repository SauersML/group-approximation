---
rg: 2
id: bg-cycle-triviality-is-closed-under-the-pbh-calculus
kind: claim
title: The quasi-identities "every Baumslag--Gersten cycle is trivial" hold in all residually finite, periodic, hyperbolic and proper CAT(0) seeds and survive free, retract-amalgam, graph and wreath products, finite extensions and partial-conjugation mapping tori, so that calculus never reaches the Baumslag--Gersten group, Higman's group or any one-relator group containing them
distinct_from:
  bg-pattern-groups-act-on-no-locally-finite-cat0-complex: that excludes locally finite geometric hosts (trees, CAT(0) complexes, finite-orbit permutation actions); this excludes the algebraic permanence calculus of the permutational Boone--Higman class, whose members need not act on any locally finite space.
  magnus-hnn-permanence-forces-one-relator-boone-higman: that reduces one-relator Boone--Higman to Magnus-subgroup HNN permanence; this shows that permanence cannot be obtained from the other closure operations, because they all preserve an invariant that the Baumslag--Gersten HNN step destroys.
  pbh-class-closed-under-relative-holomorphs: that puts partial-conjugation mapping tori over BS(1,2) into B_A; this shows every group so obtained from the listed seeds satisfies BG-cycle triviality, so none contains the Baumslag--Gersten group.
  baumslag-gersten-group-satisfies-boone-higman: that is the open embedding question; this says which constructions cannot answer it.
artifacts:
  - research/bg-cycle-triviality-closure-proof.md
---

**ESTABLISHED** (elementary; full proof in `bg-cycle-triviality-closure-proof`).
This is a class-killing obstruction: it marks the exact step where the known
permanence calculus for `B_A` stops before reaching the Baumslag--Gersten group.

## The invariant

A **BG cycle of length `e ≥ 1`** in a group `G` is a tuple
`(a_0, …, a_(e-1); s)` of elements with

```text
a_(i+1) a_i a_(i+1)^-1 = a_i^2   (0 <= i <= e-1),   where a_e := s a_0 s^-1.
```

`G` has **BG-cycle triviality**, written `G ∈ 𝒫`, if `a_0 = 1` in every BG cycle
of `G`. Rotating a cycle to `(a_1, …, a_(e-1), s a_0 s^-1; s)` shows that then
all `a_i = 1`. Each condition is a quasi-identity, so `𝒫` is a quasivariety.

- `e = 1`, `s = t`: in `BG = < a, t | b a b^-1 = a^2 >` with `b = t a t^-1`, the
  tuple `(a; t)` is a BG cycle with `a ≠ 1`. So `BG ∉ 𝒫`.
- `e = 4`, `s = 1`: in `H4 = < g_i (i ∈ Z/4) | g_i g_(i+1) g_i^-1 = g_(i+1)^2 >`,
  the tuple `(g_0, g_3, g_2, g_1; 1)` is a BG cycle with `g_0 ≠ 1`. So `H4 ∉ 𝒫`.

## Statement

**A. Seeds.** The following groups lie in `𝒫`:
1. every group all of whose elements that are conjugate to their own square have
   finite order; in particular every periodic group;
2. every residually-`𝒫` group, in particular every residually finite group and
   every linear group over any field (finitely generated subgroups are residually
   finite, and a cycle lives in one);
3. every hyperbolic group;
4. every group acting by semisimple isometries on a CAT(0) space in which every
   element with a fixed point has finite order. In particular this covers every
   group acting by cellular isometries, with finite cell stabilizers, on a CAT(0)
   polyhedral complex with finitely many shapes: lattices in products of trees
   (including the Burger--Mozes and Rattaggi simple lattices), Kac--Moody lattices
   acting on their buildings, and groups acting properly on finite-dimensional
   CAT(0) cube complexes;
5. every group of orientation-preserving piecewise-linear homeomorphisms of an
   compact interval with finitely many breakpoints (Thompson's `F`, Stein groups,
   irrational-slope `F`).

**B. Closure.** `𝒫` is closed under:
1. subgroups, arbitrary direct products, directed unions, ultraproducts;
2. extensions `1 → N → G → Q → 1` with `N ∈ 𝒫` and `Q` periodic, in particular
   finite-index overgroups;
3. groups acting on trees without inversions in which, for each vertex stabilizer `G_v` and each
   `1 ≠ g ∈ G_v`, some homomorphism from `G` to a `𝒫`-group does not kill `g`.
   So `𝒫` is closed under free products, amalgams `X *_C Y` over a common retract,
   finite trees of groups with retract edge groups, graph products, and equivariant
   graph products `G_Γ ⋊ C` with every `G_v ⋊ C ∈ 𝒫`;
4. restricted permutational wreath products `A wr_X G = (⊕_X A) ⋊ G` over an
   arbitrary `G`-set `X`, when `A, G ∈ 𝒫`;
5. **free-product mapping tori, as a reduction.** Let `Q = M * F_m`, and let
   `β ∈ Aut(Q)` with `β(M) = k M k^-1` for some `k ∈ Q`. Let `α ∈ Aut(M)` be
   `m ↦ k^-1 β(m) k`. Then `Q ⋊_β Z ∈ 𝒫` if and only if `M ⋊_α Z ∈ 𝒫`. In
   particular, when `β` is a partial conjugation on `M` (`α = id`), `Q ⋊_β Z ∈ 𝒫`
   iff `M ∈ 𝒫`, and so is every ascending HNN extension `J *_β` with `β(J) ⊆ J`;
6. relative holomorphs `Q ⋊ Aut_M(Q)`, and `Aut_M(M * F_n)`, when `M` is finitely
   generated and residually finite.

**C. Consequence.** Let `𝒢` be the smallest class containing the seeds of part A
and closed under the operations of part B. It contains the `B_A` members of the
graph built from char-zero and char-`p` linear groups, `Aut(F_n)`, hyperbolic
groups, product-of-trees lattices, power-map free mapping tori (residually finite
by Borisov--Sapir), 3-manifold groups, mapping class groups, PL interval groups, and the constructions of
`pbh-class-closed-under-graph-products`,
`pbh-class-closed-under-common-retract-amalgams`,
`boone-higman-type-a-class-closed-under-finite-extensions`,
`permutational-boone-higman-closed-under-wreath-products`,
`bh-type-a-class-closed-under-permutational-lamp-wreaths` (with top group in `𝒫`)
and parts (T) and (H, RF case) of `pbh-class-closed-under-relative-holomorphs`.
Then `𝒢 ⊆ 𝒫`. So **no group in `𝒢` contains `BG`, `H4`, or any group with a
nontrivial BG cycle**, and in particular no one-relator group containing `BG`.

## Where the calculus stops (exact steps)

- **HNN extensions over finitely generated subgroups.** `BG` is the HNN extension of
  `BS(1,2) ∈ 𝒫` along `<a> → <b>`. This is the Magnus-subgroup HNN step of
  `bh-embeddability-survives-magnus-subgroup-hnn`, and part (b) of
  `stable-permutation-hnn-of-type-a-actor-is-type-a`. Any proof that `BG` lies in
  `B_A` must leave `𝒢`. It must use an operation outside part B, such as a
  permutation-realized HNN step, along whose permutation `a` has infinite orbits
  (`bg-pattern-groups-act-on-no-locally-finite-cat0-complex`). Or it must use a seed
  that already carries a nontrivial BG cycle.
- **Seeds that part A does not cover.** Higman--Thompson and Brin--Thompson
  groups, twisted Brin--Thompson groups, Leavitt unit groups, Rover--Nekrashevych
  groups and finitely presented simple highly transitive groups are `B_A` seeds that
  part A does not cover. A seed containing `BG` would have to come from such a
  non-residually-finite, non-geometric family. (Remark, not used: in a finitely
  generated group an infinite-order `g` with `h g h^-1 = g^2` has `|g^(2^k)| <= |g| + 2k|h|`,
  so `<g>` is exponentially distorted. So any seed whose infinite cyclic subgroups
  are undistorted lies in `𝒫` by A1; this is the reported situation for `V` itself.
  The families above other than `V` are where membership is genuinely open.)
- **Mapping tori with a nontrivial outer part.** For
  `mif-free-product-automorphism-ascending-hnn-is-pbh` with `M` a finitely presented
  simple MIF group, part B5 reduces membership in `𝒫` to `M ⋊_α Z ∈ 𝒫`, which is
  open. The relative holomorph (H) over a non-residually-finite `M ∈ 𝒫` is open.

## Sharpness

- `𝒫` is not closed under HNN extensions with cyclic associated subgroups (`BG`).
- Exponent `2` matters: for `a_(i+1) a_i a_(i+1)^-1 = a_i^3`, `SL(2,3)` has the
  nontrivial finite pattern `a = i`, `b = j`, `t` of order 3.
