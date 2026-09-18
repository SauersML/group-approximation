---
rg: 2
id: simple-groups-on-trees-with-fg-edge-groups-have-b1-zero
kind: claim
title: A finitely generated simple group acting on a tree without a fixed point has s-normal edge stabilizers of infinite index, so its first L2-Betti number vanishes as soon as one edge stabilizer is finitely generated
distinct_from:
  fp-infinite-simple-group-not-two-generated: that asks for a finitely presented simple group needing three generators, for which a first L2-Betti number above 1 would suffice; this shows that no simple amalgam, HNN extension or tree lattice with a finitely generated edge group can supply it.
  l2-betti-numbers-vanish-for-actions-with-l2-acyclic-stabilizers: that needs L2-acyclic stabilizers of an action on an acyclic complex; this needs only that one edge stabilizer has finite first L2-Betti number, and uses simplicity instead.
  amenable-normalish-kills-l2-betti-bounded-cohomology: that is vanishing from an amenable normalish subgroup; this is vanishing from an s-normal edge stabilizer, which need not be amenable (free, in the Burger–Mozes case).
---

**ESTABLISHED** by `simple-groups-on-trees-b1-zero-proof` (lane proof, bh-free-13, 2026-09-18; not
independently reviewed). The proof combines two cited theorems, both read at source on 2026-09-18:
Minasyan–Osin, arXiv:1310.6289, Theorem 1.1 (TeX label `main-1`), with their remark that simple groups are
never acylindrically hyperbolic; and Peterson–Thom, arXiv:0708.4327, the theorem labelled `main2`. No
priority is claimed.

## Statement

Let `G` be a finitely generated infinite simple group acting on a simplicial tree `𝒯` without inversions and
without a global fixed point. Let `𝒯_0` be the minimal `G`-invariant subtree.

1. For all vertices `u, v` of `𝒯_0`, the pointwise stabilizer `Pst_G{u, v}` is infinite.
2. Every edge stabilizer `E = G_e`, `e ⊂ 𝒯_0`, is s-normal (`E ∩ gEg^(-1)` is infinite for every `g`) and has
   infinite index in `G`.
3. If `β_1^(2)(G_e) < ∞` for one edge `e` of `𝒯_0`, for instance if `G_e` is finitely generated, then
   `β_1^(2)(G) = 0`.
4. **Product lattices.** Let a simple group `Γ` act properly and cocompactly on a product `T_1 × T_2` of two
   infinite locally finite trees, preserving the factors. Then `β_1^(2)(Γ) = 0`. This covers the Burger–Mozes, Wise and
   Rattaggi groups. The action on (the barycentric subdivision of) `T_1` has edge stabilizers that act
   properly and cocompactly on `T_2`, so they are finitely generated and virtually free.

## Why it matters here

The only general lower bound for the rank of an infinite simple group is `d(G) ≥ 1 + β_1^(2)(G)`, the one
recorded in `fp-infinite-simple-group-not-two-generated`, Attempt 2. Item 3 closes that route for every simple
group that splits over a finitely generated subgroup, whatever the vertex groups are. This includes the
"amalgam-like" designs, such as `A *_C B` with `C` amenable or free of finite rank. Item 4 re-derives the
product-of-trees vanishing recorded there without L²-Künneth.

An amalgam route to `β_1^(2) > 1` therefore needs an edge group with infinite first L²-Betti number, e.g. an
infinitely generated free group, as in Camm's simple amalgams. Finite presentability of `G` would then have
to come from elsewhere.

## Lesson for general BH

A simple host that splits over a subgroup can never do so acylindrically: its edge stabilizers are s-normal
and of infinite index, i.e. pairwise conjugates always meet infinitely (Minasyan–Osin). So a Boone–Higman
route that builds the final simple group as an amalgam or HNN extension must end in a Burger–Mozes- or
Camm-type splitting, with fat, commensurated-like edge groups. It can never end in the small or malnormal edge
groups that make permanence theorems easy. This is a necessary shape condition for the amalgam/HNN
permanence nodes (`bh-class-decidable-amalgams-from-free-products-and-hnn`,
`bh-embeddability-survives-decidable-edge-hnn`): the simple envelope must thicken the edge groups.

## Scope

- Only `β_1^(2)` is controlled. Nothing here bounds the rank of these groups from above, and whether the
  Burger–Mozes groups are 2-generated stays open.
- Simplicity is used only to exclude acylindrical hyperbolicity, a virtually cyclic `G`, a fixed end and a
  finite-index edge stabilizer.
