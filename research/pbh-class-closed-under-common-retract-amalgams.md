---
rg: 2
id: pbh-class-closed-under-common-retract-amalgams
kind: claim
title: The permutational Boone--Higman class is closed under amalgams X *_C Y over a common retract C, under trees of groups with retract edge groups, and under equivariant graph products
distinct_from:
  pbh-class-closed-under-graph-products: that proves X *_C (C x K), where the second factor centralizes C, and graph products with no twisting; this allows any second factor Y that retracts onto C, so C may act nontrivially on the kernel on both sides, and graph products extended by a common group of vertex-wise automorphisms. That node's Scope lists the twisted case as not covered.
  pbh-class-closed-under-relative-holomorphs: that is closure under relative holomorphs of M * F_m and partial-conjugation mapping tori, with a free factor F_m added; this is closure under amalgamated products over retracts, and adds no free factor.
  boone-higman-type-a-class-closed-under-finite-extensions: that is closure under subgroups, finite direct products and finite-index overgroups; this is closure under amalgamated products over common retracts and over trees of such amalgams, which are infinite extensions.
  bh-embeddability-survives-decidable-edge-hnn: that is the open permanence of plain Boone--Higman embeddability under HNN extensions over decidable edge groups; this is a proved permanence of the permutational class, only for amalgams whose edge group is a retract on both sides.
artifacts:
  - research/artifacts/bh-common-retract-amalgams-even-artin-2026-09-16.md
---

Proved by the route `pbh-common-retract-amalgam-closure-proof`. It has not been
independently reviewed. The priority search is bounded: see §8 of the artifact.

Write `B_A` for the class of groups that embed in a group admitting an action of type
(A) (`boone-higman-type-a-class-closed-under-finite-extensions`). Every member embeds in
a finitely presented simple group and, if finitely generated, has solvable word problem
(`type-a-action-gives-boone-higman-for-subgroups`).

## Statement

1. **Common-retract amalgams.** Let `X, Y ∈ B_A`, and let `C` be a common subgroup
   that is a retract of `X` and a retract of `Y`. Then `X *_C Y ∈ B_A`.
2. **Trees of groups.** Let `T` be a finite tree of groups with every vertex group in
   `B_A`, where every edge group is a retract of both adjacent vertex groups. Then the
   fundamental group of `T` lies in `B_A`.
3. **Equivariant graph products.** Let `Γ` be a finite nonempty simplicial graph with
   vertex groups `G_v`. Let a group `C` act on every `G_v` by automorphisms, and so on
   the graph product `G_Γ`. If `G_v ⋊ C ∈ B_A` for every vertex `v`, then
   `G_Γ ⋊ C ∈ B_A`.

## What is new

- Part 1 strictly contains Part 1 of `pbh-class-closed-under-graph-products`, which is
  the case `Y = C × K`.
- The new input: realize both factors inside one finitely presented simple MIF
  envelope through the fibre product `X ×_C Y`. There conjugation by `C` induces the
  given actions on both kernels. The second kernel then goes to transvections, not to
  a set commuting with `C`.
- Part 3 with `C = 1` is Part 2 of the graph-product node.
  - With `C = Z` acting vertex-wise on doubled right-angled Artin groups by
    hyperbolic matrices in `SL_2(Z)`, it gives mapping tori that contain Sol lattices.
    These are not CAT(0) groups (artifact, §4).
- The main application is `artin-pbh-reduces-to-odd-component-cliques`: every even
  Artin group of FC type lies in `B_A`.

## Scope

- **Outer twists.** HNN extensions `<X, t | t c t^-1 = φ(c)>` with `φ` outer are not
  covered. `C` is a retract of `C ⋊_φ Z` only when `φ` is inner.
- **One-sided retracts.** Amalgams where `C` is a retract of one side only are not
  covered.
- In general amalgams the word problem involves membership in `C` (BFFHZ, as quoted
  in `pbh-class-closed-under-graph-products`).

**Verification (bh-verify-artin, 2026-09-18; lane check, not an external review).** PASS (Steps 0--4 re-derived; Steps 5--6 checked). The claim rests on BFFHZ Theorems C, (i) ⟹ (iv), and E, as quoted on their import nodes. I did not re-read them. See `research/artifacts/gq-bh-bh-verify-artin-report.md`.
