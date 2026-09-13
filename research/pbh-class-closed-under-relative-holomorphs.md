---
rg: 2
id: pbh-class-closed-under-relative-holomorphs
kind: claim
title: The permutational Boone--Higman class is closed under relative holomorphs (M * F_m) ⋊ Aut_M(M * F_m) and under ascending HNN extensions along partial-conjugation automorphisms
distinct_from:
  pbh-passes-to-relative-free-group-automorphisms: that moves the property from M to Aut_M(M * F_n); this adds the free product M * F_m itself as a normal subgroup on which those automorphisms act, and derives mapping tori and ascending HNN extensions from it.
  boone-higman-type-a-class-closed-under-finite-extensions: that is closure under subgroups, finite direct products and finite-index overgroups; this is closure under semidirect products and ascending HNN extensions with infinite cyclic top, which are not finite extensions.
  aut-free-groups-satisfy-permutational-boone-higman: that imports BFFHZ Theorem A and Corollary F, closure under free products; this is a mapping-torus permanence statement derived from Theorems C and E through the relative-automorphism claim.
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that imports Bux--Llosa Isenrich--Wu for groups acting cocompactly on locally finite trees; the ascending HNN extensions reached here along infinite-index images act on no such tree in their natural splittings.
---

**ESTABLISHED** through `pbh-relative-holomorph-closure-proof`. Not independently
reviewed.

Write `B_A` for the class of groups that embed in a group admitting an action of
type (A), as in `boone-higman-type-a-class-closed-under-finite-extensions`. In
the language of Belk--Fournier-Facio--Hyde--Zaremsky (BFFHZ, arXiv:2503.21882v2)
these are the groups satisfying the permutational Boone--Higman conjecture.

## Statement

Let `M` be a finitely generated group in `B_A`, let `m >= 1`, put
`Q = M * F_m`, and let `Aut_M(Q)` be the group of automorphisms of `Q`
restricting to the identity on `M`.

1. **(H) Relative holomorph.** The semidirect product `Q ⋊ Aut_M(Q)` embeds in
   `Aut_M(M * F_(m+1))`. So it lies in `B_A`.
2. **(T) Partial-conjugation mapping tori.** Let `β ∈ Aut(Q)` restrict on `M` to
   conjugation by an element of `Q`: there is `k ∈ Q` with `β(x) = k x k^-1` for
   all `x ∈ M`. Let `J <= Q` be a subgroup with `β(J) ⊆ J`. Then the ascending
   HNN extension `J *_β = < J, t | t j t^-1 = β(j) (j ∈ J) >` lies in `B_A`. In
   particular `Q ⋊_β Z` does.

By `type-a-action-gives-boone-higman-for-subgroups`, every finitely generated
group in (H) or (T) has solvable word problem and embeds in a finitely presented
simple group.

## Automorphisms allowed in (T)

The automorphisms in (T) are exactly `β = c_k ∘ α` with `k ∈ Q` and
`α ∈ Aut_M(Q)` arbitrary. For `m = 1` with letter `z` and `σ ∈ M`, two basic
kinds:
- **Partial conjugation:** `β = c_σ` on `M` for some `σ ∈ M`, and `β(z) = z`.
- **Letter multiplication:** `β = c_σ` on `M` and `β(z) = z n` with `n ∈ M`. Its
  inverse is `c_σ^-1` on `M` and `z -> z σ^-1 n^-1 σ`.

## Examples

Let `B = BS(1,2) = < u, σ | σ u σ^-1 = u^2 >`, which is in `B_A` by
`char-zero-linear-groups-satisfy-permutational-boone-higman`.
- **Squaring on two letters.** `β = c_σ * id` on `B * <z>`, with
  `J = < u, z^-1 u z >`, free of rank 2. Then `J *_β` is
  `< x, y, t | t x t^-1 = x^2, t y t^-1 = y^2 >`. This is the index-two subgroup
  `K = BS(1,2) *_<c> BS(1,2)` of the Druţu--Sapir group
  (`drutu-sapir-group-index-two-squaring-mapping-torus`).
- **A mixing step.** `β = c_σ` on `B` and `β(z) = z u`, with `J = < u, z >`, free
  of rank 2. Then `J *_β` is `< x, y, t | t x t^-1 = x^2, t y t^-1 = y x >`.

The general power-map family is `power-map-free-mapping-tori-satisfy-permutational-boone-higman`.

## Credit

No priority is claimed. BFFHZ place `A * B` inside `Aut_G(G * F_n)` in their
proof of Corollary F, as recorded in
`pbh-passes-to-relative-free-group-automorphisms`. Their embedding was not
re-read here, so this node does not assert that it is the left-multiplication
map of Step 1. The sources read were only the repo nodes, and none of them
contains the conjugation formula with `Aut_M(Q)` or the ascending HNN
consequence.
