---
rg: 2
id: pbh-groups-act-freely-in-relative-automorphism-actors
kind: claim
title: Every group in the permutational Boone--Higman class sits inside a type (A) actor that it acts on freely, with infinitely many orbits
distinct_from:
  relative-automorphism-of-fp-simple-mif-group-has-type-a-action: that is BFFHZ Theorem E, the type (A) action of Aut_M(M * F_n) on Hom_M(M * F_n, M); this records that the copy of M given by the translations x_1 -> x_1 g acts freely on that set, which Theorem E does not state.
  pbh-passes-to-relative-free-group-automorphisms: that moves the permutational property from H to Aut_H(H * F_n); this is a statement about the orbits of the input on the actor set, used to embed free sets of the input equivariantly.
artifacts:
  - research/artifacts/solve-bh-free-solvable-2026-09-13.md
---

**ESTABLISHED** by `pbh-free-action-via-relative-automorphisms-proof`.

**Credit.** An observation on BFFHZ's actor (arXiv:2503.21882v2), elementary once
their Theorems C and E are available. No priority is claimed. Not independently
reviewed.

## Statement

Let `G` be a group that embeds in a group admitting an action of type (A), that
is, `G ∈ B_A` (`boone-higman-type-a-class-closed-under-finite-extensions`). Then
there are:
- a finitely presented simple MIF group `M ⊇ G`;
- the type (A) action of `Γ = Aut_M(M * F_2)` on `S = Hom_M(M * F_2, M)` from
  BFFHZ Theorem E;
- an injective homomorphism `τ : M -> Γ`;

such that every point of `S` has trivial stabilizer in `τ(G)`, and `τ(G)` has
infinitely many orbits on `S`.

**Consequence.** Every countable free `G`-set `X` admits a `G`-equivariant injection
`X -> S`. Choose distinct orbit representatives in `S`, one for each `G`-orbit of
`X`.

## Why this matters

A type (A) actor usually has large point stabilizers, and a subgroup of it need not
act freely anywhere. Regular wreath products `A wr G` need a free `G`-orbit at the
top. This node supplies free orbits for every `G` in `B_A`, inside an actor of type
(A). It is the input of `permutational-boone-higman-closed-under-wreath-products`.
