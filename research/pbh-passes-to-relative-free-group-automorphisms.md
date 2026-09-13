---
rg: 2
id: pbh-passes-to-relative-free-group-automorphisms
kind: claim
title: A group satisfies permutational Boone--Higman exactly when its relative automorphism group Aut_H(H * F_n) embeds in a group with a type (A) action
distinct_from:
  fp-simple-highly-transitive-groups-satisfy-pbh: that is BFFHZ Theorem C, characterizing permutational Boone--Higman for one group by highly transitive or MIF envelopes; this is a permanence statement moving the property from H to the larger group Aut_H(H * F_n), proved from Theorems C and E.
  aut-free-groups-satisfy-permutational-boone-higman: that imports Theorem A and Corollaries D and F, where Aut(F_n) sits in Aut_V(V * F_n); this extends the same relative-automorphism mechanism from the base V to an arbitrary base H with the property.
  bffhz-action-image-is-finitely-presented: that is a finite-presentation statement about the image of the relative automorphism group acting on homomorphisms; this needs no finite presentation of any quotient and does not use that action.
  fp-simple-groups-embed-in-fp-simple-mif-groups: that is BFFHZ Question 3.4 itself; this reformulates it, one finitely presented simple group S at a time, as membership of the finitely presented group Aut_S(S * F_n) in the permutational class.
artifacts:
  - research/artifacts/ideas-2026-09-13/bh/bh-abstraction.md
---

**ESTABLISHED** through `pbh-relative-free-group-automorphisms-proof`. Not
independently reviewed.

## Statement

Let `H` be a finitely generated group with solvable word problem and let
`n >= 2`. Write `Aut_H(H * F_n)` for the group of `H`-automorphisms of the free
`H`-group `H * F_n`, that is, automorphisms restricting to the identity on `H`
(Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882v2, §1). The following
are equivalent.

1. `H` satisfies the permutational Boone--Higman conjecture: `H` embeds in a
   group admitting an action of type (A).
2. `Aut_H(H * F_n)` embeds in a group admitting an action of type (A).

**Corollary (BFFHZ Question 3.4 one group at a time).** For a finitely presented
simple group `S` and `n >= 2`, `S` embeds in a finitely presented simple MIF
group if and only if `Aut_S(S * F_n)` embeds in a group admitting an action of
type (A).

## What this adds

- **Permanence.** The permutational class is closed under
  `H -> Aut_H(H * F_n)`. This joins the permanence properties BFFHZ and
  Zaremsky record: commensurability, direct products, and free products
  (BFFHZ Corollary F).
- **Question 3.4 as a single instance.** For a centerless finitely presented `S`,
  `Aut_S(S * F_n)` is finitely presented (BFFHZ Proposition 1.1), and its action
  on `Hom_S(S * F_n, S)` has every type (A) property except faithfulness
  (`relative-automorphism-action-is-highly-transitive`). The corollary asks for
  any type (A) actor containing `Aut_S(S * F_n)`. It does not ask to remove the
  kernel of that particular action. A positive answer to BFFHZ Question 3.2 for
  `S` gives it, through BFFHZ's remark after Question 3.2, but the corollary
  needs no finite presentation of the action image.

## Novelty

BFFHZ already use nearby special cases: in the proof of Theorem A they embed
`Aut(F_n)` in `Aut_V(V * F_n)` (the case `H = 1` of the extension lemma), and in
the proof of Corollary F they place `A * B` inside `Aut_G(G * F_n)`. The extension step for an arbitrary
subgroup `H <= M`, and the two-sided statement above, were not found in
arXiv:2503.21882v2 as read (Theorems A, C, E, Corollaries D and F, Questions
3.1--3.6). The argument is elementary and no priority is claimed.
