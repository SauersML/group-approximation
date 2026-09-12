---
rg: 2
id: bliw-locally-finite-tree-actions-embed-in-fp-simple-groups
kind: claim
title: A group acting faithfully and cocompactly on a locally finite tree with finitely presented edge stabilizers embeds in a finitely presented simple group
distinct_from:
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that imports the two named families the paper settles; this imports the general tree theorems they are derived from, together with the generalised Baumslag--Solitar theorem and the residual-finiteness boundary the authors state.
  twisted-brin-thompson-finite-presentation-criterion: that is the finite-presentation criterion for a twisted Brin--Thompson group; this is an embedding theorem for groups acting on locally finite trees, which reaches a twisted Brin--Thompson group only after enlarging the tree action to an oligomorphic one.
  type-a-action-gives-boone-higman-for-subgroups: that turns an action of type (A) into simple envelopes for subgroups of the actor; this starts from an action on a locally finite tree, which almost never has finitely many orbits of pairs, and builds the envelope through rigid permutation groups.
  fp-self-similar-groups-embed-in-fp-simple-groups: that covers finitely presented self-similar inputs through Rover--Nekrashevych groups; this covers cocompact actions on locally finite trees with finitely presented edge stabilizers.
---

**ESTABLISHED (literature import).** Source: K.-U. Bux, C. Llosa Isenrich,
X. Wu, *On the Boone--Higman Conjecture for groups acting on locally finite
trees*, arXiv:2408.05673v2 (24 January 2025). Read 2026-09-12 from the arXiv
HTML rendering, extracted to text. Verbatim:

1. **Theorem B [10.5].** "Let G be a group acting faithfully and cocompactly on
   a locally finite tree. If all edge stabilizers for the action are finitely
   presented, then G embeds in a finitely presented simple group."
2. **Theorem 10.5.** "Let G be a graph of groups such that all vertex groups are
   of type F_n and all edge groups have finite index in the vertex groups.
   Assume that G acts faithfully on its Bass–Serre tree. Then G embeds in a
   simple group of type F_n."
3. **Theorem C [11.1].** "Let G be a finitely presented group. Assume that there
   is a non-trivial group H ∈ BS_G such that H acts faithfully on its
   Bass–Serre tree. Then every K ∈ BS_G embeds in a finitely presented simple
   group." Here `BS_G` is "the class of groups consisting of all finite graphs of
   groups with the property that all edge and vertex groups are abstractly
   commensurable with G and all edge group inclusions in vertex groups have
   finite index."

## Stated boundary

Verbatim, from the paragraph after Theorem C: "the only obstruction for
applying Theorem C that we are currently aware of is that any G satisfying its
hypotheses must be residually finite. However, even if G is residually finite,
groups in BS_G need not themselves be, as is shown by BS(2,3) ∈ BS_Z and the
Burger–Mozes groups".

The authors also note that the groups of their Theorem A "do not necessarily
act faithfully on the corresponding Bass–Serre trees", and that their remedy is
"to enlarge the graphs of groups, so that the Bass-Serre trees remain locally
finite but the actions become faithful". In the proof of Theorem 11.1 this
enlargement glues a faithful graph of groups to the given one by a new edge
carrying a common finite-index subgroup.

## Scope

Nothing is reproved, and there is no Lean counterpart. The proof goes through
the rigid permutation group of the tree, a Stein--Farley complex, an
oligomorphic action on the vertex set, and the twisted Brin--Thompson group of
Belk--Zaremsky.

Not part of the import: under a faithful action on a locally finite tree, every
vertex stabilizer acts on each finite ball through a finite group, so it is
residually finite. This is why the method never reaches vertex groups without
enough finite quotients. The consequences for HNN extensions are drawn in
`finite-index-edge-hnn-embeds-in-fp-simple-group`.
