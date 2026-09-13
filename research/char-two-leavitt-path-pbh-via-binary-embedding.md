---
rg: 2
id: char-two-leavitt-path-pbh-via-binary-embedding
kind: route
title: Embed the Leavitt path algebra unitally in L_F(1,2), lower the field to F_2, and use the binary type (A) actor
target: char-two-leavitt-path-unit-groups-satisfy-pbh
requires:
  - countable-graph-leavitt-path-algebras-embed-in-binary-leavitt
  - leavitt-unit-groups-over-finite-fields-mutually-embed
  - binary-leavitt-unit-group-satisfies-pbh
---

Let `F` be a finite field with `q = 2^k` elements and `E` a countable graph with `E^0` finite.

1. **Graph to rose.** By `countable-graph-leavitt-path-algebras-embed-in-binary-leavitt`
   with `R = F`, there is a unital injective ring homomorphism `ι : L_F(E) -> L_F(1,2)`. By
   the consequence recorded there, `ι` restricts to an injective group homomorphism
   `L_F(E)^x -> L_F(1,2)^x`.
2. **Lower the field.** `F` is the field `F_q`. By `leavitt-unit-groups-over-finite-fields-mutually-embed`
   with `p = 2`, `(q, n) = (q, 2)`, there is an injective group homomorphism
   `L_(F_q)(1,2)^x -> L_(F_2)(1,2)^x`.
3. **The actor.** By `binary-leavitt-unit-group-satisfies-pbh`, `L_(F_2)(1,2)^x` embeds in a
   finitely presented group `Γ` with an action of type (A).
4. **Composition.** The composite `L_F(E)^x -> Γ` is injective. Every subgroup `H` of
   `L_F(E)^x` embeds in `Γ` by restriction. ∎

For `E` the rose with `n` loops, step 1 can be replaced by step (a) of
`leavitt-unit-groups-over-finite-fields-mutually-embed-proof`.
