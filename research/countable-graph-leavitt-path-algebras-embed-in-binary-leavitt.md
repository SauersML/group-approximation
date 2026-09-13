---
rg: 2
id: countable-graph-leavitt-path-algebras-embed-in-binary-leavitt
kind: claim
title: The Leavitt path algebra of a countable graph embeds in the binary Leavitt algebra over the same coefficient ring, unitally when the graph has finitely many vertices
distinct_from:
  leavitt-unit-groups-over-finite-fields-mutually-embed: that proves mutual embeddings of the one-vertex Leavitt unit groups over the finite fields of one characteristic, and cites this theorem only as credit for its prefix-code step; this imports the theorem itself, for every countable graph.
  leavitt-algebras-l-k-1-n-are-simple: that is simplicity of the one-vertex Leavitt algebras; this is an embedding theorem for the Leavitt path algebras of all countable graphs.
artifacts:
  - research/artifacts/leavitt-pbh-general-2026-09-13.md
---

**ESTABLISHED (literature import)** through `brownlowe-sorensen-leavitt-path-embedding-citation`.
Not reproved here.

## Statement

Let `R` be a commutative ring with unit and `E` a directed graph. If `E` is countable,
there is a `*`-algebraic embedding of the Leavitt path algebra `L_R(E)` into
`L_R(1,2)`. If `E^0` is finite, the embedding can be chosen to be unital.

This is Theorem 4.1 of N. Brownlowe and A. P. W. Sørensen, *Leavitt R-algebras over
countable graphs embed into L_(2,R)*, arXiv:1503.08705v3, where `L_(2,R)` denotes
`L_R(1,2)`.

## Consequence for unit groups

A unital injective ring homomorphism `ι` maps units to units, since `ι(u)ι(u^-1) = ι(1) = 1`,
and it restricts to an injective group homomorphism of the unit groups. So for countable
`E` with `E^0` finite, `L_R(E)^x` embeds in `L_R(1,2)^x`.

**Conventions.** Leavitt path algebras are written with two opposite edge conventions in
the literature. Switching conventions replaces `E` by its opposite graph, which is again
countable with the same vertex set. So the statement is the same in either convention.
