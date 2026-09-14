---
rg: 2
id: nonpositively-curved-simple-complexes-are-developable
kind: claim
title: A nonpositively curved simple complex of finite groups is strictly developable, so every local group injects into the direct limit
artifacts:
  - research/artifacts/hl-nh-local-colimit-2026-09-13.md
distinct_from:
  finite-readout-bcs-decoders-are-phase-surviving-local-colimits: that identifies decoders with phase survival in a colimit; this is the general developability theorem that certifies injectivity of local groups into such a colimit.
---

**ESTABLISHED** as a citation import by
`nonpositively-curved-simple-complexes-developable-citation`.

A **simple complex of finite groups** `G(Q)` over a finite poset `Q` is a
family of finite groups `P_J`, `J in Q`, with injective non-surjective
homomorphisms between comparable elements. Its **fundamental group** is the
direct limit `lim P_J`. It is **strictly developable** if every canonical map
`i_J : P_J -> lim P_J` is injective.

It is **nonpositively curved** if the geometric realization carries a
piecewise Euclidean (more generally `M_kappa`, `kappa <= 0`) structure with
finitely many shapes for which every local development is locally `CAT(0)`.
For a 2-dimensional realization this means: in every local development, the
link of the central vertex, with the angular metric, has no embedded cycle of
length `< 2 pi`.

**Theorem (Bridson--Haefliger, Theorem II.12.28).** A nonpositively curved
simple complex of finite groups is strictly developable, and its standard
development admits a `CAT(0)` metric on which the fundamental group acts by
isometries.

Trust surface: the book itself was not read. The statement is quoted from two
secondary sources by the same author, which state it with the same numbering.
Their quotes are in the artifact.
