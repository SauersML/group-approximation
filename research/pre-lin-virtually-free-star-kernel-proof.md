---
rg: 2
id: pre-lin-virtually-free-star-kernel-proof
kind: route
title: Freeze the exact star, retain its selector kernel, and then apply projection-density rounding
target: pre-lin-virtually-free-star-retains-forbidden-gram-kernel
requires:
  - predicate-preserving-nonscalar-frames-miss-forbidden-source
  - role-hyperoctahedral-type-has-an-orthogonal-amalgam-model
  - finite-packet-graph-atlases-have-a-regular-stationary-flow
  - partial-isometry-gram-state-collapses-lin-corners
  - algebraic-exhaustive-marked-type-detectors-violate-induction
---

Apply `(PNF5)` from the first required claim to every star vertex.  This is
exactly `(PLV2)`, and taking the join gives `(PLV3)`.  Since
`Ftilde_c<=Q` and every selected carrier annihilates `Ftilde_c`, Pythagoras
and partial-isometry transport give `(PLV4)`.

A finite graph of finite groups has virtually-free fundamental group.  Its
simultaneous normalized-HS exactification does not add relations: feeding
it the exact orthogonal-amalgam representation from the second required
claim returns a zero-defect admissible representation.  The third required
claim supplies the positive regular stationary multiplicities, including
every rejected marked selector atom.  Consistency is already exact on the
whole source by `(PNF2)`, since every transported occurrence is the image
of the same source selector.  This proves `(PLV5)--(PLV6)` without a
state-dependent choice of atom or intertwiner.

The fourth required claim says that Lin's spectral family for the Gram
state is constantly `Q` almost everywhere, so applying Lin after this exact
star leaves all displayed source projections unchanged.  Finally, the last
required claim proves the exhaustive dichotomy: rows on a proper allowed
subfamily retain the kernel, while algebraic rows on every marked type are
impossible.
