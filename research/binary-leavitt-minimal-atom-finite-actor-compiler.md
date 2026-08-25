---
rg: 2
id: binary-leavitt-minimal-atom-finite-actor-compiler
kind: claim
title: A finite normalizer packet returns a minimal marked atom with binary Leavitt capacity
refuted_by:
  - binary-leavitt-finite-actor-minimal-atom-dichotomy
distinct_from:
  binary-leavitt-three-row-atomic-compiler: that permits a coordinate-dependent coefficient address but requires three coefficient-sensitive rows with fixed relator fillings; this proposal tries to obtain those rows from finite atom minimality and normalizer covariance alone.
  norm-corona-sparse-character-atom-reduces-pointwise-centralizer: that constructs a common reducing sparse corona carrier for pointwise centralizers; this claims the stronger and false conclusion that a finite normalizer orbit returns coefficient multiplicity to that carrier.
---

**REFUTED AS A FINITE-PACKET COMPILER.**  The proposed input was a fixed
finite elementary abelian root window `A` containing a nonzero marked root,
together with finitely many exactified actor unitaries whose conjugations
preserve `A`.  After choosing a nonzero joint character atom of least rank
in the finite actor orbit, the proposal asserted that orbit minimality and a
bounded actor return produce, on that same atom, the two inverse rows and
the completeness row of `binary-leavitt-atomic-morita-return`.

This conclusion was meant to use only:

1. the exact multiplication table of `A`;
2. the finite actor action table on `A`;
3. exact actor covariance of the joint spectral projections; and
4. minimality of the selected nonzero atom rank.

It is false even at zero defect.  The finite crossed-product model in
`binary-leavitt-finite-actor-minimal-atom-dichotomy` has a surviving marked
rank-one atom, exact covariance, and equal--hence minimal--rank atoms
throughout every actor orbit.  A return word merely acts inside the same
multiplicity fiber.  It supplies no one-to-two capacity and cannot produce
exact binary Leavitt rows in a nonzero finite matrix corner.

The refutation is deliberately scoped.  It does not refute
`binary-leavitt-atomic-morita-return`, the three-row occurrence compiler, or
the Property-`(T)`-free non-MF endpoint.  It rules out only the inference
from finite abelian exactification, finite normalizer covariance, and
minimal-atom selection without an additional coefficient-sensitive
mixed/opposite-root occurrence.

