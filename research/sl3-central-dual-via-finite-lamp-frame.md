---
rg: 2
id: sl3-central-dual-via-finite-lamp-frame
kind: route
title: Use a finite quasiregular stable-letter frame to eliminate the separator
target: sl3-hnn-central-dual-gap-vanishes
requires:
  - full-hnn-regularity-is-a-quasiregular-unitary-orbit
---

**INVALIDATED PROPOSAL.**  Choose a large fixed family of cosets in
`Gamma/Lambda`, use the canonical mixed moments of the conjugates
`phi(a)Tphi(a)^*` to obtain an almost-orthogonal unitary frame, and apply its
noncommutative cross-Gram table to a stable-letter-central separator.

`finite-lamp-frame-is-matrix-range-neutral` realizes every prescribed fixed
window of these lamp moments exactly in a finite regular quotient of
`C_k*F_q`, while tensoring an arbitrary matrix-range separator through the
common multiplicity factor with unchanged support function and gap.  Thus
neither pairwise Gram data nor arbitrary fixed reduced lamp words can close
the dual inequality.

A replacement must keep the arithmetic actor attached: the same matrices
must both permute the lamp frame according to `Gamma/Lambda` and transport
the lattice coordinates according to the `SL_3(Z[1/p])` relations.  That
actor-covariant mixed datum is absent from the countermodel and is the
remaining finite-coordinate seam.
