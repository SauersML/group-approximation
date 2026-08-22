---
rg: 2
id: canonical-marked-corner-kazhdan-density-vanishes
kind: claim
title: A canonical central-sign corner has zero positive-gap Kazhdan commutant density
distinct_from:
  commutant-density-trace-blind: that computes the iterated exact-commutant density from the character; this gives the fixed spectral-cutoff statement needed for a marked central corner.
  property-t-hs-positive-density-commutant-no-growth: that compares the low spectra of a subgroup and its compressed copy; this proves absolute vanishing for the old subgroup in the canonical marked corner.
---

Let `G` contain an infinite property-`(T)` subgroup `Lambda` and a central
involution `J` with

```text
<J> intersect Lambda = 1.
```

Let `phi_n` be canonical-trace normalized-Hilbert--Schmidt microstates of
`G`.  After exactifying the fixed central two-point packet, put

```text
e_n=(1-phi_n(J))/2,
```

and normalize the adjoint trace on `e_n M_(d_n) e_n` by its squared matrix
dimension.  For a fixed inverse-closed Kazhdan generating set `S` of
`Lambda`, let `A_n` be the adjoint Laplacian of the compressed
representation on that corner.  There is `kappa>0` such that, for every
fixed `0<b<kappa`,

```text
tr_ad(1_[0,b](A_n)) -> 0.                              (CMK1)
```

In particular, a construction that forces a subspace of fixed positive
adjoint density into the old low-commutator space of `Lambda` on the
canonical `J=-1` carrier is already a non-hyperlinearity contradiction.  It
does not additionally need to copy that subspace through a parity
implementer and invoke commutant no-growth.

The statement is specific to canonical microstates.  It says nothing about
arbitrary exact finite-dimensional representations, and it does not provide
the missing coefficient-covariant placement of a local Schur Reynolds
range.
