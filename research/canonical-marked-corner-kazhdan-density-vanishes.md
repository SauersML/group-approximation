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
`G`.  Apply `central-involution-corner-exactification`, write `psi_n` for
the corrected tuples, and put

```text
e_n=(1-psi_n(J))/2,
```

and normalize the adjoint trace on `e_n M_(d_n) e_n` by its squared matrix
dimension.  For a fixed inverse-closed Kazhdan generating set `S` of
`Lambda`, let `A_n` be the adjoint Laplacian of the compressed
representation on that corner.  There is `kappa>0` such that, for every
fixed `0<b<kappa`,

```text
tr_ad(1_[0,b](A_n)) -> 0.                              (CMK1)
```

Equivalently in an energetic form useful for packet constructions: there
cannot be projections `R_n` in the corner adjoint spaces and a constant
`rho>0` with

```text
tr_ad(R_n)>=rho,
tr_ad(R_n A_n)/tr_ad(R_n) ->0.                         (CMK2)
```

In particular, a construction that forces a subspace of fixed positive
adjoint density with vanishing average old-`Lambda` commutator energy on the
canonical `J=-1` carrier is already a non-hyperlinearity contradiction.  It
does not need exact spectral containment, nor an additional copy through a
parity implementer followed by commutant no-growth.

The statement is specific to canonical microstates.  It says nothing about
arbitrary exact finite-dimensional representations, and it does not provide
the missing coefficient-covariant placement of a local Schur Reynolds
range.
