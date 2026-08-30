---
rg: 2
id: stw63-all-separably-acting-von-neumann-proof
kind: route
title: Split into semifinite and type-III central summands
target: stw63-all-separably-acting-von-neumann-codomains-have-uniqueness
requires:
  - stw63-semifinite-von-neumann-codomains-have-uniqueness
  - stw63-type3-separable-predual-vn-uniqueness
---

Let `z_sf` be the central type-I-and-II projection of `M`.  Then

```text
M = z_sf M directSum (1-z_sf)M = M_sf directSum M_III,
```

where `M_sf` is semifinite and `M_III` is type III.  Both summands act on
separable Hilbert spaces, and `M_III` has separable predual.

Central compression turns each original embedding into a unital embedding in
each nonzero summand.  Semifinite uniqueness supplies implementing unitaries
in `M_sf`; type-III uniqueness supplies them in `M_III`.  Given one finite set
and tolerance, take one unitary from each result and form their direct sum.
This proves the required finite-set approximation in `M`, and separability of
`Z` turns these approximations into one implementing sequence.
