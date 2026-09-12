---
rg: 2
id: literal-antiphase-regular-packing-proof
kind: route
title: Convert opposite conjugacy phases into orthogonal full Reynolds translates
target: literal-antiphase-branches-recreate-regular-character-packing
requires:
  - pairwise-antiphase-covariance-controls-cross-gram
  - canonical-trace-forbids-supercritical-character-packing
  - central-sign-bcs-atoms-are-subgroup-reynolds-projections
---

Equation `(LAP2)` and the defining Fourier sum give `(LAP3)` term by term.
For `i!=j`, insert the two spectral projections of `r_ij`; their ranges are
orthogonal, proving `(LAP4)`.  Trace additivity below `c` gives `(LAP5)`, and
the canonical Plancherel formula gives `(LAP6)`.

Since `F<=e_chi`, every transported analytic range is below the
corresponding full literal translate `p_i`.  Summing yields `(LAP8)`.  The
faithfulness of canonical trace shows that violating the resulting bound
can only collapse the finite source character, rather than produce a
matrix-only obstruction.  The analytic antiphase theorem then identifies
the strictly weaker compressed residual which would avoid this collapse.

