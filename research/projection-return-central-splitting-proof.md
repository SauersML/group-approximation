---
rg: 2
id: projection-return-central-splitting-proof
kind: route
title: Spectrally return minimal projections and apply matrix-unit transport
target: projection-return-models-force-central-splitting
requires: []
---

## Proof

Fix a model `D` and write `p_j=e^(j)_(11)`.  Choose `c_j in C_+` with
`||c_j-p_j||<1/16`.  The spectrum of `c_j` lies in disjoint neighbourhoods
of `0` and `1`, so the spectral projection

```text
q_j=1_((1/2),infinity)(c_j)
```

belongs to `C*(c_j) subset C`.  Standard spectral-projection perturbation
is quantitative here: on the lower spectral component `||q_j-c_j||` is at
most `1/16`, and on the upper component it is also at most `1/16`.  Hence

```text
||q_j-p_j|| <= ||q_j-c_j||+||c_j-p_j|| < 1/8 < 1.
```

In particular `q_j` is nonzero and is unitarily equivalent to `p_j` inside
`B`.  The hypothesis makes `q_j` properly infinite, hence `p_j` is properly
infinite.

The matrix-unit transport calculation in
`stw77-af-range-central-splitting-proof` now applies verbatim to `D`: split
each `p_j` into two orthogonal equivalent subprojections, transport the two
isometries across its matrix block, and sum over the central blocks.  This
produces two exact orthogonal isometries commuting with all of `D`.

As `D` approximates the prescribed finite subset of `C`, those isometries
have arbitrarily small commutators with that subset.  Therefore all defects
from `oinfty-map-stability-is-central-isometry-splitting` vanish, and the
inclusion is O-infinity-stable.
