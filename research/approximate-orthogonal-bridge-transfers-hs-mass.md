---
rg: 2
id: approximate-orthogonal-bridge-transfers-hs-mass
kind: claim
title: An approximate common bridge forces a quantitative transverse HS block
distinct_from:
  two-matchings-force-exponential-dimension-with-multiplicity: that uses only exact nonvanishing; this supplies the dimension-free local inequality needed for robust orbit propagation.
---

Let `P,Q,Q',R` be orthogonal projections in a matrix algebra with `QQ'=0`.
Put

```text
B=P Q R,               B'=P Q' R,             C=Q P Q'.        (AB1)
```

If

```text
||B-B'||_2 <= eta,
```

then

```text
||C||_2 >= ||B||_2^2-eta ||B||_2.                              (AB2)
```

All norms are normalized Schatten norms, so the estimate is independent of
matrix dimension and all four projection ranks.  In particular, when
`eta=0`, every nonzero common bridge produces a nonzero transverse block.

The quadratic dependence on the bridge amplitude is real in this local
estimate.  A robust two-matching proof must therefore sum orthogonal bridge
energies before applying `(AB2)`, rather than thresholding one tiny block at
a time.
