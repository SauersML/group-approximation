---
rg: 2
id: canonical-spectral-derangement-proof
kind: route
title: Cyclically shift the regular spectral summands
target: canonical-spectral-derangement-kills-same-letter-row
requires: []
---

The canonical character restricts to the regular character of the finite
subgroup `<a>`.  Fourier inversion therefore gives

```text
tr(p_j)=1/m+o(1)
```

in canonical microstates, and exactly `1/m` after finite-group packet
exactification.  The Grassmann inequality for two rank-`d/m` projections is

```text
dim(E intersection F)>=max(2d/m-d,0),
```

which is `(CSD2)`.

For sharpness use the block cyclic shift `T(e_j tensor xi)=e_(j+1) tensor xi`.
This proves `(CSD3)`.  On `p_j` one has

```text
aTp_j=zeta^(j+1)Tp_j,
Tap_j=zeta^jTp_j.
```

Their difference is `(zeta-1)zeta^jTp_j`.  Since `T` is unitary, taking the
normalized Hilbert--Schmidt square proves `(CSD4)`.  Tensoring `a,T` with an
unrelated exact packet representation changes none of these identities and
lets the second factor satisfy any fixed edge table which has not been mixed
with `a`.

