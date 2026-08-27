---
rg: 2
id: a4-regular-line-sector-spectral-split
kind: claim
title: A regular A4 context canonically exposes its three one-dimensional sectors by a 1 versus 1/3 compression gap
---

Let `A=<a> ~= C3`, `B=<b> ~= C2` be the standard generators of `A4`, and let
`rho` be any multiple of the regular representation.  Write `P_chi` for the
three spectral projections of `rho(a)` and

```text
Q_+=(1+rho(b))/2,   Q_-=(1-rho(b))/2.
```

On each `P_chi` sector, the positive compression `P_chi Q_+ P_chi` has exactly
two eigenvalues:

```text
1    on the chi-th one-dimensional A4-isotypic summand,
1/3  on the contribution of the three-dimensional A4 irrep.
```

Equivalently `P_chi Q_- P_chi` has eigenvalues `0` and `2/3` on those same
summands.  In one copy of `Reg(A4)` the multiplicities are respectively `1`
and `3`; in an arbitrary regular multiple they scale by the external
multiplicity.

Hence the spectral projection

```text
1_[2/3,1](P_chi Q_+ P_chi)
```

is **exactly** the corresponding one-dimensional A4 isotypic projection.  It
has normalized trace `1/12`, and the gap from the rest of the spectrum is the
fixed number `2/3`.

Thus a regular A4 context carries more than the flat scalar C3/C2 overlap law:
it supplies three canonically recoverable positive-density line carriers.  The
information discarded by the rank-one classical overlap channel is stored in
the operator-valued principal-angle decomposition.