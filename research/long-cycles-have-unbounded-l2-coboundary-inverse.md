---
rg: 2
id: long-cycles-have-unbounded-l2-coboundary-inverse
kind: claim
title: Cyclic shifts have no dimension-free L2 coboundary inverse off their fixed vectors
distinct_from:
  weyl-defect-koopman-spectral-regularity: that asks the arithmetic Weyl-relator defect to avoid the bad low orbit-frequency modes; this exhibits those modes for an unrestricted cyclic-shift defect.
  solenoid-absorption-cascade-converges: that asks whether the full coupled solenoid correction still converges; this proves the bare cyclic dynamics cannot supply the needed estimate.
---

Let `L>=2`, let `psi_L` be cyclic shift on normalized
`ell^2(Z/LZ)`, and let `H_L^0` be the orthogonal complement of the
constant vectors.  The norm of the inverse

```text
(1-psi_L)^(-1):H_L^0 -> H_L^0
```

is at least

```text
L/(2 pi).                                             (LCI1)
```

Consequently there is no dimension-independent estimate

```text
||c||_2 <= C ||(1-psi_L)c||_2                         (LCI2)
```

on the mean-zero subspaces of arbitrarily long cycles.  This remains true
when the coordinates of the cycle are labelled by a lacunary orbit
`m,4m,...,4^(L-1)m`: lacunarity of the labels does not change the cyclic
shift spectrum.

Applied to the exact odd `BS(1,4)` skeleton, this proves that Parseval,
removal of the fixed algebra, or a generic lacunary large-sieve inequality
cannot establish the dimension-free Weyl-defect coboundary estimate.  Such
an estimate requires an additional arithmetic theorem excluding the first
few orbit-frequency modes from the projected Weyl-relator defect.
