---
rg: 2
id: central-phase-certificate-forces-divergent-filling-proof
kind: route
title: Quotient by the relator phases, then compare the modular seminorm with the chord length
target: central-phase-certificate-forces-divergent-filling
requires: []
---

**(1) The filling identity.**  Let `N = <z^(b_1),...,z^(b_l)> <= <z>`.  It is
contained in the centre of `E`, hence normal, and `E/N` is a finite group.
The composite

```text
F(S) -> E -> E/N
```

sends every relator `r_j` to the class of `z^(b_j)`, which is trivial in
`E/N`.  So it kills every relator and factors through `P`, exhibiting `E/N`
as a *finite quotient of `P`*.  Because `w in R_fin(P)`, its image is
trivial there, i.e. `z^a in N`.  The subgroup `N` of the cyclic group `<z>`
consists exactly of the elements `z^(sum_j c_j b_j)` with `c_j in Z`, so

```text
a = sum_j c_j b_j   (mod m),
```

which is `(CPC2)`.

**(2) The chord bound on the witness phase.**  For any integer `k`,

```text
|e^(2 pi i k / m) - 1| = 2 |sin(pi k / m)| = 2 sin(pi |k|_m / m),
```

using `|k|_m <= m/2`, so that `pi |k|_m / m` lies in `[0, pi/2]` where `sin`
is nondecreasing.  Applying this to `k = a` and inverting,

```text
|e^(2 pi i a / m) - 1| >= eta
  ==>  sin(pi |a|_m / m) >= eta/2
  ==>  pi |a|_m / m >= arcsin(eta/2)
  ==>  |a|_m >= kappa(eta) m,        kappa(eta) = (1/pi) arcsin(eta/2).
```

The inversion is legitimate because both `pi|a|_m/m` and `arcsin(eta/2)` lie
in `[0,pi/2]`, and `eta <= 2` always, since a chord of the unit circle has
length at most `2`.

**(3) The modular seminorm is subadditive.**  `|.|_m` satisfies
`|x+y|_m <= |x|_m + |y|_m` and `|c x|_m <= |c| |x|_m` for `c in Z`, both
immediate from the definition as distance to the subgroup `m Z`.  Hence,
from `(CPC2)`,

```text
|a|_m = |sum_j c_j b_j|_m <= sum_j |c_j| |b_j|_m <= eps m sum_j |c_j|.
```

**(4) Combine.**  Steps (2) and (3) give
`kappa(eta) m <= eps m sum_j |c_j|`.  Dividing by `eps m > 0`,

```text
sum_j |c_j| >= kappa(eta) / eps,
```

which is `(CPC3)`.
