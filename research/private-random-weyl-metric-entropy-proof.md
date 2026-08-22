---
rg: 2
id: private-random-weyl-metric-entropy-proof
kind: route
title: Uniformly sample the full Weyl energy over all low-dimensional additive representations
target: private-random-weyl-sampler-forces-growing-matrix-dimension
requires:
  - full-weyl-energy-support-floor
---

First fix a universal full-product gap `eta_0>0`.
`full-weyl-energy-support-floor` gives the sharper elementary estimate

```text
E_(a,b) ||X(a)Z(b)-(-1)^(a.b)Z(b)X(a)||_2^2
 >=2(1-d/2^r).
```

Consequently, for every fixed `K`, one may take, for example, `eta_0=1` for
every sufficiently large `r` and every `d<=K r`, since `K r/2^r->0`.
Notice that this estimate requires only the exact additive law for `X`; it
permits an arbitrary unitary family `Z(b)`.

It remains to sample this expectation uniformly.  Up to simultaneous
conjugacy, an exact representation of `F_2^r` in dimension `d` is specified
by a list of `d` characters.  Thus a pair `(X,Z)` is specified by at most

```text
2^(2rd)
```

discrete character lists and one relative unitary `W in U(d)`.  An
operator-norm `epsilon`-net for `U(d)` has size at most

```text
(C_0/epsilon)^(2d^2).                                      (1)
```

For fixed `(a,b)`, the squared normalized-HS Weyl defect lies in `[0,4]`
and changes by at most `16 epsilon` when `W` moves by `epsilon` in operator
norm.  Choose `epsilon=eta_0/64`.

For one net point, Hoeffding bounds failure of empirical/full agreement to
within `eta_0/4` by

```text
2 exp(-c_0 eta_0^2 m).                                    (2)
```

For every `d<=K r`, the logarithm of the total net size is

```text
2rd log 2 + 2d^2 log(C_0/epsilon)=O_(eta_0,K)(r^2).        (3)
```

Summing `(2)` over the nets for all `d<=K r`, a sufficiently large choice
`m=C_K r^2` leaves positive probability that every empirical energy is
within `eta_0/2` of its full expectation.  Fix one realization.  Then
`(PRW1)` holds with `eta=eta_0/2` for every `d<=K r`.

Finally put `N=r^2` and append the private columns to a good dimension-`N`
generator block.  Since `m=O(N)`, the same distance calculation as in the
scalar condenser preserves a constant column spectral gap, while the sampled
incidence is a matching.  This proves `(PRW2)`.
