---
rg: 2
id: private-random-weyl-metric-entropy-proof
kind: route
title: Uniformly sample the full Weyl energy over all low-dimensional additive representations
target: private-random-weyl-sampler-forces-growing-matrix-dimension
requires:
  - generator-column-pauli-test-globalizes-but-does-not-pin-sites
---

First fix a universal full-product gap `eta_0>0`.  The average
Gowers--Hatami theorem quoted in
`generator-column-pauli-test-globalizes-but-does-not-pin-sites` says that
sufficiently small full Weyl energy produces an exact central-sign Weyl
representation on an amplification of relative dimension at most
`1+16 delta`.  For a fixed sufficiently small `delta`, a representation with
`d<=r` would therefore produce a nonzero exact rank-`r` Weyl packet in
dimension at most `2r`, impossible for large `r` because every such packet
has dimension divisible by `2^r`.  Consequently every exact additive pair in
dimension `d<=r` has full uniform Weyl energy at least `eta_0`.

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

For every `d<=r`, the logarithm of the total net size is

```text
2rd log 2 + 2d^2 log(C_0/epsilon)=O_(eta_0)(r^2).          (3)
```

Summing `(2)` over the nets for all `d<=r`, a sufficiently large universal
choice `m=C r^2` leaves positive probability that every empirical energy is
within `eta_0/2` of its full expectation.  Fix one realization.  Then
`(PRW1)` holds with `eta=eta_0/2`.

Finally put `N=r^2` and append the private columns to a good dimension-`N`
generator block.  Since `m=O(N)`, the same distance calculation as in the
scalar condenser preserves a constant column spectral gap, while the sampled
incidence is a matching.  This proves `(PRW2)`.
