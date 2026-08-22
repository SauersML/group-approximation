---
rg: 2
id: exact-dyadic-conductor-overlap-loss-proof
kind: route
title: Span the depth-two congruence kernel by eight conjugates of the kernel-join packet
target: exact-dyadic-conductor-band-has-uniform-parahoric-overlap-loss
requires:
  - depth-shifted-regular-overlap-is-exactly-one-sixteenth
---

By `(DSO3)`, the image of `K_B(a)` under `alpha_a` contains the cyclic
root subgroup

```text
X_13={x_13(2^(a-2)t):t in Z/4Z}.                        (DCL2)
```

Its six signed-Weyl conjugates give the six off-diagonal root subgroups at
depth `a-2`.  Add the conjugates of `X_12` and `X_23` by `x_21(1)` and
`x_32(1)`, respectively.  Modulo the six off-diagonal directions, their
infinitesimal matrices are

```text
E_22-E_11,       E_33-E_22.                             (DCL3)
```

For `a>=4`, the ideal `I=2^(a-2)(Z/2^a Z)` has `I^2=0`.  Hence the
depth-two principal kernel

```text
N_a=ker(Q_a -> Q_(a-2))
```

is the additive group `1+sl_3(I)`, and the eight conjugates above generate
it: their matrices are a `Z/4Z` basis of `sl_3(Z/4Z)`.  In particular, if
`F_j` is the fixed space of the `j`-th conjugate of `X_13`, then

```text
intersection_(j=1)^8 F_j = H^(N_a).                    (DCL4)
```

On an irreducible of minimal conductor `a`, the right side is zero.  Indeed
`N_a` is normal, so its fixed space is invariant under `Q_a`; a nonzero
fixed space would be the whole irreducible and make it factor through
`Q_(a-2)`.  The same holds on a direct sum of exact-conductor-`a`
irreducibles.  All eight `F_j` have the same dimension `f`, because their
subgroups are conjugate.  Codimension subadditivity in `(DCL4)` gives

```text
dim(pi) <= sum_j codim(F_j)=8(dim(pi)-f),
f <= (7/8)dim(pi).                                      (DCL5)
```

Finally, any common constituent of `pi o alpha_a` and
`theta o beta_a` is trivial on both `K_A(a)` and `K_B(a)`.  Viewed on the
`alpha_a` side, it is therefore fixed by
`alpha_a(K_B(a))`, hence by `X_13`.  Its dimension is at most `f`, and
`(DCL5)` proves `(DCL1)`.

