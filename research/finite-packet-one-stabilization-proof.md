---
rg: 2
id: finite-packet-one-stabilization-proof
kind: route
title: Put one positive generator of the packet ideal in an off-diagonal corner
target: finite-packets-fuse-after-one-stabilization
requires: []
---

Define

```text
d=sum_i (x_i*x_i + x_i x_i*) in A_+.
```

For each `i`, the C-star quotient norm argument gives

```text
Ideal(x_i)=Ideal(x_i*x_i)=Ideal(x_i x_i*).
```

For a finite sum of positive elements, the ideal of the sum is the sum of
their ideals: in the quotient by `Ideal(d)`, positivity of all summands and
vanishing of their sum force every summand to vanish.  Hence `Ideal(d)=I`.

Now put

```text
W = e_12 tensor d in M_2(A).
```

Then `W^2=0`.  Moreover `W*W=e_22 tensor d^2`, and
`Ideal(d^2)=Ideal(d)=I`.  Multiplication by the matrix units in the multiplier
algebra of `M_2(A)` shows

```text
Ideal(W)=M_2(I).
```

The final assertion follows immediately.  Thus the unresolved fusion step is
precisely a support-preserving destabilization, not the construction of a
square-zero element in the stabilized algebra.
