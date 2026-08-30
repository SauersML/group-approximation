---
rg: 2
id: clean-face-restriction-bessel-packing-proof
kind: route
title: Turn clean-face orthogonality into orthogonal restricted characters and apply Bessel
target: clean-face-finite-type-packing-is-quadratically-bounded
requires:
  - finite-type-restriction-overlap-defect-formula
  - finite-type-subprojection-forces-large-root-intersection
---

Write

```text
v=Res^K_L pi,             u_a=Res^(A_a)_L alpha_a,
d_a=dim(alpha_a).
```

Because `p_a<=q` and `K intersect A_a=L`, the full-overlap computation
`(LRI3)` gives

```text
<v,u_a>_L=d_a s/d.                                      (CFP8)
```

For `a!=b`, the exact restriction-overlap formula and
`A_a intersect A_b=L` give

```text
0=tau_Gamma(p_a p_b)
 =d_a d_b |L|/(|A_a||A_b|) <u_a,u_b>_L.                (CFP9)
```

The prefactor is positive, so the nonzero restricted characters `u_a` are
pairwise orthogonal in the Hilbert space of class functions on `L`.
Bessel's inequality therefore yields

```text
sum_a |<v,u_a>|^2/||u_a||^2 <= ||v||^2=r.              (CFP10)
```

If `u_a=sum_theta m_(a,theta) theta`, then

```text
||u_a||^2=sum_theta m_(a,theta)^2
 <=(sum_theta m_(a,theta) dim(theta))^2=d_a^2.          (CFP11)
```

Combining `(CFP8)--(CFP11)`, every summand on the left of `(CFP10)` is
at least

```text
(d_a^2 s^2/d^2)/d_a^2=s^2/d^2.
```

This proves the first inequality in `(CFP4)`. Applying the same elementary
character estimate to `v` gives

```text
r=||v||^2<=dim(pi)^2=d^2,
```

which proves the second inequality and `(CFP5)`. Formula `(CFP6)` is the
case `n>=2`. If `s=d^2`, then `(CFP4)` reads
`n d^2<=r<=d^2`, so `n<=1`, proving the partition obstruction and the
extraspecial consequence.
