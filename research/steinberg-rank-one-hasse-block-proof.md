---
rg: 2
id: steinberg-rank-one-hasse-block-proof
kind: route
title: Convert the dense binomial block to a translation difference equation
target: steinberg-a-defect-isomorphism-on-rank-one-hasse-block
requires:
  - steinberg-standard-augmentation-filtration-firewall
---

For `2<=i<=p-2`, put `phi_i=[a^i c]`.  These are normal quotient-basis
classes and have zero point and plane marginals.  Exact reduction modulo
endpoint potentials gives

```text
T_A phi_i=cG_i(a),
G_i=a^i(1+2a)^(p-i)-(a-1/2)^i(2a)^(p-i).              (SRH1)
```

After imposing `a^p=a`, every `G_i` lies in
`span{a^2,...,a^(p-2)}`.  Suppose `sum_i t_iG_i=0` and define

```text
P(y)=sum_(i=2)^(p-2) t_i 2^(-i)y^i,
F(x)=(1+x)P(x/(1+x)),
```

where `F(-1)` is defined by the polynomial continuation of `(SRH1)`.  The
vanishing combination is exactly

```text
F(x)-F(x-1)=0                         on F_p.           (SRH2)
```

At `x=-1`, the zero extension gives `F(-1)=0`.  Translation invariance in
`(SRH2)` therefore forces `F=0`.  The fractional-linear map
`x |-> x/(1+x)` covers every `y!=1`, so `P` vanishes at `p-1` points.
Since `deg P<=p-2`, `P=0`, and all `t_i=0`.  Domain and range have the
same dimension, proving that `T_A|_S` is an isomorphism.

The coefficient of the top basis vector is particularly simple:

```text
coeff_(a^(p-2)) G_i = i 2^(p-i-2) !=0.                (SRH3)
```

Direct normal reduction of `T_B=(1-s^(-1))B^(-1)` gives zero on `phi_2`
and the scalar `2^(1-2i)` on `phi_i` for `i>=3`.  Thus the full projected
row `pi_S X^*|_S` is the explicit matrix recorded in
`steinberg-rank-one-schur-pivot-is-invertible`.
