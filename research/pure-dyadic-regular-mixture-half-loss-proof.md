---
rg: 2
id: pure-dyadic-regular-mixture-half-loss-proof
kind: route
title: Compute the tridiagonal conductor table and its weighted Cheeger constant
target: pure-dyadic-regular-iwahori-mixtures-have-a-uniform-half-loss
requires: []
---

Write an element of `B` as

```text
gamma=[[x,y],[z,w]],             z even.
```

The commensuration sends it to

```text
sigma(gamma)=[[x,2y],[z/2,w]].                         (DRP1)
```

Thus `N_a` is defined by

```text
x,w=1 mod 2^a,       y,z=0 mod 2^a,                   (DRP2)
```

whereas `M_b` is defined by

```text
x,w=1 mod 2^b,       y=0 mod 2^(b-1),
z=0 mod 2^(b+1).                                      (DRP3)
```

This proves `(DRI2)`. At equal depth the image of `M_a` in `B/N_a` has
order exactly two: only `y=2^(a-1)` can survive, and the corresponding upper
unipotent realizes the nonzero class. The quotient orders of `N_a` and
`M_a` agree, so `(DRI3)` follows.

Reduction modulo two has kernel of order `2^(3(a-1))`, and the Iwahori image
has index three in `SL_2(Z/2^a)`. Hence

```text
|B/N_a|=|B/M_a|=2^(3a-2).                              (DRP4)
```

For normal finite-index subgroups `N,M`, the common irreducibles of `B/N`
and `B/M` are precisely those of `B/(NM)`. Therefore

```text
F(a,b):=sum_(n<=a,m<=b)w_(n,m)=|B/(N_aM_b)|
 = 2^(3a-2)       if b>=a+1,
   2^(3a-3)       if b=a,
   2^(3b-2)       if a>=b+1.                           (DRP5)
```

Taking the two-variable finite difference of `(DRP5)` gives `(DRI4)`. In
particular, if

```text
c_n=8^(n-1),
v_1=2,                  v_n=(7/4)c_n  (n>=2),          (DRP6)
```

then `v_n=sum_m w_(n,m)=sum_m w_(m,n)` is the total upper or opposite exact
conductor-`n` Plancherel weight.

Restriction of `lambda_a` to `B` is `3 Reg(B/N_a)`. Define the tail
multiplicities

```text
R_n=3 sum_(a>=n)r_a,       S_m=3 sum_(b>=m)s_b.        (DRP7)
```

An irreducible of conductor pair `(n,m)` has multiplicities
`dim(theta)R_n` and `dim(theta)S_m` on the two sides. Consequently

```text
D_+=sum_n v_nR_n,             D_-=sum_m v_mS_m,
L=sum_(n,m)w_(n,m)|R_n-S_m|,
common=(D_++D_--L)/2.                                  (DRP8)
```

Discard the nonnegative diagonal terms from `L`. The remaining graph is the
disjoint union of two alternating rays

```text
R_1--S_2--R_3--S_4--...,
S_1--R_2--S_3--R_4--...,
```

whose edge from depth `n` to `n+1` has weight `c_n`. Give a depth-`n`
vertex weight `v_n`. This weighted graph has Cheeger constant exactly
`1/2`. Indeed an initial segment through depth `N` has boundary `c_N` and
mass

```text
v_1+...+v_N=2c_N.                                      (DRP9)
```

Every other finite interval has at least the same boundary-to-mass ratio,
and splitting into intervals only increases boundary. The layer-cake
formula therefore gives

```text
L >= (1/2)(D_++D_-).                                  (DRP10)
```

When `D_+=D_-=d`, `(DRP8)--(DRP10)` give `common<=d/2`, proving `(DRI5)`.
The single-level values follow directly from `(DRP5)`.

For `(DRI6)`, let `E` project normalized Hilbert--Schmidt operators onto the
exact intertwiner space. The common-support bound and contractivity of the
finite-group average give `||E(V)||_2^2<=1/2` for every unitary `V`, hence
`||V-E(V)||_2>=1/sqrt(2)`. The left-right action factors through a congruence
quotient of the fixed subgroup `B`; Selberg `(tau)` supplies the uniform
Poincare constant `kappa_B`.

