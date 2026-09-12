---
rg: 2
id: asymmetric-prefix-unit-whitehead-conjugacy-proof
kind: route
title: Expand the prefix rotation and its elementary torus conjugator
target: asymmetric-prefix-unit-conjugates-native-whiteheads
requires:
  - literal-prefix-coupling-of-j1-j2-has-gl7-model
  - b2-b3-pair-full-hecke-four-native-sectors
---

For binary words use `t_(ij)=t_jt_i`.  Orthogonality and completeness of
the two prefix codes give

```text
u^(-1)u=e_0+e_10+e_11=1,
uu^(-1)=e_00+e_01+e_1=1,                              (1)
```

so `(APU1)` is indeed a unit and the displayed second sum is its inverse.

For the first forward coefficient, all cross-prefix products vanish and

```text
u s_00=s_000,                 t_0u^(-1)=t_00.         (2)
```

Thus `u(s_00t_0)u^(-1)=s_000t_00=x_2`.  Likewise

```text
u s_0=s_00,                   t_00u^(-1)=t_000,       (3)
```

which gives `u(s_0t_00)u^(-1)=s_00t_000=y_2`.  This
proves `(APU3)` using only the binary Leavitt relations.

For a ring unit `a`, define

```text
w_(i,k)(a)=x_(i,k)(a)x_(k,i)(a^(-1))x_(i,k)(a),
h_(i,k)(a)=w_(i,k)(a)w_(i,k)(1)^(-1).                 (4)
```

After the canonical map to the elementary group, `h_(i,k)(a)` is diagonal
with entries `a,a^(-1)` in coordinates `i,k` and identity elsewhere (the
usual signs disappear in characteristic two).  The two factors in `(APU4)`
have disjoint supports.  Hence, for every coefficient `b`,

```text
D x_87(b)D^(-1)=x_87(ubu^(-1)),
D x_78(b)D^(-1)=x_78(ubu^(-1)).                       (5)
```

Applying `(5)` to the three factors of `J_1` and then using `(APU3)` gives

```text
DJ_1D^(-1)=x_87(x_2)x_78(y_2)x_87(x_2).              (6)
```

Constant Weyl words implement every even coordinate permutation after one
spare coordinate is included.  Choose their ordinary product `P` to act by
the cycle `(7 8 9)`.  It sends the root positions `(8,7),(7,8)` to
`(9,8),(8,9)`.  Conjugating `(6)` by `P` proves `(APU7)`.

Finally group elements act unitarily in every exact representation.  For
`C=GF`,

```text
C^*C=FG^*GF=F,
CC^*=GFG^(-1)=F'.                                     (7)
```

Using `GJ_1=J_2G`, `J_i^2=1`, and `GF=F'G` gives every identity in
`(APU9)`.  No invariance of `F` under `G` is asserted or used; that moved
source is exactly the remaining fixed-frame seam.
