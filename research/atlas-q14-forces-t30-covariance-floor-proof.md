---
rg: 2
id: atlas-q14-forces-t30-covariance-floor-proof
kind: route
title: Compare q14 with t20 and polar-round to the t30 commutant
target: atlas-q14-forces-t30-covariance-floor
requires:
  - atlas-a4-packet-centralizer-product-compiler
artifacts:
  - experiments/atlas_q14_t30_wall.py
---

The exact radius-five replay verifies `(Q14-1)--(Q14-2)` and verifies directly
that `q_14` has trivial image in the binary Leavitt algebra.  In the aligned
regular representation,

```text
q_14(U)=(rho(t23) U rho(t30) U^*)^2.                  (1)
```

If `V in C_30(k)`, equation `(1)` and `(Q14-2)` give

```text
q_14(V)=rho_k(t20).
```

The regular character vanishes at the nonidentity involution `t20`, so

```text
||q_14(V)-1||_2=sqrt(2).                              (2)
```

Only the two second-chart occurrences depend on the relative unitary.  For a
fixed unitary `A`, bi-invariance gives

```text
||UAU^*-VAV^*||_2<=2||U-V||_2.
```

Telescoping the two occurrences in `(1)` therefore gives

```text
||q_14(U)-q_14(V)||_2<=4||U-V||_2.                   (3)
```

Equations `(2)--(3)` and the reverse triangle inequality prove `(Q14-DIST)`.

It remains to compare distance and covariance without losing dimension.  Put
`h=h_k` and decompose its space into the `+1` and `-1` eigenspaces.  Relative
to this decomposition write

```text
U=[A B; C D].
```

If the ambient dimension is `N`, then

```text
c^2:=||UhU^*-h||_2^2
    =||Uh-hU||_2^2
    =(4/N)(||B||_F^2+||C||_F^2).                     (4)
```

Polar-round `A` and `D` to unitaries `A_0,D_0` on the two diagonal blocks,
extending their polar partial isometries on the kernels.  Every singular value
`sigma in [0,1]` obeys `(1-sigma)^2<=1-sigma^2`.  Hence, with
`V=diag(A_0,D_0) in C_30(k)`, unitarity of `U` gives

```text
||U-V||_2^2
 <=(1/N)[N_+-||A||_F^2+N_--||D||_F^2
          +||B||_F^2+||C||_F^2]
 =(2/N)(||B||_F^2+||C||_F^2)
 =c^2/2.                                               (5)
```

Taking the infimum in `(5)` proves `(Q14-COV)`.  This distance estimate is
useful but is not the sharp root-energy bound.

For the sharp estimate put

```text
a=rho_k(t23),
b=U h U^*,
p=(1-h)/2,
r=(1-b)/2.
```

Then `q_14(U)=abab`, and right multiplication by `b` gives

```text
||ara-r||_2=(1/2)||aba-b||_2
           =(1/2)||q_14(U)-1||_2=epsilon_14(U)/2.     (6)
```

Write `r=[A B;B^* D]` in the `+1/-1` decomposition for `a`.  Spectrally round
the positive contractions `A,D` at `1/2` to projections `A_0,D_0`, and put
`s=diag(A_0,D_0)`.  The projection equations give

```text
A-A^2=BB^*,
D-D^2=B^*B.
```

For `lambda in [0,1]`,
`min(lambda^2,(1-lambda)^2)<=lambda(1-lambda)`.  Therefore

```text
||r-s||_2^2
 <=(4/N)||B||_F^2
 =(1/2)||ara-r||_2^2
 <=epsilon_14(U)^2/8.                                (7)
```

The projection `s` commutes with `a`.  Now average `p` over this involution:

```text
E_a(p)=(p+apa)/2=1/2-(h+aha)/4.                       (8)
```

The exact matrix audit gives `|ah|=4` and `(ah)^2=t20!=1`.  Hence `h` and
`aha` are distinct commuting involutions and generate a Klein four group.
The regular character gives trace `1/4` to each of its four joint character
spaces.  Thus the spectral distribution of `E_a(p)` is

```text
eigenvalue       0       1/2       1
trace weight    1/4      1/2      1/4.                (9)
```

Since `s` commutes with `a`, traciality gives
`tau(sp)=tau(sE_a(p))`.  The elementary decreasing rearrangement of `(9)`
implies, for every such projection `s`,

```text
tau(sp)<=3/8+|tau(s)-1/2|.                            (10)
```

Put `eta=||r-s||_2`.  Since `tau(r)=tau(p)=1/2`, Cauchy--Schwarz and
`||p||_2=1/sqrt(2)` give

```text
tau(rp)
 <=tau(sp)+eta/sqrt(2)
 <=3/8+(1+1/sqrt(2))eta.                              (11)
```

Finally,

```text
x_30(U)^2
 =1-Re tau(bh)
 =2-4tau(rp).                                         (12)
```

Substitute `(7)` into `(11)--(12)` to obtain

```text
x_30(U)^2>=1/2-(1+sqrt(2))epsilon_14(U).
```

Together with nonnegativity this proves `(Q14-ROOT)`.  Also
`||UhU^*-h||_2^2=2x_30(U)^2`, proving the two sharp limiting statements in
`(Q14-WALL)`.

For completeness, sharpness can be realized canonically.  Let `e_(sigma,tau)`
be the four joint character projections of `<h,aha>`, put

```text
e_mid=e_(+,-)+e_(-,+)=(1-(ah)^2)/2,
f=e_mid(1+a)/2,
s=e_(-,-)+f.
```

Conjugation by `a` exchanges the two middle joint-character spaces and fixes
`e_(-,-)`, so `e_mid` and `e_(-,-)` commute with `a`.  The regular character
also gives `tau(e_mid a)=0`; hence `f` is an `a`-commuting projection of trace
`1/4`.  Thus `s` commutes with `a`, has trace `1/2`, and satisfies
`tau(sp)=1/4+(1/2)(1/4)=3/8`.  It is unitarily conjugate to `p`, so the
corresponding `U` has `q_14(U)=1` and `x_30(U)^2=1/2`.
