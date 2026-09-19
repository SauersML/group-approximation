---
rg: 2
id: atlas-q14-growing-width-rank-one-bridge-is-sharp
kind: claim
title: At square-root phase width one rank-one q14-exact bridge can generate the full coefficient algebra
distinct_from:
  atlas-q14-exact-allows-full-coefficient-cyclicity: that constructs a full coefficient algebra directly at width m; this realizes the full algebra by a rank-one perturbation of a width-s amplified phase and identifies the square-root transition.
  atlas-fixed-width-phases-resist-low-rank-bridging: that rules out low-rank bridges when the phase width is fixed; this proves the width dependence is essential and qualitatively sharp.
  atlas-packet-collision-m2-has-full-coefficient-algebra: that satisfies the twelve packet cubes and collision at multiplicity two but fails q14; this satisfies q14 at arbitrary growing multiplicity but makes no assertion about the other thirteen relations.
---

ESTABLISHED.  Let `s>=k`, put

```text
W=F2^s,  K=F2^k,  M=W tensor K,  m=sk.               (GWB1)
```

There are chart changes `T0,T in GL_4(M_m(F2))` such that

1. `rank(T-T0)=1`;
2. the coefficient algebra of `T0` is
   `End(W) tensor I_K`, a width-`s` amplified phase;
3. the coefficient algebra `C_T` is all of `M_m(F2)`;
4. `T` centralizes the marked transvection nilpotent `E23 tensor I_M`, so
   q14 is exact.

In particular, any nonzero one-dimensional seed is `C_T`-cyclic.  Taking
`s=k` gives `m=s^2`: a single rank-one bridge can escape a phase whose width
is of order `sqrt(m)`.  Combined with
`atlas-fixed-width-phases-resist-low-rank-bridging`, this makes the
square-root scale qualitatively sharp.  The construction does **not** make
the twelve packet cubes or collision small; those thirteen formulas are now
the whole relation-specific obstruction to turning it into an Atlas
countermodel.

### Construction

Choose `X,Y in End(W)` generating `End(W)`, for example the nilpotent shift
and wrap matrix

```text
X=sum_(i=1)^(s-1) E_(i,i+1),     Y=E_(s,1).           (GWB2)
```

Put `X0=X tensor I_K`, `Y0=Y tensor I_K`.  Choose vectors
`u_1,...,u_s` spanning `K` and covectors `phi_1,...,phi_s` spanning `K^*`,
and set

```text
u=sum_i e_i tensor u_i,
phi=sum_j e_j^* tensor phi_j,
R=u phi.                                               (GWB3)
```

Thus `rank R=1`.  On `F2^4 tensor M`, define

```text
T0=I+E13 tensor X0+E14 tensor Y0,
T =T0+E24 tensor R.                                   (GWB4)
```

The three matrix units `E13,E14,E24` have pairwise-zero products.  Hence
`T0^2=T^2=I`, so both chart changes are invertible and self-inverse, and

```text
rank(T-T0)=rank(E24 tensor R)=1.                      (GWB5)
```

Their blocks and diagonal inverse blocks show

```text
X0,Y0 in C_(T0),
X0,Y0,R in C_T.                                       (GWB6)
```

The first two elements generate `End(W) tensor I_K`.  For all indices,
sandwiching the last element gives

```text
(E_(a,i) tensor I) R (E_(j,b) tensor I)
   =E_(a,b) tensor u_i phi_j.                         (GWB7)
```

Because the `u_i` span `K` and the `phi_j` span `K^*`, the operators
`u_i phi_j` span `End(K)`.  Therefore `(GWB7)` spans
`End(W) tensor End(K)=End(M)`, proving `C_T=M_m(F2)`.

Finally, each of `E13,E14,E24` commutes with `E23`; hence both `T0` and `T`
centralize `E23 tensor I_M`.  The two marked transvections coincide, so
their q14 commutator relation is exact.

### Quantitative boundary

For an `r`-rank perturbation of a width-`s` phase,
`atlas-fixed-width-phases-resist-low-rank-bridging` gives

```text
m <= s^2(dim U+512r)                                  (GWB8)
```

whenever `U` is cyclic.  Thus a rank-one bridge from a one-dimensional seed
requires `s` at least a constant multiple of `sqrt(m)`.  The construction
above works at `s>=k`, and hence at `s=sqrt(m)`, up to that constant.
