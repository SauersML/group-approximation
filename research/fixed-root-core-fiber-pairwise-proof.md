---
rg: 2
id: fixed-root-core-fiber-pairwise-proof
kind: route
title: Compare each cubic row to its inversion row through the shared transported core ratio
target: fixed-root-exact-core-fiber-has-pairwise-row-coercivity
requires: []
---

Put `q=R_1R_0^(-1)`.  Since both implementers send `T` to `T^4`, the same
calculation as in the exact one-sided slice gives `q in {T}'`.  Set

```text
A=XR_0,           B=XT^2R_0,        d=XqX,
p=R_0^(-1)qR_0,   alpha=Ad(A),      beta=Ad(B),
W=A^2=W_0,        V=B^3=V_0.                         (FRP1)
```

No endpoint row is assumed exact.  Direct conjugation gives

```text
alpha(d)=W p W^(-1),
beta^(-1)(d)=p,
beta^2(d)=V p V^(-1).                                (FRP2)
```

Since `XR_1=dA` and `XT^2R_1=dB`, expanding the powers and using `(FRP2)`
gives exact finite-difference formulas

```text
W_1=(dA)^2=dWp,
V_1=(dB)^3=d beta(d)Vp.                              (FRP3)
```

Consequently

```text
V_1 W_1^(-1)=d beta(d)V W^(-1)d^(-1).                (FRP4)
```

The matrix `d beta(d)d^(-1)` is at distance exactly `||q-1||_2` from the
identity, because `beta` and conjugation are trace-preserving isometries and
`d=XqX`.  Comparing it with `(FRP4)` therefore yields

```text
||q-1||_2
 <=||V_1W_1^(-1)-1||_2+||VW^(-1)-1||_2
 = ||V_1-W_1||_2+||V_0-W_0||_2,                     (FRP5)
```

which is `(FRC3)`.  Finally
`||V_i-W_i||_2^2<=2(||V_i-1||_2^2+||W_i-1||_2^2)`;
squaring `(FRC3)` proves `(FRC4)`.

For `(FRC6)`, conjugate the first core by `z`.  It becomes
`(zR_0z^*,T_1)`, while `[z,X]=0` makes both of its row values the conjugates
by `z` of the original row values.  Their normalized-HS energy is therefore
still `e_0`.  Apply `(FRC4)` to this conjugated core and `(R_1,T_1)`.
