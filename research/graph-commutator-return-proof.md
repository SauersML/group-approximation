---
rg: 2
id: graph-commutator-return-proof
kind: route
title: Compute the graph-reflection commutator exactly
target: graph-commutator-authenticates-paz-return
requires: []
---

In `M_2(M)` let

```text
p_+=1/2[[1,1],[1,1]],  R=p_+ tensor G,
U=diag(I,W),           X_R=2R-I.
```

In one further `2 by 2` amplification put

```text
A=diag(X_R,X_R),  B=[[0,U^*],[U,0]],  C=ABAB.
```

Set `eta=tau(G)-Re tau(GWG)` and
`b=||(I-G)WG||_2^2`.  If
`L=||(I-R)UR||_(2,tau_2)^2`, direct compression to the graph range gives

```text
L=eta/4+b/8.                                           (1)
```

Indeed, writing `s=tau(G)`, `r=Re tau(GWG)`, and
`a=||GWG||_2^2`, one has `eta=s-r`, `b=s-a`, and
`L=(3s-2r-a)/8`.  The two off-diagonal blocks of `U` relative to `R`
have equal HS norm, hence `||[U,R]||_2^2=2L`.  Since `X_R=2R-I`, unitary
invariance and the equal diagonal blocks of `C` yield

```text
||C-I||_2^2=4||[U,R]||_2^2=8L=2eta+b.                 (2)
```

Finally,

```text
b=||(I-G)(W-I)G||_2^2 <=||(W-I)G||_2^2=2eta.
```

Substitution in `(2)` proves both comparison inequalities.  If an
involution `Y` is coupled by `Y=C`, the same identity replaces the return
energy by the ordinary word distance `||Y-I||_2^2`; with mixed defect,
the triangle inequality gives the corresponding fixed-factor error bound.
