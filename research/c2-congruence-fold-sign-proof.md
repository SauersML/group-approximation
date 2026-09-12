---
rg: 2
id: c2-congruence-fold-sign-proof
kind: route
title: Eliminate all two-sheet signs with one Weyl conjugacy and the torus word
target: rank-one-conjugacy-kills-c2-congruence-fold
requires:
  - closed-a2-loop-still-leaves-swap-fold-free
  - two-torus-closures-detect-denominator-multiplicity
---

Use the lowercase congruence matrices `e_ij,b_ji,w_ij` and `K=rho(h)` from
`(CAP1)`.  Write the four possible sheet signs as

```text
E_12=Z^(p_12) tensor e_12,       B_21=Z^(q_12) tensor b_21,
E_23=Z^(p_23) tensor e_23,       B_32=Z^(q_23) tensor b_32,  (CSP1)
```

where every exponent lies in `Z/2`.  The doubled-root and Weyl definitions
give

```text
A_12=1 tensor a_12,              W_12=Z^(q_12) tensor w_12,
A_23=1 tensor a_23,              W_23=Z^(q_23) tensor w_23. (CSP2)
```

Indeed each doubled root contains its positive-root sign twice, while each
Weyl word `E_ij B_ji E_ij` contains the sign of `B_ji` and two copies of the
sign of `E_ij`.

In the first equality of `(RCK2)`, the two `W_12` signs cancel under
conjugation.  Its left side therefore has sheet sign `Z^(p_23)`, whereas the
commutator on the right has no sheet sign.  Hence

```text
p_23=0.                                                (CSP3)
```

Likewise the second return in `(RCK2)` gives

```text
p_12=0.                                                (CSP4)
```

Now evaluate `(RCK3)`.  The two `W_12` signs again cancel, so its left side
has sheet sign `Z^(p_12)`, while its right side has sign `Z^(q_12)`.  The
underlying congruence equality is
`w_12 e_12 w_12^*=b_21`; therefore `(CSP4)` implies

```text
q_12=p_12=0.                                          (CSP5)
```

Only `q_23` remains.  Put

```text
V=GZG^*Z.                                              (CSP6)
```

The exact congruence factors in the two torus closures multiply to `K`, by
`(TTC3)`.  From `(CSP2)` and `(CSP5)`, their sheet factors are respectively

```text
1,                         V^(q_23).                   (CSP7)
```

Thus `R_tor=1`, equivalently `D_12D_23=H=G tensor K`, reduces exactly to

```text
V^(q_23)=G.                                            (CSP8)
```

If `q_23=0`, this says `G=1`.  If `q_23=1`, then

```text
GZG^*Z=G.
```

Multiplying on the left by `G^*` gives `ZG^*Z=1`, again implying `G=1`.
Therefore `G=1` in both cases.  Equation `(RCK4)` follows immediately, since
the congruence factor `K` commutes with the sheet involution `S`.

The same calculation gives `(RCK5)--(RCK6)` without assuming the torus word
exact.  Because the actor factor is still exact and unitary invariance removes
it,

```text
eta=||R_tor-1||_2=||V^(q_23)-G||_2.                   (CSP9)
```

If `q_23=0`, `(CSP9)` is exactly `||G-1||_2=eta`.  If `q_23=1`, then

```text
G^*V=ZG^*Z,
```

so unitary invariance again gives

```text
||G-1||_2=||ZG^*Z-1||_2=||V-G||_2=eta.               (CSP10)
```

In either case the actual fold is `F=GZG^*Z=V`, and

```text
||F-1||_2<=2||G-1||_2<=2 eta,
||F^2-1||_2<=2||F-1||_2<=4 eta.                       (CSP11)
```

Finally the exact two-projection identity

```text
tr(QPQ-(QPQ)^2)=(1/32)||F^2-1||_2^2
```

turns `(CSP11)` into `(RCK6)`.

For the particular packet `(CAP5)`, the failure of `(RCK3)` is visible before
any calculation: its left side is

```text
1 tensor (w_12e_12w_12^*)=1 tensor b_21,
```

while `B_21=Z tensor b_21`.  Hence `(RCK3)` is a single genuine lattice
identity which detects exactly the negative-root/Weyl sheet sign used there.
