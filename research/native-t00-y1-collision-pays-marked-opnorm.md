---
rg: 2
id: native-t00-y1-collision-pays-marked-opnorm
kind: claim
title: Colliding the native t00 arm with Y1 pays marked operator norm
artifacts:
  - research/native-t00-y1-collision-payment-proof.md
  - experiments/native_t00_y1_collision_payment_audit.py
distinct_from:
  row2-parallel-a2-return-diamond-has-gl8-model: that identifies the two same-root occurrences x_78(t_00) and x_78(s_0t_00) in its finite GL8 model; this adds their literal root-additivity discrepancy and a uniform Leavitt sandwich returning that discrepancy to the marked root.
  binary-leavitt-nonzero-roots-have-uniform-corona-rank-scale: that gives a rank-germ comparison for every nonzero coefficient root; this writes the particular t00 discrepancy explicitly and obtains an operator-norm lower bound on the distance between the two named occurrences.
  middle-index-order-seven-orbit-cut-is-native-scale-neutral: that closes all ejected q-roots in a 128-dimensional scale-neutral packet; this uses the first coefficient-sensitive attachment outside that packet and quantitatively forbids its key same-root collapse.
---

**ESTABLISHED FULL-PRESENTATION OPNORM PAYMENT.**  In
`R=L_(F_2)(1,2)` put

```text
T=x_78(t_00),                  Y=x_78(s_0t_00),
d=t_00+s_0t_00,               D=TY=x_78(d).           (TYC1)
```

The coefficient `d` is nonzero and has the explicit one-sandwich inverse

```text
t_1 d (s_00s_1)=1.                                    (TYC2)
```

Indeed `d s_00=1+s_0`, then `t_1(1+s_0)=t_1`, and
`t_1s_1=1`.  Consequently the marked root is a product of four conjugates
of `D`.  More explicitly, after a constant Weyl word `K` moves `(7,8)` to
`(1,3)`, put

```text
A=x_41(t_1),               B=x_32(s_00s_1q),
q=s_1t_1.
```

Then

```text
[[A,KDK^(-1)],B]=x_42(q),                              (TYC3)
```

and a second constant Weyl word moves this output to `z=x_13(q)`.

Therefore every finite-dimensional unitary representation of this fixed
ordinary-root packet satisfies

```text
||rho(T)-rho(Y)||_op
 =||rho(D)-I||_op
 >=(1/4)||rho(z)-I||_op.                               (TYC4)
```

The same estimate holds with `o(1)` loss in an operator-norm microstate for
the fixed packet.  In particular, on any subsequence with
`||rho_n(z)-I||_op>=delta>0`,

```text
liminf ||rho_n(T)-rho_n(Y)||_op >=delta/4.              (TYC5)
```

There is also a positive marked carrier, not merely a global operator-norm
separation.  Let

```text
P_z=(1-rho(z))/2,                 P_D=(1-rho(D))/2.
```

The root positions `(1,3)` and `(7,8)` are disjoint, so `P_z` and `P_D`
commute.  The direct nonzero-root overlap estimate gives

```text
tau(P_zP_D)>=tau(P_D)/4>=tau(P_z)/16.                 (TYC6)
```

On `P_zP_D`, one has `TY=D=-1`, and hence

```text
||(T-Y)P_zP_D||_op=2                                  (TYC7)
```

whenever the common carrier is nonzero.  After active-core reblocking,
`(TYC6)` is a dimension-independent positive-rank payment; its rounded
microstate version loses only `o(1)` normalized mass.

This is the first full-presentation relation that excludes the exact
`GL_8(F_2)` escape in `row2-parallel-a2-return-diamond-has-gl8-model`:
that model assigns `T=Y`, hence `D=1`, while keeping the mark nonidentity.
It cannot extend to `(TYC1)--(TYC3)`.

The payment now lies on a fixed positive part of the marked carrier, but it
does not yet prove that this part meets the signed Hecke source.  The next
live occurrence must localize `P_zP_D` to the common center-chain Hecke
corner or show that escape from that corner itself pays a fixed return
defect.  No Property T, canonical trace, stability theorem, literature
input, or local computation is used.

DERIVATION
native-t00-y1-collision-payment-proof
