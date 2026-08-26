---
rg: 2
id: rank-one-closure-reduces-to-noncentral-gauge
kind: claim
title: Rank-one closure reduces congruence-sheet enemies to noncentral gauges
artifacts:
  - research/rank-one-near-central-gauge-proof.md
distinct_from:
  rank-one-conjugacy-kills-c2-congruence-fold: that treats exact discrete C2 signs and is torus-robust inside that sector; this allows arbitrary noncommuting sheet unitaries and proves collapse whenever they approach the block-scalar center.
  rank-one-closure-excludes-noncentral-outlier-gauges: that asks for the still-open exclusion of gauges uniformly far from block scalars and of non-congruence actor outliers; this proves the complementary near-central sector.
  sl3-swap-extension-has-defect-only-fold-square-rigidity: that quantifies over arbitrary approximate assignments of the full presentation; this theorem keeps the actor factor exact and assumes the displayed rank-one and closed-A2 equations exact.
---

Let `rho` be an exact odd-level congruence representation and tensor its
displayed root slots with arbitrary sheet unitaries

```text
P,R,Q,T in U(K_sh) intersect {S}',                    (NCG1)
```

assigned respectively to `E_12,E_23,B_21,B_32`.  Put

```text
U=PQP,                 V=RTR,                 C=[P,R]. (NCG2)
```

The two Weyl definitions, the rank-one conjugacy, and the closed `A_2` loop
are exact if and only if the sheet gauges satisfy

```text
UPU^*=Q,
URU^*=C=V^*PV.                                         (NCG3)
```

In particular `PQP=QPQ`.  Since every gauge commutes with `S`, the sheet
space decomposes as

```text
K_sh=K_+ direct-sum K_-                              (NCG4)
```

and `(NCG2)--(NCG3)` hold independently on the two blocks.  They do **not**
force scalarity: an exact congruence root packet on either block is a
noncommutative solution.

They do give a quantitative reduction.  Suppose there are central sheet
unitaries

```text
P_0,R_0,Q_0,T_0 in Z({S}')
```

such that

```text
max(||P-P_0||_2,||R-R_0||_2,||Q-Q_0||_2,||T-T_0||_2)
 <=epsilon.                                            (NCG5)
```

Let `H=G tensor rho(h)` and allow only the unbalanced torus word to have
defect

```text
eta=||R_tor-1||_2.                                    (NCG6)
```

Then, with `F=HSH^*S`,

```text
||G-1||_2<=eta+184 epsilon,
||F-1||_2<=2(eta+184 epsilon),
||F^2-1||_2<=4(eta+184 epsilon),                       (NCG7)

tr(Q_f P_f Q_f-(Q_f P_f Q_f)^2)
 <=(1/2)(eta+184 epsilon)^2,                           (NCG8)
```

where `P_f=(1-S)/2` and `Q_f=HP_fH^*`.  The constant is deliberately coarse
but dimension-free.

Consequently a sequence with vanishing torus defect and a fixed positive
fold-square or Gram defect must keep its sheet gauges a fixed normalized-HS
distance from the block-scalar center.  The residual is precisely a genuinely
noncentral multiplicity gauge; central phases and asymptotically central
block gauges are both closed.

DERIVATION
rank-one-near-central-gauge-proof

