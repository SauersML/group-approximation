---
rg: 2
id: positive-toeplitz-head-is-square-defect-or-rectangular-escape
kind: claim
title: Positive Toeplitz head mass is a square-reservoir defect or an exact rectangular escape
distinct_from:
  toeplitz-self-embedding-fixes-unbounded-congruence-types: that constructs high-degree square congruence representations on which the head defect vanishes; this proves quantitatively that positive head mass excludes that branch only after source and target have been authenticated as one square reservoir.
  mixed-steinberg-loops-admit-morita-rectangular-model: that realizes arbitrary pasted mixed root triangles in a many-object linear category; this isolates the two Toeplitz inverse equations and gives the sharp normalized-HS payment in the square case.
  approximate-relative-leavitt-cell-kills-active-trace: that uses the two-branch Leavitt return and range-sum identities on one projection; this is the one-sided Toeplitz head equation and explicitly identifies rectangular reservoir change as the unique trace-cyclicity escape.
---

Let `(M,tau)` be a finite tracial matrix algebra, let `P in M` be a
projection, and let `X,Y in M` be contractions.  Put

```text
epsilon_left = ||YX-1||_2,
epsilon_head = ||P-(1-XY)||_2.                          (PTH1)
```

Then

```text
tau(P) <= epsilon_left+epsilon_head,
epsilon_left^2+epsilon_head^2 >= tau(P)^2/2.            (PTH2)
```

Thus, once the Toeplitz source and target have been decoded on the **same
finite matrix reservoir**, positive forbidden-head mass quantitatively
excludes the stationary congruence collapse and pays one of the two named
coefficient defects.  No property `(T)`, bounded-type theorem, or Schur
commutant estimate is needed at that point.

The same statement is false for a rectangular decoder, sharply and with
zero error.  For finite-dimensional spaces `E` and `H!=0`, put

```text
F=E direct_sum H,
S:E->F  the coordinate inclusion,
T:F->E  the coordinate projection,
P_H=projection of F onto H.                             (PTH3)
```

Then

```text
TS=1_E,                  ST=1_F-P_H,                    (PTH4)
```

while `tr_F(P_H)>0`.  Hence a Fourier/shear decoder which represents the
two identities on different label-times-multiplicity reservoirs can retain
arbitrary positive head mass with zero Toeplitz defect.  In a common block
matrix these are corner identities, not the same global identity.

This gives the exact dichotomy required by the stationary congruence
falsification test:

```text
same square reservoir + positive head  => named HS payment;
unpaid positive head                   => rectangular reservoir escape.
                                                               (PTH5)
```

Consequently `toeplitz-tail-retains-contextual-schur-density` does not need
a new scalar inequality.  Its remaining content is precisely a
matrix-coordinate authentication that the residual tail shear returns to
the same reservoir, or a word defect charging the change of reservoir.
Positive forbidden mass alone does not imply bounded old-group type mass;
without that authentication it can live in the exact rectangular model.
