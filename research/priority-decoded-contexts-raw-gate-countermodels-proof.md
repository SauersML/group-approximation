---
rg: 2
id: priority-decoded-contexts-raw-gate-countermodels-proof
kind: route
title: Two exact countermodels separate raw gates from their priority-decoded observables
target: priority-decoded-contexts-are-not-glued-by-raw-gate-equality
requires: []
---

Use normalized trace on `M_2(C)` and put

```text
P = diag(1,0),       R=1-P.
```

In context `c` take the exact one-hot selector projections `(P,1-P)`; in
context `d` take `(R,1-R)`.  Equivalently,

```text
Z_(c,1)=1-2P,       Z_(c,2)=2P-1,
Z_(d,1)=1-2R,       Z_(d,2)=2R-1.
```

The selector product is `-1` in both contexts, so the even-parity loss is
zero.  Set, branch by branch in both contexts,

```text
G_1=1,       G_2=-1.
```

These scalar gates commute with every selector and the two cross-context raw
gate equalities hold exactly.  Priority decoding (in branch order `1,2`) is
ordinary one-hot decoding here and gives

```text
U_c=P-(1-P)=2P-1,
U_d=R-(1-R)=2R-1=-(2P-1).
```

Therefore `(U_c-U_d)^*(U_c-U_d)=4`, and hence
`||U_c-U_d||_2^2=4`.  Thus no inequality can bound decoded mismatch by only
the two parity defects and branchwise raw-gate equality defects.

For the aggregate proposal, work already in the scalar algebra `C`.  Take
three selectors `Z_1=Z_2=Z_3=-1`.  Their product is `-1`, so odd parity is
exact, and priority assigns the unique scalar atom to branch `1`.  Take

```text
G_1=-1,       G_2=-1,       G_3=1.
```

Then the priority-decoded observable is `G_1=-1`, whereas
`G_1G_2G_3=+1`.  The aggregate relation can therefore identify a shared
observable with `+1` at zero defect while its decoded copy differs by squared
Hilbert--Schmidt distance `4`.

For the completeness statement, direct expansion of the canonical gates
gives

```text
G_P-G_R = [1+P(U-1)]-[1+R(U-1)] = (P-R)(U-1).
```

For example, with the above complementary `P,R` and `U=-1`, the two gates are
`1-2P` and `1-2R=-(1-2P)`, hence are unequal.  All assertions follow.
