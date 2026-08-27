---
rg: 2
id: mixed-cross-zero-four-state-gauge-proof
kind: route
title: Rotate two overlapping source packets to complementary target supports
target: mixed-cross-zero-squares-have-four-state-gauge-model
requires:
  - cross-zero-breaks-reverse-whitehead-support-fusion
  - reverse-product-whitehead-fold-has-finite-fusion
---

The projections in `(MCZ1)` are diagonal and commute.  Their symmetric
difference is

```text
P_0+P_1-2P_0P_1=diag(1,0,1,0)=P_A,
```

which proves the fold and the rank statements.  Swapping `e_2,e_4` sends
`P_1` to `diag(0,0,1,1)`, proving `(MCZ3)`.

Controlled packet multiplication is pointwise on the four joint spectral
atoms.  For the base involution `w`, a vector in both `P_0,P_1` receives
`w^2=1`, a vector in exactly one child receives `w`, and a vector in neither
receives one.  This is precisely control by the symmetric difference
`P_A`, proving `(MCZ5)`.  The same calculation applies to the positive root
signs and gives the source fold.

Conjugation satisfies

```text
(U_i tensor 1) g[P_i] (U_i^* tensor 1)=g[Q_i]          (1)
```

for every base occurrence `g`, including both factors of every opposite-root
Whitehead.  This proves all mixed occurrence squares.  If `a,b` are the two
composable base roots, then `a[Q_0]` and `b[Q_1]` act nontrivially on
orthogonal carrier subspaces and hence commute, proving the crossed-zero
row.

All three source projections have rank two.  Any fixed native label
transport between the parent and a child can therefore be tensored with a
carrier unitary taking `P_A` onto `P_i`; equation `(1)` again transports
the whole packet.  Finally, choose a vector in `P_AH_0` and a base vector on
which the parent root is nonidentity.  The controlled parent packet acts
nontrivially there, whereas every listed discrepancy is exactly one.

Since `P_0P_1` is the rank-one projection onto `e_2`, `(MCZ6)` fails with
left side one and right side zero.

