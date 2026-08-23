---
rg: 2
id: affine-frobenius-common-negative-carrier
kind: claim
title: Correlate each variable's Frobenius packets on one common negative carrier
distinct_from:
  affine-frobenius-algebraic-projection-crt: that permits an arbitrary algebraic projection solving the incidence right ideals; this asks for the sharper high-density normal form in which every negative masked incidence projection is literally the same projection.
  affine-frobenius-tight-defect-column-frame: that is phrased as a cubic scaled-partial-isometry identity; high-density tight-frame collapse shows that its genuinely surviving case is the common carrier requested here.
---

**OPEN.**  Correlate the fixed affine-Frobenius context packets, without
changing their context PVMs, so that for every source variable `x` there is
one finite-support projection `p_x` satisfying

```text
p_x=p_x^*=p_x^2,
((1-A_(c,x))/2)q_(c,x)=p_x                 for every c containing x.  (AFNC1)
```

The packet embeddings and the strict weighted canonical predicate and
consistency deficit budget of
`rowwise-hecke-crt-certificate-for-nonce-bcs` must be preserved.

Since the left side of `(AFNC1)` is a projection below `q_(c,x)`, the
identity implies `p_x<=q_(c,x)`.  The reflection

```text
B_x=1-2p_x                                                        (AFNC2)
```

then obeys

```text
B_xq_(c,x)=A_(c,x)q_(c,x)                            (AFNC3)
```

for every incidence.  Thus `(AFNC1)` is already an algebraic Hecke-CRT
solution.

This is not a demand that the whole masks have a common meet.  It identifies
only their prescribed negative pieces, separately for each variable.  The
remaining difficulty is the cycle holonomy/global compatibility of these
variable-specific carriers with the fixed nonaffine context PVMs.  A tree or
finite Bass--Serre gluing cannot meet the strict BCS budget.

There is no hidden additive-overlap shortcut.  By
`common-carrier-lives-in-packet-intersection`, once the finite context
groups embed in one ambient group, `p_x` must lie in the group algebra of
their literal finite subgroup intersection.  The required construction is
therefore a finite-overlap cycle whose holonomy leaves the Bass--Serre class
without collapsing a packet or the strict deficit.
