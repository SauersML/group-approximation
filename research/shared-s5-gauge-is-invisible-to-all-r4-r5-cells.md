---
rg: 2
id: shared-s5-gauge-is-invisible-to-all-r4-r5-cells
kind: claim
title: Every valid R4/R5 cell is blind to the shared-S5 extension gauge
invalidates:
  - mixed-r5-energy-kills-s5-extension-gauge
distinct_from:
  shared-s5-selector-face-has-multiplicity-rotation-gauge: that gives one explicit multiplicity rotation preserving the common S5 face and its selector commutators; this classifies every label-valid disjoint-support cell across the two extensions and shows why none can see such a rotation.
  bare-r5-a6-collision-does-not-synchronize-shared-labels: that gives one five-dimensional A6 countermodel for the nonshared Carmichael collision; this works for arbitrary representations of S6 agreeing on the point stabilizer and for every R4/R5 disjointness placement.
  mixed-r2-cell-couples-shared-s5-extension-multiplicities: that gives a cross-extension overlapping-support relation whose defect equals the missing-arm mismatch; this proves disjoint-support relations cannot provide an alternative coupling.
---

Let

```text
G=Sym(Omega),       Omega={i,p,j,k,l,q},
H=Sym(Omega setminus {i}),
rho_0,rho_1:G->U(d),              rho_0|_H=rho_1|_H,             (RGI1)
```

and suppose `rho_1=U rho_0 U^*` for a unitary
`U in rho_0(H)'`.  This is precisely the residual extension gauge after the
common `S_5` face has been aligned.

Take any two disjoint transpositions `a,b in G`, and evaluate their
commutator with either chart chosen independently for each transposition.
Every such mixed evaluation is the identity:

```text
[rho_epsilon(a),rho_eta(b)]=I,             epsilon,eta in {0,1}. (RGI2)
```

Indeed at most one of the disjoint transpositions can move `i`.  If neither
moves `i`, both lie in `H`, where the representations agree.  If, say, `a`
moves `i`, then `b in H`; moreover `U` commutes with `rho_0(b)`.  Since
`rho_0(a)` commutes with `rho_0(b)`, so does
`U rho_0(a)U^*=rho_1(a)`.  This proves `(RGI2)` in all cases.

The Bleak--Quick R4 and R5 relators are commutators of disjoint prefix
transpositions.  Therefore **every** label-valid R4/R5 cell inside the fixed
six-letter union packet remains exact under an arbitrary common-S5
multiplicity rotation, even when its two arms are assigned to different
contextual charts.  Taking the explicit rotation from
`shared-s5-selector-face-has-multiplicity-rotation-gauge` makes the missing
arm mismatch positive while all these mixed R4/R5 defects vanish.

The blindness is quantitative before exactification.  Suppose
`Phi_0,Phi_1:G->U(d)` have all-pairs multiplicative defect at most `epsilon`
and

```text
max_(h in H)||Phi_0(h)-Phi_1(h)||_2 <= eta.                      (RGI3)
```

For disjoint transpositions `a,b` and arbitrary chart choices,

```text
||[Phi_epsilon(a),Phi_eta(b)]-I||_2 <= 2 epsilon+4 eta.          (RGI4)
```

At least one of `a,b` lies in `H`.  Move that factor, and also the other one
when it lies in `H`, into a single chart using `(RGI3)`.  Inside one chart,
`ab=ba` and two uses of all-pairs multiplicativity give commutator defect at
most `2 epsilon`; replacing a unitary in a commutator costs at most twice
its HS displacement.  This proves `(RGI4)`.

Consequently no dimension-free inequality can control the missing-arm
distance using the common-S5 defect plus any family of fixed-packet R4/R5
cell energies.  A successful matrix-dependent collapse must retain an
**overlapping-support** cross relation.  At the fixed packet level the mixed
R2 cell is the minimal such relation; a genuinely mixed R3 split would be an
alternative only if its child occurrence were independently authenticated.
