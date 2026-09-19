---
rg: 2
id: bs14-cubic-rounding-leaves-relative-core-basin
kind: claim
title: Cubic spectral rounding leaves exactly the relative BS-core basin problem
distinct_from:
  bs14-thresholded-newton-needs-coordinate-basin: that isolates the operator-norm coordinate tube needed by the mixed-norm Newton estimate; this proves that rounding the two cubic values does not manufacture that tube.
  bs14-relative-involution-extension-stability: that is the desired normalized-HS flexible theorem; this is an operator-norm reduction over an already exact BS core.
  exel-loring-relative-quasirep-invariant: that records a possible group-homological obstruction; this proves there is no obstruction carried by either cubic torsion relation separately and localizes any such class to the relative core incidence.
---

Let `R,S,X in U(d)` satisfy the exact BS and dihedral relations

```text
R S R^*=S^4,       X^2=1,       X R X=R^*.
```

Put

```text
A=X S^2,       B=X R S,       C=S^(-2) R S.
```

Then the identity

```text
B=A C,             C=A^*B                                      (CSR1)
```

is exact.  If

```text
eta=max(||A^3-1||_op,||B^3-1||_op)<2,
```

functional calculus supplies order-three unitaries `Ahat,Bhat` with

```text
Ahat^3=Bhat^3=1,
||A-Ahat||_op <= (1/2)||A^3-1||_op,
||B-Bhat||_op <= (1/2)||B^3-1||_op,                  (CSR2)
```

and consequently

```text
||C-Ahat^*Bhat||_op <= eta.                           (CSR3)
```

For `(CSR2)`, write a spectral value of `A` as `exp(it)` and let
`Delta in [-pi/3,pi/3]` be its angular distance from the nearest cube root
of unity.  Since

```text
2 sin(|Delta|/2) <= (1/2) 2 sin(3|Delta|/2),
```

on this interval (equivalently `sin(3u)>=2 sin(u)` for
`0<=u<=pi/6`), nearest-root functional calculus proves the estimate.  The
same argument applies to `B`, and `(CSR3)` follows by telescoping.

This is the entire dimension-free conclusion available from the three
spectral labels.  In general

```text
Bhat != Ahat C,
X_A:=Ahat S^(-2)
```

need not be an involution or invert `R`.  Alternatively, replacing `C` by
`Chat=Ahat^*Bhat` requires changing the exact BS core so that

```text
S'^(-2) R' S'=Chat,
R'S'R'^*=S'^4,
```

while simultaneously making `Ahat S'^(-2)` an involution that inverts
`R'`.  That is precisely a **relative operator-norm basin/lifting theorem**
for the inclusion of the BS core in the Iwahori presentation.

Thus the free pair of cubic relations has no standalone Voiculescu or
`K`-theoretic obstruction: `(CSR2)` explicitly corrects it in the same
matrix dimension.  Any obstruction must involve the relative incidence
with `C=S^(-2)RS` (and the common `X`), not the torsion spectral projections
of `A` and `B` separately.

Nor does finite spectral support give a compactness proof uniform in `d`.
It fixes only the three eigenvalue labels.  Their multiplicities and the
relative positions of the associated spectral subspaces range over
Grassmannians of unbounded dimension.  Compactness gives an error bound on
each fixed matrix stratum, but not one modulus over their union.  The
uniform infinitesimal gap at exact congruence atoms controls a pre-existing
operator-norm tube; it does not rule out a far approximate component.

The exact global survivor is therefore:

> uniformly over all exact periodic BS cores, every exact dihedral
> involution for which the two cubics are small in operator norm enters a
> fixed operator-norm tube of an exact Iwahori extension, allowing the
> prescribed small-rank/flexible changes.

No semiprojectivity theorem currently represented in Cairn establishes
this **relative** statement.  Invoking stability of `z^3=1`, or compactness
of fixed-dimensional conjugacy classes, stops at `(CSR3)`.

The immediate attempt to absorb `Chat=Ahat^*Bhat` into the core is audited
in `bs14-hs-stability-does-not-supply-relative-op-basin`.  It gives an
operator-norm approximate BS pair `(Chat,S)` with defect at most `2 eta`,
but the known BS theorem is normalized-HS stability.  Those topologies are
separated even by exact cores differing on one scalar packet, and
operator-norm stability of `BS(1,4)` remains open in the cited primary
literature.  Moreover separate core correction does not preserve the common
involution, so even a positive answer to that open BS question would still
need a joint or contractive relative step.
