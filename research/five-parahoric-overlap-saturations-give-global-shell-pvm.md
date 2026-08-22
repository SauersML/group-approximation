---
rg: 2
id: five-parahoric-overlap-saturations-give-global-shell-pvm
kind: claim
title: Five saturated parahoric chart overlaps produce one global forty-two-vertex shell PVM
artifacts:
  - research/artifacts/sl3-five-overlap-shell-authentication-2026-08-22.md
distinct_from:
  forty-two-branch-gram-polar-rounding: that orthogonalizes one family of forty-two candidate projections when its internal cross-Gram sum is small; this identifies six native Weyl parameterizations of the same shell and gives the minimal cross-chart trace data forcing them to be literally the same family.
  six-parahoric-finite-fiber-folds-remain-amenable: that permits the six charts to recycle labels through unrelated finite-fiber gauges; this gives the exact five saturation scalars which prohibit that recycling.
  native-sl3-edge-parahoric-has-index-forty-two: that computes each chart and its size; this uses the common Hecke-sphere interpretation to identify corresponding labels across all six charts.
---

Let `C=SL_3(Z)`, `h=diag(2,1,1/2)`, and, for the six Weyl elements `w`, put

```text
h_w=w h w^(-1),       D_w=C cap h_w C h_w^(-1).
```

Every chart

```text
I_w=C/D_w
```

has `42` elements.  More importantly, all six charts canonically
parameterize the SAME Hecke sphere

```text
Omega=C h C/C
```

through

```text
phi_w(cD_w)=c h_w C.                                  (FOS1)
```

Hence there are canonical bijections

```text
beta_w=phi_(w_0)^(-1) phi_w:I_w -> I_(w_0)             (FOS2)
```

to any chosen root chart `w_0`.

Suppose each chart carries a projection family

```text
(P_(w,i))_(i in I_w)
```

which is a partial PVM.  For each of the other five charts define the single
aggregate saturation deficit

```text
Delta_w=(1/2) sum_(i in I_w)
        ||P_(w,i)-P_(w_0,beta_w(i))||_2^2.             (FOS3)
```

Equivalently, `Delta_w` is determined by the individual projection traces
and the `42` cross traces

```text
tr(P_(w,i)P_(w_0,beta_w(i))).
```

Then the root family

```text
E_j=P_(w_0,j),        j in I_(w_0),                    (FOS4)
```

is one global shell PVM and

```text
sum_(w!=w_0) sum_(i in I_w)
 ||P_(w,i)-E_(beta_w(i))||_2^2
 =2 sum_(w!=w_0) Delta_w.                              (FOS5)
```

In particular the five scalar equalities `Delta_w=0` force literal global
label agreement across all `6*42` chart atoms.  If the deficits tend to
zero, they give dimension-free approximate authentication with no separate
rounding theorem.

Five chart links are minimal at this level.  Any family of pairwise chart
comparisons whose chart graph has fewer than five edges is disconnected.
Conjugate every PVM in one connected component by an independent unitary
which does not normalize the root PVM.  All tested within-component
saturations and all individual chart Gram matrices remain unchanged, but no
single prescribed labeling identifies the two components.  Thus bounded
local overlap data can authenticate the shell exactly when it connects the
six charts; a spanning tree is necessary and sufficient, and the star above
has the sharp quantitative identity `(FOS5)`.

This theorem isolates rather than proves the arithmetic estimate.  The
remaining group-word problem is to force the five `Delta_w` to vanish (or
be bounded by mixed-root defect and first exits).  Once that is done, the
global 42-vertex shell PVM is already present and the established building
spectral gap applies.  Finite-fiber recycling is therefore exactly failure
of one of these five cross-chart trace saturations.

The first proposed source of these saturations is false.
`two-equivariant-shell-pvms-have-independent-coordinate-escape` places two
complete shell PVMs on the two coordinates of `Omega times Omega`.  The full
diagonal `C`-action covaries both exactly and every lattice root relation has
zero defect, but their corresponding-atom deficit is `41/42`.  Thus the
finite shell Laplacian reaches the full orbital commutant, not specifically
the diagonal matching.  At least one denominator-incidence row selecting
the diagonal orbital sector is necessary.
