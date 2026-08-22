---
rg: 2
id: finite-tree-first-exits-extract-an-equal-rank-global-pvm
kind: claim
title: A finite tree of two-sided first exits extracts one equal-rank global PVM core
distinct_from:
  forty-two-branch-gram-polar-rounding: that orthogonalizes one family of overlapping candidate projections from a cross-Gram bound; this starts with separately orthogonal chart PVMs and cuts them coherently along actual transition edges to obtain equal ranks and one common transported core.
  polar-compression-turns-band-mismatch-into-first-exit: that treats one edge and one closed product after equal trace is supplied; this first balances ranks across an arbitrary finite tree, intersects all pulled-back polar sources, and propagates the resulting common source simultaneously to every vertex.
  atlas-a4-context-exact-regular-normalization: that trims representation types to a prescribed finite-group regular vector and repairs exact graph-of-groups intertwiners; this uses only projection ranks and HS first-exit leakage and does not exactify any actor representation.
---

Let `G=(V,E)` be a finite connected graph with `m=|V|`, and choose a rooted
spanning tree `T`.  For every vertex `v`, let `P_v` be a projection in
`M_d(C)`.  For every oriented tree edge `e:v->w`, let `U_e` be unitary and
put

```text
ell_e^+=||(1-P_w)U_eP_v||_2^2,
ell_e^-=||(1-P_v)U_e^*P_w||_2^2,
L=sum_(e in T)(ell_e^++ell_e^-).                       (TFE1)
```

Then there are subprojections

```text
E_v<=P_v                                                   (TFE2)
```

of one common normalized rank, and polar partial isometries `V_e`, such
that

```text
E_w=V_eE_vV_e^*,                                      (TFE3)
||(1-E_w)U_eE_v||_2^2<=2ell_e^+ +2mL,                 (TFE4)
tau(P_v-E_v)<=m(m+2)L.                                (TFE5)
```

The harmless displayed constants are deliberately coarse.  They depend
only on the fixed graph, not on `d`, the projection ranks, conductor depth,
or any spectral period.

Moreover, for any additional oriented edge `f:v->w` with unitary `U_f`,

```text
||U_fE_vU_f^*-E_w||_2^2
 <=3||U_fP_vU_f^*-P_w||_2^2+6m(m+2)L.                 (TFE6)
```

Thus every non-tree lattice covariance remains controlled after the common
core extraction.

## Rank balancing

For a tree edge, direct expansion gives

```text
tau(P_v)-tau(P_w)=ell_e^+-ell_e^-.                    (TFE7)
```

Let `r=min_v tau(P_v)` and trim each `P_v` to a subprojection `P'_v` of
trace `r`.  Such a subprojection exists in matrices because all traces are
integer multiples of `1/d`.  Along tree paths, `(TFE7)` implies

```text
sum_v tau(P_v-P'_v)<=mL.                               (TFE8)
```

The forward leakage after trimming satisfies

```text
ell'_e=||(1-P'_w)U_eP'_v||_2^2
 <=ell_e^+ +tau(P_w-P'_w),                             (TFE9)
```

so

```text
sum_(e in T)ell'_e<=(m+1)L.                           (TFE10)
```

## One pulled-back source

Polar-decompose `P'_wU_eP'_v`.  By
`polar-compression-turns-band-mismatch-into-first-exit`, its polar partial
isometry `V_e` has source missing from `P'_v` by trace at most `ell'_e`, and

```text
||U_eP'_v-V_e||_2^2<=2ell'_e.                          (TFE11)
```

For each vertex `v`, multiply the `V_e` along the unique root-to-`v` path
and let `R_v` be the initial projection of that product in the root space.
Successive source losses and the projection union bound give

```text
tau(P'_root-R_v)<=sum_(e in path(root,v))ell'_e.        (TFE12)
```

Put

```text
R=meet_(v in V)R_v.                                    (TFE13)
```

The finite von Neumann projection inequality
`tau(P-meet_j Q_j)<=sum_j tau(P-Q_j)` yields

```text
tau(P'_root-R)<=m sum_e ell'_e<=m(m+1)L.               (TFE14)
```

Transport `R` along the tree path to define `E_v`.  Every path product is
isometric on `R`, proving equal rank and `(TFE3)`.  Equations
`(TFE8)`, `(TFE10)`, and `(TFE14)` give `(TFE5)`.  Restricting `(TFE11)` to
`E_v` proves `(TFE4)`.  Finally,

```text
||U_fE_vU_f^*-E_w||_2
 <=||U_fP_vU_f^*-P_w||_2
   +||P_v-E_v||_2+||P_w-E_w||_2,                       (TFE15)
```

and a three-term square bound gives `(TFE6)`.

## The 252-vertex arithmetic tree

For the six `42`-atom SL3 charts, use vertices `(w,i)`.  Choose:

1. `41` lattice-label edges forming a spanning tree inside one root chart;
2. for each of the other five charts and every label, its raw denominator
   section edge to the root chart.

This is a spanning tree with

```text
41+5*42=251=6*42-1                                    (TFE16)
```

edges.  The first edge class is paid by the decoded full-PVM lattice
covariance.  The second is paid by the conductor first-exit ledger.  Hence
`(TFE2)--(TFE6)` construct equal-rank atoms in all charts, preserve their
PVM orthogonality because only subprojections are taken, and place the
actual section transitions in the same first-exit ledger consumed by
`equal-rank-denominator-edges-authenticate-decoded-atoms`.

If the six initial chart PVMs carry a fixed common positive mass and their
displayed energies tend to zero, `(TFE5)` retains that mass asymptotically.
Thus rank balancing and common-source synchronization are not additional
frontier holes.  The remaining arithmetic input is earlier: construct the
six separate decoded chart PVMs from the conductor/root packets with the
two edge-energy classes in `(TFE16)` tending to zero.

