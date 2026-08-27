---
rg: 2
id: bounded-dimension-microstates-force-lef
kind: claim
title: A group whose windows carry bounded-dimension microstates is LEF, hence sofic
distinct_from:
  exact-finite-dimensional-group-table-classicalizes: that is the table-level statement -- one finite partial multiplication table with an *exact* separated unitary solution has an exact finite permutation model; this is the group-level consequence, quantified over all finite windows of a group and over *approximate* solutions, and its conclusion is LEF (a property of the group) rather than the classicalization of one table.
  permutation-norm-models-certify-exactly-lef: that identifies which groups the Folner permutation construction can certify and why operator-norm permutation models never leave the LEF class; this identifies which groups a *dimension-capped unitary* microstate family can certify, and the mechanism is compactness plus Malcev, not the zero-or-one rigidity of permutation matrices.
  lef-implies-operator-mf: that is the forward permanence direction from LEF into operator MF; this is a criterion *for* LEF from approximation data, and says nothing about MF.
artifacts:
  - research/artifacts/hyperlinear-firewall-dossier-2026-08-24.md
---

Let `G` be a countable group.  Suppose there are a constant `c>0` and a
dimension cap `D<infinity` such that for every finite `F<=G` and every
`eps>0` there is a map

```text
rho : F -> U(d),      d <= D,                                   (BDM1)
```

with

```text
||rho(x) rho(y) - rho(xy)||_2 < eps   whenever x,y,xy in F,      (BDM2)
||rho(x) - rho(y)||_2 >= c            whenever x != y in F,      (BDM3)
```

the norm being the normalized Hilbert--Schmidt norm on `M_d`.  Then every
finite window of `G` embeds in a finite group compatibly with its partial
multiplication table, i.e. **`G` is LEF**, and therefore `G` is sofic.

The separation constant is not an extra hypothesis on the regular-character
face: microstates normalized by `tau(rho(x))->0` for `x!=1` satisfy
`||rho(x)-rho(y)||_2^2 = 2 - 2 Re tau(rho(x)^* rho(y)) -> 2`, so `(BDM3)`
holds with `c=1` for all small `eps`.  What is essential is that `c` does
**not** shrink with `eps`.

## Consequence for the separation root

Contrapositively, a hyperlinear nonsofic group `G` -- a witness for
`hyperlinear-nonsofic-group` -- must contain a finite window `F` whose
minimum microstate dimension diverges,

```text
d_F(eps) -> infinity   as eps -> 0.                              (BDM4)
```

So the obstruction sought on the flexible side of Question 3.4 is
intrinsically high-dimensional.  No fixed matrix algebra, no compact-group
representation, and no bounded-rank gadget can carry it: any construction
whose microstates live in `U(d)` for a single `d`, or in a fixed compact
group, is certifying LEF and therefore soficity.  This is a constraint on
*every* flexible-side route, not a refutation of any particular one.
