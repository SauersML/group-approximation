---
rg: 2
id: finite-quotients-bound-carmichael-conjugacy-chromatic-number
kind: claim
title: A finite quotient separating the mark bounds every Carmichael conjugacy graph
distinct_from:
  bounded-area-high-chromatic-conjugacy-collapse: that uses matrix compactness and uniformly bounded presentation area to obstruct hyperlinearity; this is an exact group-theoretic coloring obstruction requiring no presentation or area bound.
  literal-one-cell-carmichael-cliques-are-uniformly-finite: that uses free-group axis geometry to rule out one-cell word templates; this colors any exact Carmichael graph through one finite quotient, regardless of its word representatives.
  finite-normalizer-star-no-go: that bounds a packet produced inside one finite normalizer; this applies to arbitrary conjugates once the marked element survives in any finite quotient.
---

Let `G` be a group, `w in G`, and `Lambda` a graph with vertex labels

```text
u_v=h_v w h_v^(-1)
```

satisfying

```text
u_v^3=1,
(u_vu_z)^2=1                    whenever vz is an edge. (FQC1)
```

If `phi:G->Q` is a finite quotient with `phi(w)!=1`, then

```text
chi(Lambda)<=|phi(w)^Q|<=|Q|.                            (FQC2)
```

Consequently an element admitting exact Carmichael conjugacy graphs of
unbounded chromatic number belongs to the finite residual of `G`.  In
particular no nontrivial element of a residually finite group can support
such a family.

This screens alternative finitely presented permutation actions before any
area calculation.  Thompson `V` is not eliminated because its simplicity
precludes a nontrivial finite quotient.  For a hyperlinear (hence for a
sofic or amenable) finitely presented group, the exact graphs may still
exist, but `bounded-area-high-chromatic-conjugacy-collapse` forces their
maximum defining-relator area to diverge along every sequence whose
chromatic number tends to infinity.

