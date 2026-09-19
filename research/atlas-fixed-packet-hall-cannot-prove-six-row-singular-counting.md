---
rg: 2
id: atlas-fixed-packet-hall-cannot-prove-six-row-singular-counting
kind: claim
title: A fixed packet-type Hall selection cannot prove the six-row singular-counting inequality
invalidates: [atlas-six-row-singular-counting-via-fixed-packet-hall-selection]
distinct_from:
  atlas-six-row-singular-counting-dominates-nontrivial-s3: that permits spectral projections moving with the full matrix coordinate and threshold; this rules out only replacing those moving incidences by one fixed finite packet-type graph with linear capacities.
  universal-atlas-ideal-cannot-force-hall-deficit: that rules out universal star-ideal identities for forbidden Fourier blocks; this also rules out arbitrary fixed finite packet restriction diagrams and capacitated Hall inequalities, even when the named vertices include spectral atoms.
---

**ESTABLISHED AS A SCOPED NO-GO.**  Fix a finite diagram of finite Atlas
packet groups and a fixed finite bipartite graph.  Allow its vertex capacities
to use:

- irreducible multiplicities and restriction multiplicities in that diagram;
- ranks of finitely many named spectral atoms; and
- rational linear combinations of those ranks, followed by any finite family
  of capacitated Hall inequalities.

This data cannot prove `(SCI3)` in
`atlas-six-row-singular-counting-dominates-nontrivial-s3` if the only input
relating the named atoms is the fixed packet restriction/incidence data.

Indeed all such normalized capacities form a rational polytope

```text
K={x>=0: Bx=0, dim(x)=1},                              (FPH1)
```

and every Hall condition is a rational linear inequality on `K`.  Matrix
multiplicity profiles are the rational points of `K`, while finite tracial
multiplicity profiles are all real points.  Rational points are dense in each
rational face, so a Hall inequality valid for every matrix profile is valid
for every finite tracial profile.  This is exactly the denominator-clearing
argument of `fixed-packet-hall-atlas-has-no-julia-cutoff-gap`; naming the six
spectral atoms does not alter it unless one also retains a nonlinear
matrix-coordinate relation between those atoms.

Now evaluate the profile in the exact Leavitt factor.  All six residuals are
zero, hence for every `t>0`

```text
N_(R_j)(kappa t)=N_(R_c)(kappa t)=0.                  (FPH2)
```

But `atlas-six-relator-factor-retains-half-nontrivial-s3-mass` gives
`||A||_2^2>=1/2`.  Layer cake then implies that the spectral distribution of
`|A|` is nonzero on a set of positive thresholds; in particular there is a
`t in (0,2]` with

```text
N_A(t)>0.                                             (FPH3)
```

Thus the corresponding fixed capacitated Hall conclusion fails on a finite
tracial point of the same packet polytope.  By density it cannot be a
consequence of the fixed rational packet data on all matrix points.

This does **not** refute `(SCI3)`.  It identifies the extra datum a proof must
use: the neighbor relation or capacity must depend nonlinearly on the actual
finite matrix `U` and on `t` (or use a family whose complexity grows with the
matrix dimension).  A fixed Fourier support graph, fixed packet atlas, or
fixed list of type-rank Hall cuts repeats the tracially functorial route and
cannot distinguish matrices from the Leavitt factor.
