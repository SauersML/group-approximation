---
rg: 2
id: commuting-separator-chord-is-capacitated-transport
kind: claim
title: A commuting-separator chord is an integral capacitated transport problem
distinct_from:
  chord-regauging-is-relative-commutant-feasibility: that gives the general common-relative-commutant criterion; this solves it exactly when the two separator algebras commute.
  global-v4-exit-capacity-is-cross-gram-curvature: that derives a normalized-HS leakage-or-overlap inequality for transported V4 exits; this is an exact finite-rank max-flow criterion for one signed-Hecke chord.
---

Use the notation of
`chord-regauging-is-relative-commutant-feasibility` and assume additionally
that `A_0` and `A_1` commute.  Let `(e_s)_s` and `(f_t)_t` be their minimal
projections and put

```text
g_(s,t)=e_s f_t,                  m_(s,t)=rank(g_(s,t)). (CST1)
```

Let

```text
r_s=rank(e_s(1+X_0)/2),
c_t=rank(f_t(1+X_1)/2).                                  (CST2)
```

The chord can be closed by separator-preserving endpoint regauges if and only
if there are integers `n_(s,t)` satisfying

```text
0<=n_(s,t)<=m_(s,t),
sum_t n_(s,t)=r_s,
sum_s n_(s,t)=c_t.                                      (CST3)
```

Thus feasibility is a bipartite integral flow problem with joint separator
block dimensions as edge capacities.  It has a polynomial-time max-flow
decision and an integral solution whenever the corresponding cut
inequalities hold.

Given `(CST3)`, choose a rank-`n_(s,t)` projection `P_(s,t)` inside every
nonzero full matrix block `g_(s,t)M_Dg_(s,t)` and put

```text
P=sum_(s,t)P_(s,t),                Z=2P-I.               (CST4)
```

Then `Z in A_0' intersect A_1'` and has precisely the two conditional rank
tables `(CST2)`, so the general chord criterion supplies the two endpoint
regauges.  Conversely every common `Z` gives `(CST3)` by taking
`n_(s,t)=rank(g_(s,t)(1+Z)/2)`.

If the joint blocks and their matrix units are algebraic in a signed group
corner, `(CST4)` and the regauges can be chosen algebraically with finite
support.  In a properly infinite witness, infinite joint blocks remove the
finite upper-capacity obstruction.  In finite matrices the cut constraints
remain exact and are therefore a legitimate matrix-only place for the
holonomy to pay.
