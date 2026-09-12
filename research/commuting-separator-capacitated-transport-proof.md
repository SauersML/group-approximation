---
rg: 2
id: commuting-separator-capacitated-transport-proof
kind: route
title: Resolve the common involution on every joint separator block
target: commuting-separator-chord-is-capacitated-transport
requires:
  - chord-regauging-is-relative-commutant-feasibility
---

Because the separator algebras commute, the nonzero products `g_(s,t)` are
pairwise orthogonal joint spectral projections and sum to the identity.  A
projection commuting with both separator algebras is block diagonal over
this decomposition.

For such a projection `P`, set
`n_(s,t)=rank(g_(s,t)P)`.  The block rank bound and the row and column sums are
exactly `(CST3)`.  Applying this to `P=(1+Z)/2` proves necessity.

Conversely choose arbitrary projections of the prescribed ranks in the full
matrix joint blocks and take their direct sum as in `(CST4)`.  Its row and
column conditional ranks are `(CST2)`.  The involution `Z=2P-I` therefore
satisfies `(CRF2)--(CRF3)`, and the general chord theorem gives the desired
endpoint unitaries.

The constraint matrix of the bipartite flow problem is totally unimodular,
so real feasibility with integral demands and capacities implies integral
feasibility.  Equivalently one may attach a source with capacities `r_s`, a
sink with capacities `c_t`, and use integral max flow.
