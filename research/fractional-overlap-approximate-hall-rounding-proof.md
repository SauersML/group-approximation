---
rg: 2
id: fractional-overlap-approximate-hall-rounding-proof
kind: route
title: Convert the overlap transportation plan into an integral max flow
target: fractional-overlap-approximate-hall-rounding
requires: []
---

Orient the bipartite graph from source blocks `Q_j` to target blocks `P_i`.
For `A subset J`, let `N(A) subset I` be its neighbors through allowed edges.
The exact column marginals of the overlap plan give

```text
rank(Q_A)/d
 = sum_(j in A,i) m_(i,j).
```

Every term with `j in A` and `i notin N(A)` is a forbidden edge, so their
total is at most `beta`.  The remaining terms are bounded by the target
marginals over `N(A)`.  Hence

```text
rank(Q_A) <= rank(P_(N(A))) + beta d.                 (1)
```

Since the ranks are integers,

```text
rank(Q_A) <= rank(P_(N(A))) + k,
k=ceil(beta d),                                       (2)
```

for every `A`.

Build the standard integral flow network: a source connects to vertex `j`
with capacity `rank(Q_j)`; allowed edges `j->i` have infinite (or capacity
`d`) edges; target vertex `i` connects to the sink with capacity `rank(P_i)`.
Add one dummy target of capacity `k`, connected from every `j`.
Condition `(2)` is exactly Hall's cut condition for saturating all `d` source
dimensions in this enlarged network.  Thus max-flow/min-cut gives a flow of
value `d`.  All capacities are integral, so an integral max flow exists.

At most `k` units use the dummy target.  Delete those dummy-flow units and
write the remaining allowed-edge flows as `x_(i,j)`.  Their total is at least
`d-k`, and the original source and target capacity constraints give the two
marginal inequalities in the claim.  Since the two real spaces both have
total dimension `d`, the unmatched target dimension is the same total
`d-sum x_(i,j)`, also at most `k`.  This proves the theorem.