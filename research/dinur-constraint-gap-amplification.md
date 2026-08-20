---
rg: 2
id: dinur-constraint-gap-amplification
kind: claim
title: Dinur's linear-size constraint-graph transformation amplifies UNSAT by two up to a constant
distinct_from:
  robust-locally-satisfiable-relator-code: that asks for noncommutative normalized-HS soundness together with sparse preservation of a group ball; this is the classical finite-alphabet CSP transformation and has neither property.
  atlas-a4-classical-collision-gap-one-fifth: that is an exact soundness computation for one fixed A4 packet; this is a uniform transformation of arbitrary finite-alphabet constraint graphs.
---

There is a finite alphabet `Sigma_0` with the following property.  For every
finite alphabet `Sigma` there are constants `C > 0` and `0 < alpha < 1` and a
polynomial-time transformation taking every binary constraint graph `G` over
`Sigma` to a binary constraint graph `G'` over `Sigma_0` such that

```text
size(G') <= C * size(G),
UNSAT(G) = 0  ==>  UNSAT(G') = 0,
UNSAT(G') >= min(2 * UNSAT(G), alpha).
```

Here `UNSAT` is the minimum fraction of violated edges over all vertex
assignments and `size(G) = |V(G)| + |E(G)|`, with parallel edges counted.
The constants may depend on the source alphabet but not on the size of `G`.

This is Theorem 1.5 of Irit Dinur, *The PCP Theorem by Gap Amplification*,
J. ACM 54(3), Article 12 (2007), DOI `10.1145/1236457.1236459`.

## Scope boundary for this repository

The theorem quantifies over assignments into a **finite classical alphabet**.
It does not amplify soundness over matrix-valued, commuting-operator, tracial,
or normalized-Hilbert--Schmidt assignments.  It also does not say that a sparse
random subfamily of the amplified constraints preserves a prescribed group
ball.  Those are precisely the extra clauses in
[[robust-locally-satisfiable-relator-code]], so this established theorem is a
classical baseline for that hole, not a solution of it.
