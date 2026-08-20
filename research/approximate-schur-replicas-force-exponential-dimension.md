---
rg: 2
id: approximate-schur-replicas-force-exponential-dimension
kind: claim
title: An all-pairs approximate Schur-replica table retaining its sign has exponential dimension
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  commuting-schur-replicas-force-exponential-dimension: that treats exact representations of the replicated packet group; this permits normalized-HS error with constants independent of the replica count, under the stronger all-pairs multiplication hypothesis.
  projective-holonomy-rank-forces-exponential-multiplicity: that treats one exact projective cocycle form once its rank has already been selected; this robustly obtains the rank from positive forbidden mass across selected replicated context packets.
---

Fix one selected context `c_i` in each of `N` BCS replicas.  Let `K_N` be the
finite central product, over the common sign `J`, of those `N` Schur context
packet/flip groups.  Let `f:K_N->U(d)` satisfy `(GHS1)`.  In the group algebra
let

```text
Q_i^- = ((1-J)/2) (sum of the forbidden selector atoms of context c_i).
```

The two factors commute, and in every exact representation `Q_i^-` is the
projection onto the forbidden part of the **marked `J=-1` sector**.  Write
`Q_i^-(f)` for its Fourier evaluation under the linear extension of `f` and
assume

```text
Re tau_d(Q_i^-(f)) >= b=beta_B/C                for every i.      (ASE1)
```

There is a constant `K_B`, depending only on the fixed context packets, such
that if `epsilon<b/K_B` and

```text
b_epsilon=(1-4epsilon^2)(b-K_B epsilon)>0,
```

then

```text
d >= (1-4epsilon^2) 2^(ceil(b_epsilon N)).                       (ASE2)
```

Thus a controller which chooses

```text
N > b_epsilon^(-1) log_2(d/(1-4epsilon^2))                       (ASE3)
```

inside the current model and supplies one all-pairs map with fixed
`epsilon<1/2` obtains an immediate same-model contradiction.

The context selection is load-bearing.  The group obtained by gluing all
shared BCS contexts need not be finite, so Gowers--Hatami is applied only after
the robust BCS gap selects one context per replica.  The all-pairs condition
is load-bearing as well.  Converting only the standard presentation relators
of `K_N` to `(GHS1)` by normal forms introduces a constant growing with `N`;
`(ASE2)` does not remove that compiler problem.  The sign projector in
`(ASE1)` is also load-bearing: without it, forbidden mass could lie entirely
in a `J=+1` representation, where the Schur cocycle has no rank pressure.
