---
rg: 2
id: mikhailova-left-right-lef-iff-quotient-rf
kind: claim
title: A finitely presented Mikhailova left-right action is LEF exactly when the quotient is residually finite
distinct_from:
  mikhailova-left-right-action-current-frontier: that proves the equivalence for residually finite set actions; this rules out the strictly broader class of LEF action models.
  mikhailova-positive-rope-is-not-lef: that proves the centralizing HNN group is not LEF; this proves non-LEFness already for the underlying left-right set action.
  mihailova-left-right-local-models-do-not-see-q: that gives finite local models with arbitrary invariant metrics; LEF action models require exact finite group actions and are excluded here.
---

Let `H=<x_1,...,x_m | r_1,...,r_k>` be finitely presented, let
`q:F_m->H` be the presentation map, and put

```text
G=F_m x F_m,
M_H={(u,v) in G:q(u)=q(v)}.
```

Then the following are equivalent.

1. The left-right action

```text
G acts on H,        (u,v).h=q(u)h q(v)^(-1)            (MLA1)
```

is a LEF action in the sense of Alekseev--Bradford.
2. `H` is residually finite.
3. `M_H` is separable in `G`.

The new implication is `1 => 3`.  Alekseev--Bradford identify LEFness of a
transitive action `G` on `G/M_H` with `M_H` being almost of finite
index.  Applying that definition to the identity homomorphism of the
finitely presented group `G` gives finite-index subgroups `J_n<G`
converging to `M_H` in the Chabauty topology.

Finite presentation of `H` makes `M_H` finitely generated:

```text
M_H=< (x_i,x_i), (r_j,1) : 1<=i<=m, 1<=j<=k >.         (MLA2)
```

Consequently `J_n` eventually contains all of `M_H`.  Chabauty
convergence also eventually excludes each prescribed
`g in G minus M_H`.  Hence finite-index overgroups of `M_H` separate
every element outside it, so `M_H` is separable.

For the repository's finitely presented nonsofic quotient `H`, residual
finiteness fails and therefore `(MLA1)` is not LEF.  Combined with the
one-color criterion
`mikhailova-left-right-soficity-is-one-color-code`, this gives an exact
qualitative constraint: every hypothetical GKP witness must use
asymptotically commuting permutation models that cannot be replaced, even
locally, by exact finite group-action charts.

DERIVATION
[[mikhailova-left-right-lef-rf-proof]]
