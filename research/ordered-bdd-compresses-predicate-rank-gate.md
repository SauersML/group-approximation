---
rg: 2
id: ordered-bdd-compresses-predicate-rank-gate
kind: claim
title: A reduced ordered decision diagram gives a shared-path affine rank gate
artifacts:
  - experiments/fanizza_fixed_predicate_rank_compiler.py
distinct_from:
  boolean-predicate-is-one-rank-jump: that uses one internally disjoint path per satisfying assignment; this merges equal residual Boolean functions and can reduce the packet by an exponential factor.
---

Let `f:{0,1}^k->{0,1}` and fix a variable order.  Take its reduced ordered
binary decision diagram, omit the false terminal and every edge entering it,
and label a zero edge at variable `x_i` by `1+x_i` and a one edge by `x_i`.
Let `v` be the number of reachable non-false vertices, including the true
terminal.  Its affine weighted adjacency matrix `N_f` is strictly upper
triangular after ordering vertices by decision level.  Put

```text
U_f=I+N_f,
M_f=[[U_f,e_t],[e_s^T,0]].                              (BDD1)
```

Then, on every Boolean assignment,

```text
rank_F2 M_f(x)=v+f(x).                                  (BDD2)
```

Indeed, a deterministic decision diagram has exactly one live source-to-true
path when `f(x)=1` and none when `f(x)=0`.  Hence the `(s,t)` entry of
`U_f(x)^-1` is `f(x)`.  The Schur complement of the always-invertible block
`U_f(x)` proves `(BDD2)`.

Thus the Schur--Clifford packet size is controlled by decision-diagram size,
not by the number of satisfying assignments.  Exhausting the finitely many
variable orders is an exact finite optimization for the fixed bounded-arity
predicates used below.
