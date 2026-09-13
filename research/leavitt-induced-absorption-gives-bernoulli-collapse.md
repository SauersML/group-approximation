---
rg: 2
id: leavitt-induced-absorption-gives-bernoulli-collapse
kind: route
title: DEAD. An induced projective absorbed by a free F_2[U]-module would give a Bernoulli collapse, but no group has one
target: some-group-has-isomorphic-bernoulli-shifts-of-different-entropy
requires: []
---

**DEAD.** This route is invalidated by `finite-subgroup-induced-absorption-conserves-entropy`, which is
established through the lifted p-adic trace.

**The idea.** Take `G = U = L_(F_2)(1,2)^x` and `p = 2`. Suppose `F_2[U]^n ≅ F_2[U]^n ⊕ ⊕_i Ind(Q_i)`, with
`Q_i` modules over finite subgroups, not all zero. Theorem E of
`induced-projective-absorption-breaks-bernoulli-classification` would then give isomorphic Bernoulli shifts
over `U` with base entropies `n log 2` and `n log 2 + rho log 2`, where `rho = sum dim(Q_i)/|F_i|`.

**Where it dies.** The lifted trace `t_2` of `lifted-trace-detects-finite-subgroup-projectives` is additive on
`K_0(F_2[U])` and equals `rho` on the absorbed summand. The absorption forces `t_2 = 0`, so `rho = 0` and every
`Q_i = 0`. The number that the co-induced Ornstein construction adds to the entropy is exactly the lifted
trace, and the lifted trace is conserved by every module isomorphism.
