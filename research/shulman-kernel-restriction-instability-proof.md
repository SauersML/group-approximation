---
rg: 2
id: shulman-kernel-restriction-instability-proof
kind: route
title: Lift the two free vertices of an injective norm-corona model
target: shulman-double-forces-unstable-kernel-restriction
requires:
  - symmetric-double-weak-mf
---

Apply `symmetric-double-weak-mf` to `P=F *_K F`. In an injective matrix norm
corona model, choose unitary lifts for a finite free basis of each vertex.
They extend to exact representations `u_n,v_n` because `F` is free. Equality
of the two copies of each `k in K` gives pointwise convergence on `K`, after
the standard diagonal exhaustion. The cross-vertex word determined by
`f_0 notin K` is reduced and nontrivial. Its nonzero corona norm supplies a
uniform lower bound on `||u_n(f_0)v_n(f_0)^*-I||`, which is `(PRI3)`.
