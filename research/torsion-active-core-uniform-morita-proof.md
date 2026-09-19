---
rg: 2
id: torsion-active-core-uniform-morita-proof
kind: route
title: Translate the active-core rank bound into uniform Murray-von Neumann comparison
target: torsion-active-core-is-a-uniform-morita-generator
requires:
  - torsion-normal-generator-has-full-support-corona-core
  - matrix-corona-projection-ideal-and-corner-calculus
---

Choose coordinate lifts `p_n` of `p`.  Active-core reblocking gives

```text
k_n<=L rank(p_n)                                      (UMG3)
```

eventually.  The rank-germ comparison theorem identifies eventual coordinate
rank comparison with stable Murray--von Neumann subequivalence.  Since the
unit of `Q_k` has coordinate rank `k_n` and `p^(directSum L)` has coordinate
rank `L rank(p_n)`, `(UMG3)` gives `(UMG1)`.

Every `q in Q_k` is subequivalent to `1`, so `(UMG2)` follows by transitivity.
The same calculation in `M_t(Q_k)` compares rank at most `t k_n` with
`tL rank(p_n)`.  Fullness and Morita equivalence are the standard
consequences of `1` being subequivalent to a finite direct sum of `p`.

