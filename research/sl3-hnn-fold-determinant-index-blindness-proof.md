---
rg: 2
id: sl3-hnn-fold-determinant-index-blindness-proof
kind: route
title: Realize a trace-zero determinant-one commutator by a cyclic shift and diagonal ratios
target: sl3-hnn-fold-determinant-and-index-are-trace-blind
requires: []
artifacts:
  - research/artifacts/sl3-joint-determinant-index-audit-2026-08-21.md
---

Determinant multiplicativity proves `(JDT1)`.  Let `zeta` be a primitive
`d`th root and choose `alpha^d=(-1)^(d-1)`.  The diagonal unitary with
entries `alpha zeta^j` has trace zero and determinant one.  Every diagonal
unitary of determinant one is a commutator with the cyclic shift: solve the
cyclic ratio equations `q_j/q_(j-1)=alpha zeta^j` and use the diagonal
unitary `diag(q_j)`.  This proves `(JDT2)`.

For the index assertion, `rank(X)=rank(X^*)` for square matrices, while
unitary conjugacy gives `rank(P)=rank(HPH^*)`.  Rank-nullity yields the two
zero-index formulas.  Spectator amplification preserves the normalized
trace-zero example and absorbs any fixed divisibility condition.
