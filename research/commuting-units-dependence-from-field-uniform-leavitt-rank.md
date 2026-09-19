---
rg: 2
id: commuting-units-dependence-from-field-uniform-leavitt-rank
kind: route
title: Commuting units are commuting elements, so the field-uniform rank statement at F_2 gives their dependence
target: leavitt-commuting-units-are-algebraically-dependent
requires: [leavitt-algebras-contain-no-two-variable-polynomial-ring]
---

Let `a, c` be commuting units of `L_(F_2)(1,2)`.
- By `leavitt-algebras-contain-no-two-variable-polynomial-ring` at `k = F_2`, there is a nonzero
  `P ∈ F_2[x, y]` with `P(a, c) = 0`.
- `P` is also a nonzero Laurent polynomial. That is exactly the relation the target asks for. ∎
