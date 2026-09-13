---
rg: 2
id: no-heisenberg-from-algebraic-dependence
kind: route
title: The central commutator and one generator of an integer Heisenberg group would be algebraically independent commuting units
target: leavitt-unit-group-has-no-integer-heisenberg-subgroup
requires: [leavitt-commuting-units-are-algebraically-dependent, leavitt-heisenberg-centers-have-infinite-centralizer-rank]
---

1. Suppose `H = <a, b> <= Q = L_(F_2)(1,2)^x` with `c = [a,b]` central in `H` and of infinite order, so that
   `H ≅ H_3(Z)`.
2. By `leavitt-heisenberg-centers-have-infinite-centralizer-rank` (ii), the algebra map `F_2[H] -> R` is injective.
3. `<a, c> ≅ Z^2`. The monomials `a^i c^j` are distinct elements of `H`, hence linearly independent in `F_2[H]`, and
   by step 2 also in `R`. So no nonzero Laurent polynomial `P` has `P(a, c) = 0`.
4. `a` and `c` commute, so this contradicts `leavitt-commuting-units-are-algebraically-dependent`. ∎
