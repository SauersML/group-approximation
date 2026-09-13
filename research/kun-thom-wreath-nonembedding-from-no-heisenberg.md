---
rg: 2
id: kun-thom-wreath-nonembedding-from-no-heisenberg
kind: route
title: The Theorem E actor contains the integer Heisenberg group, so a Heisenberg-free unit group cannot contain it
target: kun-thom-wreath-does-not-embed-in-leavitt-unit-group
requires: [leavitt-unit-group-has-no-integer-heisenberg-subgroup]
---

1. For `d >= 3`, the upper unitriangular matrices of `SL_3(Z) <= SL_d(Z) <= G`
   form a copy of `H_3(Z)`. Its central commutator is
   `x_13(1) = [x_12(1), x_23(1)]`, of infinite order.
2. `W`, both doubles, and every other group containing `G` contain this copy.
3. A subgroup of `Q` inherits every subgroup. By
   `leavitt-unit-group-has-no-integer-heisenberg-subgroup`, `Q` has no subgroup
   isomorphic to `H_3(Z)`, so none of these groups embeds in `Q`. ∎
