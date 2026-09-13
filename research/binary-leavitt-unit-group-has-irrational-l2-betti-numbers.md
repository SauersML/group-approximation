---
rg: 2
id: binary-leavitt-unit-group-has-irrational-l2-betti-numbers
kind: claim
title: The binary Leavitt unit group has integral group-ring matrices whose kernels have irrational von Neumann dimension
distinct_from:
  algebraic-strong-atiyah-counterexample-exists: that asks for a torsion-free group with a non-integral kernel dimension over algebraic coefficients; this is a group with torsion of every order, where irrationality is inherited from a lamplighter subgroup.
  binary-leavitt-unit-group-is-l2-acyclic: that is vanishing of the L²-Betti numbers of the group itself; this is about kernels of arbitrary matrices, which need not be boundary maps of a resolution.
---

**ESTABLISHED (proved on paper, unreviewed).** Let `G = L_(F_2)(1,2)^x`. Some matrix `T` over
`Z[G]` has irrational `dim_vN ker T`. For example
`1/64 - (1/8) Σ_(k>=1) 2^(-(k²+4k+6))` arises from `G`.

**Atiyah problem for `G`.**
- `G` contains every finite group, so the orders of its finite subgroups have no common bound.
  The strong Atiyah conjecture then predicts only rational dimensions. This refutes that
  prediction.
- The same holds for every group containing `V`, including `(L ⊗ L)^x` and every `(B ⊗ L)^x`.
- Upper bound: `G` has decidable word problem, so every arising real is right-computable,
  and computable if `G` satisfies the determinant conjecture
  (`decidable-groups-have-right-computable-l2-betti-numbers`).

Route: `binary-leavitt-unit-irrational-l2-betti-proof`.
