---
rg: 2
id: thompson-v-has-no-heisenberg-subgroup
kind: claim
title: Thompson's V_n contains no integer Heisenberg group and no Baumslag--Solitar group BS(1,k) with |k| >= 2
distinct_from:
  thompson-v-cyclic-subgroups-are-undistorted: that is the imported metric theorem; this is the subgroup obstruction derived from it.
  leavitt-unit-group-has-no-integer-heisenberg-subgroup: that asks the same question for the binary Leavitt unit group, where linear units that are not Thompson elements have no known undistortion theorem; this settles it for V_n only.
---

**ESTABLISHED** by `thompson-v-has-no-heisenberg-subgroup-proof`.

Let `n >= 2`.

1. There are no `a, b` in `V_n` such that `c = [a,b]` has infinite order and
   commutes with `a` and `b`. Equivalently, `V_n` has no subgroup isomorphic to
   `H_3(Z)`.
2. `V_n` has no subgroup isomorphic to `BS(1,k) = <x,t | t x t^-1 = x^k>` with
   `|k| >= 2`.

**The two forms of item 1 agree.** If `c = [a,b]` has infinite order and is
central in `<a,b>`, then `<a,b>` is a quotient of `H_3(Z)` in which the center
survives. A nontrivial normal subgroup of a torsion-free nilpotent group meets
its center nontrivially, so the kernel is trivial and `<a,b> ~= H_3(Z)`.

**Why it is recorded.** Every group containing `SL_d(Z)` with `d >= 3` contains
`H_3(Z)`, as the upper unitriangular integer matrices. This includes the actor of
every Theorem E pair and so every Kun--Thom coset wreath. Item 1 therefore shows
that no Thompson subgroup of the binary Leavitt unit group can supply the
Heisenberg subgroup that `kun-thom-wreath-embeds-in-leavitt-unit-group` needs.
The linear units of that group are outside this theorem; see
`leavitt-unit-group-has-no-integer-heisenberg-subgroup`.

No novelty is claimed. Belk--Bleak--Matucci--Zaremsky list this obstruction
(arXiv:2306.16356, Theorem 4.6(3)).
