---
rg: 2
id: sl3z-normal-subgroup-class-stabilizers-are-polycyclic
kind: claim
title: For a normal subgroup of a subgroup of SL_3(Z), the quotient stabilizes each infinite-order conjugacy class with a polycyclic group
distinct_from:
  sl3z-infinite-order-centralizers-are-solvable: that claim bounds the centralizer of one element; this one bounds how the quotient G/N acts on the N-conjugacy classes of a normal subgroup, via the identification of each stabilizer with C_G(x)/C_N(x)
  sl3z-products-of-infinite-subgroups-are-polycyclic: that claim is about pairs of commuting subgroups; this one is about the outer action of G/N on a normal subgroup N
artifacts:
  - research/artifacts/sl3z-normal-f2-obstruction-2026-09-16.md
---

Let `G <= SL_3(Z)` and `N ◁ G`. The group `G/N` acts on the set of
`N`-conjugacy classes `[x]_N` of elements of `N` by
`gN . [x]_N = [g x g^-1]_N`. If `x in N` has infinite order, then

`Stab_{G/N}([x]_N) = N C_G(x) / N ≅ C_G(x) / C_N(x)`

is polycyclic. Consequently:

- if some `x in N` of infinite order has a finite `G/N`-orbit of classes,
  then `G/N` is virtually polycyclic;
- if `G/N` is free, every such stabilizer is trivial or infinite cyclic.

For classes of subgroups `A <= N` the same bookkeeping gives
`Stab_{G/N}([A]_N) ≅ N_G(A)/N_N(A)`. This holds in any group.

Use for Serre's question: it constrains the monodromy of every
normal-subgroup fibration inside `SL_3(Z)`, including the free-by-free and
surface-by-free candidates for `sl3z-contains-cd2-euler-positive-fibered-subgroup`.
See `sl3z-normal-f2-subgroups-have-virtually-cyclic-quotients` and the
artifact (Corollaries A4 and A5).
