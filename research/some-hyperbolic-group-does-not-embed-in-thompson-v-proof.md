---
rg: 2
id: some-hyperbolic-group-does-not-embed-in-thompson-v-proof
kind: route
title: An infinite hyperbolic Kazhdan group cannot embed in V because V has the Haagerup property
target: some-hyperbolic-group-does-not-embed-in-thompson-v
requires:
  - thompson-v-has-haagerup-property
  - torsion-free-hyperbolic-kazhdan-partner-exists
---

1. By `torsion-free-hyperbolic-kazhdan-partner-exists` there is a group `H`
   that is infinite, non-elementary, finitely presented, torsion-free,
   word-hyperbolic and Kazhdan. For example, take a torsion-free finite-index
   subgroup of a cocompact lattice in Sp(2,1).
2. By `thompson-v-has-haagerup-property` every subgroup of V with property (T)
   is finite. The reason is that the Haagerup property passes to subgroups, and
   a countable group with both property (T) and the Haagerup property is finite.
3. Suppose `φ: H → V` is injective. Then `φ(H) ≅ H` is an infinite subgroup of
   V with property (T), which contradicts step 2. So `H` does not embed in V.

The argument uses only that `H` is infinite and has property (T). Hyperbolicity
is what makes `H` answer Problem 2.19(b), since that part asks for a hyperbolic
group.
