---
rg: 2
id: full-farrell-jones-for-fixed-two-generator-all-group-tester
kind: claim
title: The fixed two-generator all-group tester satisfies Full Farrell--Jones
distinct_from:
  full-farrell-jones-fixed-two-generator-all-group-tester: that is the established exact reduction; this is the one open membership assertion it isolates.
  full-farrell-jones-for-fixed-fp-torsion-free-tester: that is the torsion-free tester and only reaches torsion-free groups; this is the torsionful host, whose membership gives every group, including groups with torsion.
---

**OPEN.** Let `U` be the fixed two-generator finitely presented group of
[[full-farrell-jones-fixed-two-generator-all-group-tester]]: the torsionful
host of [[universal-all-group-subgroup-colimit-class-tester]], with
`Tord(U) = {2,3,4,...}`. Then `U` belongs to Lueck's Full Farrell--Jones class
`FJ`. That class covers algebraic K- and L-theory with additive-category
coefficients and finite wreath products.

By the established tester equivalence, this one assertion has exactly the
same truth value as "every group belongs to `FJ`". Every group would then
satisfy the K-theoretic Farrell--Jones conjecture with additive coefficients
relative to `VCyc`.

**Why it is isolated here.** This is the only open prerequisite of route
`free-action-leavitt-k1-k2-via-farrell-jones-with-torsion` into premise (K) of
`boone-higman-via-leavitt-units-of-rigid-sft-overgroups`. That premise needs
the Farrell--Jones conjecture only for the acting group produced by
`decidable-groups-lie-in-fp-free-minimal-crossed-products`, which is not known
to be a Farrell--Jones group.

## Attempts

- **Inheritance from known Farrell--Jones classes (deferred; dies at universality).**
  - `FJ` is closed under subgroups, finite products, free products, directed colimits, and
    extensions with Farrell--Jones kernel and quotient data. It contains hyperbolic groups, CAT(0)
    groups, lattices in almost connected Lie groups, `GL_n(Z)`, mapping class groups, and
    solvable groups.
  - Any proof that places `U` in the closure of these classes would, by the tester equivalence,
    prove the Farrell--Jones conjecture for **every** group. Every group, including groups with
    torsion, would then embed in a member of the closure.
  - No such structural description of `U` is known. The tester's defining property is that its
    subgroups realise arbitrary groups, so this is exactly the full conjecture. No counterexample
    is known either.
- Recorded as a single named hole. It is useful as the last open input of
  `free-action-leavitt-k1-k2-via-farrell-jones-with-torsion`, not as a new line of attack.
