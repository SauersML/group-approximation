---
rg: 2
id: type-fh3-iff-fp3-and-superperfect-kernel-over-fp-group
kind: claim
title: "A group is of type FH_3 iff it is of type FP_3 and a finitely presented group maps onto it with superperfect kernel"
distinct_from:
  every-type-fpn-group-is-of-type-fhn: that claim is the open implication FP_n implies FH_n for all n; this is a proved characterization of FH_3 in terms of finite presentations
  type-fp2-groups-are-of-type-fh2: that claim settles n <= 2 with no condition; this characterizes n = 3, where a condition on the kernel appears
artifacts:
  - research/artifacts/zp-fpn-fhn-2026-09-13-part2.md
---

For a group `G` the following are equivalent:

1. `G` acts properly (equivalently freely) and cocompactly on a 2-acyclic CW
   complex, i.e. `G` is of type `FH_3`;
2. `G` is of type `FP_3`, and there are a finitely presented group `Q` and a
   surjection `Q → G` whose kernel `P` satisfies `H_1(P; ℤ) = H_2(P; ℤ) = 0`.

**Consequence.** At `n = 3`, Zaremsky Problem 1.4 is exactly the
group-theoretic question: *is every group of type `FP_3` a quotient of a
finitely presented group by a superperfect normal subgroup?*

In the `G`-cover of a presentation complex of `Q`, the only obstruction to
attaching finitely many orbits of 3-cells is `H_2(P)`. It is the cokernel of
the Hurewicz map, by Hopf's theorem.

Proof: Theorem D of `research/artifacts/zp-fpn-fhn-2026-09-13-part2.md`, §6.
Unreviewed.
