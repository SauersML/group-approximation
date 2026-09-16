---
rg: 2
id: automatic-groups-virtually-abelian-or-free-subsemigroup
kind: claim
title: Every automatic group is virtually abelian or contains a free subsemigroup of rank two
distinct_from:
  fp-groups-without-free-subsemigroups-are-virtually-nilpotent: that is Grigorchuk's open conjecture for all finitely presented groups; this is the automatic case, with the stronger conclusion virtually abelian, established through regular-language pumping
  amenable-automatic-groups-are-virtually-abelian: that open claim assumes amenability, which does not exclude free subsemigroups; this assumes nothing beyond automaticity and allows a free subsemigroup as the other outcome
artifacts:
  - research/artifacts/amenable-automatic-groups-are-virtually-abelian-2026-09-16.md
---

Let `G` be an automatic group. Then `G` has an abelian subgroup of finite index, or `G`
has two elements that freely generate a free subsemigroup of rank 2. The two outcomes are
exclusive.

In particular an automatic group of subexponential growth is virtually abelian, and no
automatic group has intermediate growth. A counterexample to
`amenable-automatic-groups-are-virtually-abelian` must have exponential growth and a free
subsemigroup of rank 2.

Proof route: `automatic-va-or-free-subsemigroup-proof` (Theorem 4 of the artifact). No
priority is claimed. The polynomial half is the mechanism of the ECHLPT nilpotent theorem,
and the exponential half is standard regular-language pumping.
