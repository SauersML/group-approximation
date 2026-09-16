---
rg: 2
id: soluble-automatic-va-from-amenable-case
kind: route
title: Soluble groups are amenable, so the amenable automatic case gives Thurston's soluble case
target: soluble-automatic-groups-are-virtually-abelian
requires:
  - amenable-automatic-groups-are-virtually-abelian
---

## Why sufficient

Let `G` be a soluble automatic group. Abelian groups are amenable, and an extension of
an amenable group by an amenable group is amenable. `G` has a finite subnormal series with
abelian factors, so induction on its length shows that `G` is amenable. The prerequisite
then makes `G` virtually abelian.

This is the first forward half of Proposition 6 in
`research/artifacts/amenable-automatic-groups-are-virtually-abelian-2026-09-16.md`,
Section 6. It records that the target of
`amenable-automatic-va-via-ea-and-soluble-case` is at least as hard as Thurston's
conjecture.
