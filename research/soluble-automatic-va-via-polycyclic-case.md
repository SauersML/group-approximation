---
rg: 2
id: soluble-automatic-va-via-polycyclic-case
kind: route
title: Soluble automatic groups are virtually abelian if they are polycyclic, by Harkins' theorem
target: soluble-automatic-groups-are-virtually-abelian
requires:
  - soluble-automatic-groups-are-polycyclic
  - polycyclic-automatic-groups-are-virtually-abelian
---

## Why sufficient

Let `G` be a soluble automatic group. By `soluble-automatic-groups-are-polycyclic`, `G`
is polycyclic. `G` is then polycyclic and automatic, so
`polycyclic-automatic-groups-are-virtually-abelian` makes it virtually abelian.

The converse is `soluble-automatic-polycyclic-from-virtually-abelian-case`. So, given
Harkins' theorem, Thurston's conjecture is exactly the statement that soluble automatic
groups are polycyclic. See
`research/artifacts/amenable-automatic-groups-are-virtually-abelian-2026-09-16.md`,
Section 7.
