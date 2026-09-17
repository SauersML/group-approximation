---
rg: 2
id: kazhdan-subgroups-of-nv-finite-from-finite-orbits
kind: route
title: "If Kazhdan subgroups of nV have finite orbits on C^n, they are finite: finite-index stabilizers kill germ characters, and bounded offsets bound the group"
target: kazhdan-subgroups-of-brin-thompson-groups-are-finite
requires:
  - kazhdan-subgroups-of-nv-act-with-finite-orbits
  - finitely-generated-subgroups-of-nv-are-finite-iff-germ-finite
---

Let `K ≤ nV` have property (T). Then `K` is finitely generated. Its finite-index
subgroups have property (T), so they have finite abelianization
(Bekka–de la Harpe–Valette, Theorem 1.7.1 and Corollary 1.3.6).

By `kazhdan-subgroups-of-nv-act-with-finite-orbits`, all `K`-orbits on `C^n`
are finite. The addendum of
`finitely-generated-subgroups-of-nv-are-finite-iff-germ-finite` then gives that
`K` is finite.

**Converse.** Finite groups have finite orbits. So this route loses nothing, and
the finiteness problem for Kazhdan subgroups of `nV` is exactly the
orbit-finiteness problem.
