---
rg: 2
id: kazhdan-hyperbolic-group-without-finite-quotients
kind: claim
title: An infinite word-hyperbolic Kazhdan group with no nontrivial finite quotient
distinct_from:
  hyperbolic-group-without-finite-quotients: that is the plain Kapovich--Wise target without property (T); this adds (T), and the extra clause is free by Olshanskii's common quotients
  torsion-free-hyperbolic-kazhdan-partner-exists: that is an established existence theorem for a hyperbolic Kazhdan group, which is residually finite; this demands a hyperbolic Kazhdan group with no finite quotients at all, which is open
  simple-kazhdan-groups-have-full-mf-radical: that proves full MF radical for simple Kazhdan groups, none of which is known to be hyperbolic; this asks for a hyperbolic Kazhdan group without finite quotients, which is non-MF by Ozawa--Thom (premise refuted 2026-09-12, see body)
---

Exhibit an infinite word-hyperbolic group `Q` with property `(T)` such that
every homomorphism from `Q` to a finite group is trivial.

By `mf-kazhdan-group-without-finite-quotients-is-trivial`, such a `Q` is not MF,
so it is a `non-mf-hyperbolic-group`.  By
`kazhdan-quotientless-hyperbolic-via-common-quotient` it exists as soon as any
non-residually-finite hyperbolic group exists.

**Correction (2026-09-12, lane ex-kazhdan-simple-hyperlinear).**
`mf-kazhdan-group-without-finite-quotients-is-trivial` is refuted by
`lef-kazhdan-group-without-finite-quotients-exists`. So the previous paragraph does not show that
`Q` is non-MF. Showing that needs an argument that uses hyperbolicity; property (T) and the absence
of finite quotients are not enough.

## Attempts

- **Common quotient with a Kazhdan partner.**  From any infinite hyperbolic
  group without finite quotients, Olshanskii's simultaneous-surjection theorem
  and a torsion-free hyperbolic Kazhdan partner give this group.  The route is
  complete, so this claim is equivalent to Gromov's question.
- **Random groups.**  Gromov density-model random groups at density strictly
  between `1/3` and `1/2` are hyperbolic and Kazhdan, and their residual
  finiteness is not known.  No argument excluding every finite quotient of a
  specific such presentation is known; counting homomorphisms to a fixed finite
  group only excludes quotients of bounded size.  Recorded as the natural test
  class, not as an attack that makes progress.
- **Hyperbolic Kazhdan triangles of finite simple groups (2026-09-13, lane ex2-triangle-persistence;
  unreviewed).** `kazhdan-hyperbolic-sl2-root-triangles` gives an explicit test class.
  - *Parameters:* `q = 2^f >= 8`, `s ∈ F_{q^2} \ F_q`, and the gluing automorphisms of the edge groups
    `(Z/2)^f`.
  - *Vertex groups:* `SL_2(q), SL_2(q), SL_2(q^2)`, glued along root subgroups.
  - *The quotient test.* Torsion comes from three finite simple vertex groups. By
    `simple-vertex-groups-vtf-iff-some-finite-quotient`, one nontrivial finite quotient already decides
    virtual torsion-freeness.
  - *Calibration.* The untwisted member maps onto `SL_2(q^2)`. The open candidates are recorded in
    `sl2-root-kazhdan-triangle-without-finite-quotients`.
