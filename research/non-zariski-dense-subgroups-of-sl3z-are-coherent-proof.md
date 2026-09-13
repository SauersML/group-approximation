---
rg: 2
id: non-zariski-dense-subgroups-of-sl3z-are-coherent-proof
kind: route
title: Check coherence in each of the three non-dense cases
target: non-zariski-dense-subgroups-of-sl3z-are-coherent
requires:
  - sl3z-non-dense-subgroups-classified
  - sl3z-parabolic-subgroups-are-coherent
artifacts:
  - research/artifacts/zp-sl3z-coherence-non-dense-2026-09-13-part1.md
---

By `sl3z-non-dense-subgroups-classified`, `H` falls in case (V), (F) or (P).

- **(V)** Every subgroup of a virtually polycyclic group is finitely presented.
- **(F)** A finitely generated subgroup `K` of a discrete subgroup of
  `SO(2,1)` meets the identity component `PSL_2(R)` in a finitely generated
  Fuchsian group of index at most 2. Finitely generated Fuchsian groups are
  geometrically finite (Siegel), hence finitely presented, so `K` is finitely
  presented.
- **(P)** `H` is conjugate into a coherent maximal parabolic subgroup
  (`sl3z-parabolic-subgroups-are-coherent`), and coherence passes to
  subgroups.

This is Theorem 3.2 of the artifact.
