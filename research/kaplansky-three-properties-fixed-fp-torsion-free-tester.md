---
rg: 2
id: kaplansky-three-properties-fixed-fp-torsion-free-tester
kind: claim
title: One finitely presented torsion-free group tests Kaplansky's three group-ring properties
distinct_from:
  whitehead-universal-finitely-presented-torsion-free-group: that constructs the universal host and controls Whitehead groups; this uses only its group embeddings and concerns group rings over fields.
  full-farrell-jones-fixed-fp-torsion-free-tester: that tests a coefficient-rich assembly property; this tests domain, idempotent, and unit properties of ordinary group rings.
  subgroup-supported-one-sided-inverse-rigidity: that localizes a one-sided inverse under a direct-finiteness hypothesis; this is a global exact tester theorem for standard two-sided units and two other ring properties.
---

There exists a single finitely presented torsion-free group `U`, independent
of the coefficient field, such that for every field `k` the following three
equivalences hold separately:

1. `k[U]` is a domain iff `k[G]` is a domain for every torsion-free group
   `G`.
2. `Idem(k[U])={0,1}` iff `Idem(k[G])={0,1}` for every torsion-free group
   `G`.
3. Every two-sided unit of `k[U]` is `lambda u`, with `lambda in k^x` and
   `u in U`, iff the analogous statement holds for every torsion-free `G`.

The same `U` works simultaneously for all fields. These are tester
equivalences, not affirmative solutions: the zero-divisor and idempotent
statements remain open globally, while the unit statement is already false
for some fields (in particular `F_2`).

**ESTABLISHED 2026-08-30** by
[[kaplansky-tester-via-subgroups-and-directed-colimits]].
