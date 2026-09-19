---
rg: 2
id: kaplansky-finite-field-transfer-on-the-fixed-tester
kind: route
title: Transfer finite-field truth and then apply the fixed-group tester
target: kaplansky-all-fields-reduce-to-finite-fields-on-one-group
requires:
  - kaplansky-three-properties-fixed-fp-torsion-free-tester
---

Use the same `U` as in
[[kaplansky-three-properties-fixed-fp-torsion-free-tester]].

For one fixed torsion-free group, Ceccherini-Silberstein, Coornaert, and
Phung, *First-order model theory and Kaplansky's stable finiteness conjecture
for surjunctive groups*, Groups Geom. Dyn. 19 (2025), 495--503,
doi:10.4171/GGD/885, Remark 4.4, prove separately for units, zero divisors,
and idempotents that validity over every finite field implies validity over
every field. Their argument replaces the finite first-order witness used for
stable finiteness by the corresponding sentence for each of the three
properties.

Therefore, if `P(F[U])` holds for every finite field `F`, then `P(k[U])`
holds for every field `k`. Apply the fixed-field tester equivalence for each
`k` to obtain `P(k[G])` for every torsion-free `G`. The converse is
immediate because `U` is torsion-free and finite fields are fields. QED
