---
rg: 2
id: kaplansky-all-fields-reduce-to-finite-fields-on-one-group
kind: claim
title: All coefficients reduce to finite fields on one finitely presented torsion-free group
distinct_from:
  kaplansky-three-properties-fixed-fp-torsion-free-tester: that fixes one coefficient field and reduces the group quantifier to one group; this also collapses the all-fields quantifier to finite fields.
  full-farrell-jones-fixed-fp-torsion-free-tester: that concerns assembly with coefficient categories; this concerns ordinary group rings over fields.
---

There exists one finitely presented torsion-free group `U` for which each
of the following three equivalences holds separately:

```text
for every field k and every torsion-free G, P(k[G])
  <=>
for every finite field F, P(F[U]),
```

where `P` is any one of:

- being a domain;
- having no idempotents other than `0` and `1`;
- having no two-sided units other than `lambda g`.

Thus the all-coefficient zero-divisor and idempotent conjectures reduce to
countably many finite-field group rings of one fixed finitely presented
torsion-free group. The unit equivalence is exact as well, but both sides are
already false because the test includes `F_2`.

**ESTABLISHED 2026-08-30** by
[[kaplansky-finite-field-transfer-on-the-fixed-tester]].
