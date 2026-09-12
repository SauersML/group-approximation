---
rg: 2
id: zero-divisor-via-fixed-tester-finite-fields
kind: route
title: Check the fixed torsion-free tester over every finite field
target: kaplansky-zero-divisor-conjecture
requires:
  - kaplansky-all-fields-reduce-to-finite-fields-on-one-group
  - fixed-tester-finite-field-group-rings-are-domains
---

Apply `kaplansky-all-fields-reduce-to-finite-fields-on-one-group` with `P` =
"is a domain". The conjecture for every field and every torsion-free group is
then equivalent to `F[U]` being a domain for every finite field `F`, where `U`
is the fixed finitely presented torsion-free tester. The second prerequisite
supplies exactly this.
