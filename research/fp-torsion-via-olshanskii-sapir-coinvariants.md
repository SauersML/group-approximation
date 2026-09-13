---
rg: 2
id: fp-torsion-via-olshanskii-sapir-coinvariants
kind: route
title: An infinite coinvariant group of the Ol'shanskii–Sapir extension gives a finitely presented infinite torsion group
target: there-is-a-finitely-presented-infinite-torsion-group
requires:
  - olshanskii-sapir-hnn-has-infinite-coinvariants
  - ascending-hnn-torsion-quotients-see-only-coinvariants
  - olshanskii-sapir-fp-ascending-hnn-of-exponent-n-group
---

`𝒢 = H̄*_phi` is finitely presented, and its base `H̄` has exponent `n`, so it is
torsion (`olshanskii-sapir-fp-ascending-hnn-of-exponent-n-group`). Suppose
`H̄_{phi^m}` is infinite for some `m >= 1`
(`olshanskii-sapir-hnn-has-infinite-coinvariants`). Item 3 of
`ascending-hnn-torsion-quotients-see-only-coinvariants` then gives that
`𝒢/<<t^m>> ≅ H̄_{phi^m} x| Z/m` is an infinite torsion group. It is finitely
presented, as a quotient of the finitely presented `𝒢` by one normal generator.

This route is a real reduction, not a restatement: its open premise is about
one concrete group, and it can fail while Problem 1.11 has a positive answer
elsewhere.
