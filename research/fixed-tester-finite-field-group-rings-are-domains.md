---
rg: 2
id: fixed-tester-finite-field-group-rings-are-domains
kind: claim
title: Finite-field group rings of the fixed torsion-free tester are domains
distinct_from:
  kaplansky-all-fields-reduce-to-finite-fields-on-one-group: that proves the equivalence with the global conjecture; this is the open finite-field statement on the one group.
  kaplansky-zero-divisor-conjecture: that is the conjecture over every field and every torsion-free group; this is its equivalent form over finite fields on the fixed tester.
---

For every finite field `F`, the group ring `F[U]` of the fixed finitely
presented torsion-free tester `U` of
`kaplansky-three-properties-fixed-fp-torsion-free-tester` has no zero
divisors.

## Attempts

* **Structural methods.** `U` is built as a universal host, so it contains
  torsion-free groups without unique products (the Promislow group) and
  nonsofic torsion-free groups, and it is not elementary amenable. So neither
  unique products nor Kropholler--Linnell--Moody applies. Strong Atiyah is
  open for `U`, and it says nothing in positive characteristic.
* **Direct search.** `U` contains finitely presented torsion-free groups with
  unsolvable word problem (the Boone--Novikov groups are iterated HNN
  extensions of free groups). So its Cayley balls cannot be enumerated
  exactly, and a search has to run inside explicit subgroups with solvable
  word problem. The host analysis is on `kaplansky-zero-divisor-conjecture`.
