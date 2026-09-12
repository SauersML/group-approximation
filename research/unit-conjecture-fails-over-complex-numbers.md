---
rg: 2
id: unit-conjecture-fails-over-complex-numbers
kind: claim
title: The Kaplansky unit conjecture fails over the complex numbers, on the Promislow group
distinct_from:
  promislow-radius4-one-sided-and-integral-separation: that is an exact radius-four unit census over F_2 with an integral lifting obstruction; this imports the existence of a nontrivial unit in the complex group ring of the same group.
---

**ESTABLISHED (citation).** Let

```text
P = <a, b | b^(-1) a^2 b = a^(-2), a^(-1) b^2 a = b^(-2)>,
```

the torsion-free Promislow (Hantzsche--Wendt) group. Then `C[P]` has
nontrivial units: units that are not of the form `lambda g` with
`lambda in C^x` and `g in P`.

So the Kaplansky unit conjecture fails in characteristic zero, not only over
`F_2` (Gardam 2021) and other positive characteristics.

Consequences for this graph:
- The unit conjecture is refuted over every characteristic that has been
  tested. The idempotent and zero-divisor conjectures stay open.
- `P` is virtually `Z^3`, hence elementary amenable. By
  Kropholler--Linnell--Moody, `k[P]` is a domain for every field `k`. So the
  unit counterexample says nothing about zero divisors
  (`kaplansky-zero-divisor-conjecture`).

DERIVATION
[[gardam-complex-units-citation]]
