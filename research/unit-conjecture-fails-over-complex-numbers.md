---
rg: 2
id: unit-conjecture-fails-over-complex-numbers
kind: claim
title: The Kaplansky unit conjecture fails over the complex numbers, on the Promislow group
distinct_from:
  promislow-radius4-one-sided-and-integral-separation: that is an exact radius-four unit census over F_2 with an integral lifting obstruction; this imports the existence of a nontrivial unit in the complex group ring of the same group.
  rational-unit-conjecture-torsion-free: that is the open unit conjecture over Q, which has no primitive eighth root of unity; this is the refutation over C with coefficients in Z[zeta_8].
  integral-unit-conjecture-torsion-free: that is Higman's open integral conjecture; this is a refutation over fields containing Z[zeta_8].
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

**Coefficient field.** The units have coefficients in `Z[zeta_8]`. They come
from a unit of `R[P]` with `R = Z[s,t]/<s^4+1, t^4+1>`, specialized at two
primitive eighth roots of unity. So the conjecture fails over every field of
characteristic zero that contains a primitive eighth root of unity. The
conjecture is still open over `Q`, over `R` and over `Z`
(`rational-unit-conjecture-torsion-free`,
`integral-unit-conjecture-torsion-free`).

Consequences for this graph:
- The unit conjecture is refuted in every positive characteristic. In
  characteristic zero it is refuted only over fields containing `zeta_8`.
  The idempotent and zero-divisor conjectures stay open.
- `P` is virtually `Z^3`, hence elementary amenable. By
  Kropholler--Linnell--Moody, `k[P]` is a domain for every field `k`. So the
  unit counterexample says nothing about zero divisors
  (`kaplansky-zero-divisor-conjecture`).

DERIVATION
[[gardam-complex-units-citation]]
