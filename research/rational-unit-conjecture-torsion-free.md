---
rg: 2
id: rational-unit-conjecture-torsion-free
kind: claim
title: Rational group rings of torsion-free groups have only trivial units
root: true
distinct_from:
  unit-conjecture-fails-over-complex-numbers: that refutes the unit conjecture over C, with coefficients in Z[zeta_8]; this is the field Q, which has no primitive eighth root of unity, and it is open.
  integral-unit-conjecture-torsion-free: that has coefficients in Z and follows from this; this has coefficients in the field Q.
  kaplansky-three-properties-fixed-fp-torsion-free-tester: that reduces the unit statement over a field to one fixed tester group; this is the unit statement over Q itself.
  kaplansky-zero-divisor-conjecture: that asks for no zero divisors over every field; this asks for trivial units over Q.
  rational-units-rescale-to-integral-units: that transfers units between Q and Z on one group under a domain hypothesis; this is the conjecture for every torsion-free group.
---

For every torsion-free group `G`, every unit of `Q[G]` is `lambda g` with
`lambda in Q^x` and `g in G`.

*Marked `root`: Kaplansky's unit conjecture over the prime field of
characteristic zero.* The field version is false over every field of positive
characteristic (Gardam 2021, Murray 2021). It is also false over every field
containing a primitive eighth root of unity, because Gardam's complex units
have coefficients in `Z[zeta_8]` (`unit-conjecture-fails-over-complex-numbers`).
Tabei (arXiv:2608.02982v1, Section 1) records that it "remains open over Q
and over R — and over Z".

The route `integral-unit-conjecture-from-rational-proof` derives
`integral-unit-conjecture-torsion-free` from this claim.

## Attempts

* **Reduction to Z.** On `P`, and on every torsion-free elementary amenable
  group, this is equivalent support by support to the integral conjecture
  (`rational-units-rescale-to-integral-units`). So every obstruction recorded
  under `integral-unit-conjecture-torsion-free` applies verbatim, and the
  attack dies at the same Case A.
* **Galois norm of Gardam's unit.** Galois conjugates of Gardam's unit are
  units of `Q(zeta_8)[P]`. The ring is noncommutative, so a product of
  conjugates is not Galois-invariant and there is no norm into `Q[P]`.
  Restriction of scalars gives an element of `GL_4(Q[P])`, not a unit of
  `Q[P]`. The attack dies at the missing norm.
* **Tester group.** By `kaplansky-three-properties-fixed-fp-torsion-free-tester`
  it is enough to decide `Q[U]` for one finitely presented torsion-free group
  `U`. That reformulates the problem without deciding it.
