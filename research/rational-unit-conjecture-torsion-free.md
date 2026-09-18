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
* **Descent on the support of Gardam's unit.** On Gardam's 21-element support
  pair, a field of characteristic zero carries a nontrivial unit only if it
  contains `zeta_8` (`gardam-support-pair-has-no-rational-units`). So the
  complex units do not descend to `Q`, or even to `R` or `Q_2`, on their own
  support. The attack dies at the choice of support. The next bullet extends
  it to the other pairs of the radius-four census.
* **Descent on the radius-four census pairs.** Let `S` be the support of one
  of the 52 units of `F_2[P]` supported in `B(4)`, and `T` the support of its
  inverse. A field of characteristic zero carries a nontrivial unit with
  support in `S` and inverse support in `T` only if it contains `zeta_8`
  (`promislow-radius4-support-pairs-need-zeta8`). The attack dies at the
  inverse support, which is fixed to `T`, and at supports that are not the
  support of a unit of `F_2[P]`.
* **Galois norm of Gardam's unit.** Galois conjugates of Gardam's unit are
  units of `Q(zeta_8)[P]`. The ring is noncommutative, so a product of
  conjugates is not Galois-invariant and there is no norm into `Q[P]`.
  Restriction of scalars gives an element of `GL_4(Q[P])`, not a unit of
  `Q[P]`. The attack dies at the missing norm.
* **Murray's z-only ansatz.** Murray builds nontrivial units of `F_d[P]` for
  every odd prime `d` from coefficients that depend on `z = (ab)^2` alone,
  with Gardam's formula for the inverse. Over every field of characteristic
  zero this ansatz has only the trivial solutions `+-z^k ab`, with no bound on
  the length of the coefficients (`murray-z-only-ansatz-has-no-char0-units`).
  The attack dies at the shape of the ansatz: units whose coefficients involve
  `x` or `y` beyond Murray's fixed factors, or whose inverse is not given by
  Gardam's formula, are not covered.
* **Tester group.** By `kaplansky-three-properties-fixed-fp-torsion-free-tester`
  it is enough to decide `Q[U]` for one finitely presented torsion-free group
  `U`. That reformulates the problem without deciding it.
* **Definite shadows (positivity).** Every unit of `Z[P]`, and after rescaling
  every unit of `Q[P]`, maps to a signed monomial in the three quotients
  `Z[P]/(x+1, y+1)`, `Z[P]/(y+1, z+1)` and `Z[P]/(x+1, z+1)`. Each is a definite
  quaternion-type ring whose norm has a sum of squares as constant term
  (`promislow-integral-units-have-monomial-definite-line-shadows`). This fails
  over `Z[zeta_8]`: Gardam's complex unit has non-monomial shadows of norm 1.
  As a consequence no unit of `Z[P]` reduces to Gardam's unit, to a radius-four
  census unit, or to Murray's units for `d = 3, 5, 7`, at any support or height
  (`promislow-classical-nontrivial-units-have-no-integral-lifts`). The attack
  dies at the kernels: it says nothing about units in
  `+-g + (I_A cap I_B cap I_C)`, and every normalized Case A unit already lies
  in `+-1 + (I_A cap I_B cap I_C)`.
* **Mahler-measure / spectral dichotomy.** The idea was to split units of
  `Q[P]` by the Mahler measure of the characteristic polynomial of their
  induced `4 x 4` matrix over `Q[L]`. Either it is zero, so the unit is
  quasi-unipotent over `L` and should be trivial, or it is positive, with
  exponential coefficient growth to be ruled out. Nontrivial units fall on
  both sides. Gardam's complex unit has Mahler measure about `1.41`, while its
  conjugate `alpha x alpha^-1` has Mahler measure 0. The attack dies at the
  conjugation `u -> u x u^-1`. That map preserves the characteristic
  polynomial, spectral radius, Brown measure, Fuglede--Kadison determinant and
  trace sequence, and the result is still nontrivial. Pushing this through
  gives an equivalent reformulation over every commutative domain
  (`promislow-units-iff-axis-quadratic-roots`). `R[P]` has a nontrivial unit
  iff `v^2 - (x + x^-1) v + 1 = 0` has a root other than `x^(+-1)`. Every such
  root has exactly the spectral invariants of `x`, so no
  conjugation-invariant spectral argument can prove the conjecture on `P`.
  Over `Z` the nontrivial roots lie in `x + (I_A cap I_B cap I_C)` after
  `v -> x + x^-1 - v`. That is Case A of the definite shadows, where that
  method is silent.
