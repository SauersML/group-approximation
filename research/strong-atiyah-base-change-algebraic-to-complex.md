---
rg: 2
id: strong-atiyah-base-change-algebraic-to-complex
kind: claim
title: Strong Atiyah over the algebraic numbers for all torsion-free groups implies it over the complex numbers
distinct_from:
  strong-atiyah-torsion-free: that is the complex-coefficient conjecture itself; this is only the base-change implication from algebraic to complex coefficients.
  algebraic-strong-atiyah-for-all-torsion-free-groups: that is the algebraic-coefficient conjecture; this is the implication from it to the complex case.
---

**OPEN.**  If every torsion-free group satisfies Strong Atiyah over `Qbar`,
then every torsion-free group satisfies it over `C`.

For a single sofic group the implication is a theorem: Jaikin-Zapirain, GAFA
29 (2019), Theorem 1.1, cited in arXiv:2201.03268, Remark 3.8, as "for a sofic
group G, the strong Atiyah conjecture over Qbar implies the strong Atiyah
conjecture over C".

## Attempts

* **Group by group.**  The sofic base change does not apply to the nonsofic
  hosts of this region: the master tester, and the Fournier--Facio group inside
  it (`universal-torsion-free-hosts-not-sofic-or-locally-indicable`).
* **Colimit permanence.**  `algebraic-atiyah-with-determinant-closed-under-colimits`
  controls small spectrum through integral determinants after restriction of
  scalars.  Transcendental coefficients have no such integral form, so the
  argument gives nothing over `C`.
* **Central variables.**  Replacing transcendental coefficients by central
  generators, `G x Z^r`, computes an average of kernel dimensions over a torus
  of specializations.  On its own this does not give the dimension at one
  transcendental point.  With Galois invariance it does: generic
  specializations are Galois conjugates, and restriction of scalars along two
  functions of coprime degrees (Riemann--Roch) removes the leftover
  denominator.  This is `strong-atiyah-base-change-from-galois-invariance`, and
  the live route `strong-atiyah-base-change-via-galois-invariance` needs only
  `vn-rank-galois-invariant-for-torsion-free-groups`.
