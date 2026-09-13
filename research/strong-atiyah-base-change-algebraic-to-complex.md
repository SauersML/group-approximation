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
* **Pointwise off a countable set (2026-09-12, lane `ex-atiyah-torsion-free`).**
  *Proved for purely transcendental coefficient fields, group by group; algebraic
  extensions remain.*
  - `atiyah-base-change-holds-off-a-countable-set`: for a torsion-free `G` with
    Strong Atiyah over `Qbar`, integrality over `Qbar(z)[G]` fails only at a
    countable set `E_G` of transcendental `z`. In several variables the
    exceptions form a null meagre set. The proof uses Jacobson's normal form over
    `D_(Qbar[G])[x]` and independence of eigenspaces, with no approximation of the
    group.
  - One-variable Galois invariance is equivalent to `E_G = ∅`.
  - Under the determinant conjecture, no point of `E_G` is algebraically
    Liouville, and each is badly approximable by algebraic numbers of every
    bounded degree (`determinant-conjecture-excludes-liouville-atiyah-exceptions`).
  - What is left: emptiness of `E_G`, and finite extensions `F` of
    `Qbar(z_1..z_s)`, where `D(x_1..x_s) (x) F` must stay a skew field in `U(G)`
    (Jaikin-Zapirain--Lopez-Alvarez, arXiv:1810.12135v4, Conjecture 3).
