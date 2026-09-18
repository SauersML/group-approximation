---
rg: 2
id: dadarlat-linear-groups-have-nonzero-h2-windings
kind: claim
title: Every non-torsion second-homology class of a finitely generated linear group has a nonzero matricial winding along some asymptotic homomorphism
distinct_from:
  exel-loring-relative-quasirep-invariant: that imports Dadarlat's pairing and his nontriviality theorem as a relative invariant of a candidate extension; this imports only Theorem 3.2 and its linear-group sentence, as the absolute statement used against Schur kernels.
  dadarlat-matricial-stability-obstruction: that is Corollary 3.3 (no genuine approximants when H_2(Gamma;Q) != 0); this is the underlying Theorem 3.2, class by class, with the winding number itself nonzero.
---

Marius Dadarlat, *Quasi-representations of groups and two-homology*,
arXiv:2111.05755 (dated November 11, 2021). Verbatim, from the primary text.

**Notation (display (9)).** "Chose a free resolution of Γ:
(9) 0 → R → F → Γ → 0, q(a) = ā, where F and R are free groups. By Hopf's
formula [3], H2(Γ, Z) = R ∩ [F,F] / [R,F]. Thus each element x ∈ H2(Γ, Z) is
represented by a product of commutators, ∏[ai, bi] with ai, bi ∈ F for some
integer g ≥ 1 and such that ∏[āi, b̄i] = 1."

**Definition.** "A countable discrete group G is quasidiagonal if it is
isomorphic to a subgroup of the unitary group of a quasidiagonal C*-algebra
[8]. ... Thus, a maximally almost periodic group (MAP) is quasidiagonal."

> **Theorem 3.2.** Let Γ be a quasidiagonal group which admits a γ-element.
> Suppose that x is a non-torsion element of H2(Γ, Z) represented by a
> product of commutators ∏_{i=1}^g [ai, bi] with ai, bi ∈ F and
> ∏_{i=1}^g [āi, b̄i] = 1. Then there is an asymptotic homomorphism
> {πn : Γ → U(kn)}n such that
> wn det((1−t)1_{kn} + t ∏_{i=1}^g [πn(āi), πn(b̄i)]) ≠ 0
> for all sufficiently large n.

**Linear groups (sentence after the proof).** "Any finitely generated linear
group Γ is residually finite by Malcev's theorem and exact by [13] and so it
satisfies the hypotheses of Theorem 3.2."

**Meaning of the terms, from the same paper.**

- The maps in Theorem 3.2 are unital maps `πn : Γ → U(kn)` with
  `lim_n ||πn(st) − πn(s)πn(t)|| = 0` for all `s, t ∈ Γ`. In the proof, the
  πn are obtained "by functional calculus ... [as] a unital map πn : Γ → U(kn)",
  and Theorem 1.1 is stated for a "unital map with ‖π(st)−π(s)π(t)‖ < ε".
- Lemma 2.1: "If w ∈ SU(n) and ‖w − 1‖ < 2, then
  wn det((1−t)1n + tw) = κ(w)", where κ(w) = (1/2πi) Tr(log(w)) with the
  principal branch. The paper also records: "The function κ is continuous
  and hence locally constant as it assumes only integral values."

**Consequence used downstream.** Let Γ be a finitely generated linear group
(for example `Sp_4(Z)`) and `x ∈ H_2(Γ; Z)` non-torsion. Then some unital
asymptotic homomorphism `πn : Γ → U(kn)` has
`κ(∏[πn(āi), πn(b̄i)]) ≠ 0` for all large n. For large n the product is
within 2 of `1`, so Lemma 2.1 applies.

DERIVATION
dadarlat-linear-groups-have-nonzero-h2-windings-citation
