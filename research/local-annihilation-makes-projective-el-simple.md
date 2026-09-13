---
rg: 2
id: local-annihilation-makes-projective-el-simple
kind: claim
title: Over a simple ring with local annihilation, every normal subgroup of EL_n (n >= 3) is central or everything
distinct_from:
  stepanov-linear-dependence-standard-normal-structure: that is Stepanov's theorem under the linear-dependence condition (b), whose Lemma 4.3 is this criterion's extraction step; this assumes local annihilation, which (b) does not imply.
  vaserstein-local-stable-range-normal-subgroups: that is Vaserstein's localized stable-range theorem; this needs no stable range.
artifacts:
  - research/artifacts/un-steinberg-elementary-simplicity-2026-09-13.md
  - research/artifacts/un-stepanov-credit-2026-09-13.md
  - GroupApproximation/Pestov91/SimpleModCentre.lean
---

**ESTABLISHED (Lean on main, root-imported; paper proof unreviewed).** Let `R` be a unital simple ring with local
annihilation: for every finite `F ⊆ R`, the elements `s` admitting `t ≠ 0` with `ts = 0` and `tfs = 0` for all
`f ∈ F` generate `R` as a non-unital ring. Let `n ≥ 3`. Then every normal subgroup of `EL_n(R)` is central or all of
`EL_n(R)`. So `EL_n(R)/Z(EL_n(R))` is simple, and `Z(EL_n(R)) ⊆ Z(R)^× I_n`.

Lean: `GroupApproximation.Pestov91.isSimpleGroup_elementaryGroup_quotient_center`
(`hcard : 3 ≤ Fintype.card ι`, `[IsSimpleRing R]`, `hloc : LocalAnnihilation R`). No sandwich theorem and no
stable-range or exchange hypothesis is used.

This is the common ring criterion behind the simplicity halves of the Pestov 9.1 answer (via
`localAnnihilation_of_crossedProduct`) and of the Leavitt unit groups: L_k(1,d) is a Steinberg algebra, see
`steinberg-algebras-have-local-annihilation`.

**Credit (un-stepanov-credit, 2026-09-13).**
- **Prior:** the extraction step (a nonzero left annihilator of an off-diagonal entry of a noncentral element of a
  normal subgroup forces a transvection) is Stepanov's Lemma 4.3, J. Math. Sci. 95 (1999) p. 2151; see
  `stepanov-linear-dependence-standard-normal-structure`.
- **New:** the hypothesis, local annihilation, which supplies such elements in every simple ring that has it.
- **Relation to Stepanov's Theorem 4.4:** condition (b) does not imply local annihilation (simple Artinian rings,
  `division-rings-satisfy-stepanov-b-not-local-annihilation`). Whether local annihilation implies (b) is open
  (`local-annihilation-implies-stepanov-condition-b`).
- **Vaserstein's stable-range criteria** (`vaserstein-local-stable-range-normal-subgroups`) are not known to cover
  these rings.
- Details: `research/artifacts/un-stepanov-credit-2026-09-13.md`.

**Review (un-verify, 2026-09-13): PASS.** Paper steps and the centre clause re-derived; the Lean signature `(hcard : 3 ≤ Fintype.card ι) [IsSimpleRing R] (hloc : LocalAnnihilation R)` is as cited, and the module is root-imported. See `research/artifacts/un-review-2026-09-13-part1.md` §4.
