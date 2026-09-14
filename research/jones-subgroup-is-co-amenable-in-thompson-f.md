---
rg: 2
id: jones-subgroup-is-co-amenable-in-thompson-f
kind: claim
title: Jones' oriented subgroup is co-amenable in Thompson's group F
distinct_from:
  thompson-f-is-amenable: that is amenability of F, which implies this claim; this is co-amenability of one subgroup, and a refutation of it would prove F nonamenable.
  jones-subgroup-coamenable-if-dyadic-action-extensively-amenable: that is the implication from extensive amenability of the dyadic action; this is the unconditional statement.
artifacts:
  - research/artifacts/ideas-wildcards-2026-09-14.md
---

**OPEN.** The homogeneous space `F/\vec F` of Jones' oriented subgroup (`\vec F ≅ F_3`, the vacuum stabilizer
of Jones' chromatic representation at `Q = 2`) carries an `F`-invariant mean. Equivalently, `1_F ≺ λ_(F/\vec F)`.

**Source of the question.** Aiello–Brothier–Conti, *Jones representations of Thompson's group F arising
from Temperley–Lieb–Jones algebras*, arXiv:1901.10597, IMRN 2021, Remark 4.7 (PDF text read 2026-09-14),
verbatim: "Even in this specific situation we do not know if 1_F is weakly contained in λ_(F/\vec F),
which is an interesting open problem."

**Why it matters.** A negative answer proves `F` nonamenable. A positive answer follows from extensive
amenability of `F ↷ D`.

## Attempts

- **Parity lamplighter (2026-09-14, ideas-wildcards).** `F/\vec F` is the transitive affine lamplighter
  `(P_f(D), ⋆)` over the dyadic rationals (`jones-subgroup-cosets-form-a-parity-lamplighter`). So this claim
  follows from `thompson-f-dyadic-action-is-extensively-amenable`, via route
  `jones-subgroup-coamenability-via-extensive-amenability`. Not decided.
- **Barriers.**
  - The dyadic Schreier graph is transient (Mishchenko, arXiv:1512.03083, nontrivial Poisson boundary), so the
    recurrence criterion for extensive amenability does not apply.
  - `\vec F` contains no `F_[c,1]` or `F_[0,c]`, so `thompson-f-end-rigid-schreier-graphs-are-amenable` gives
    nothing here.
