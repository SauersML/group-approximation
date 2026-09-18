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
- **Jones mean collapse (2026-09-17, e-f-reframer, reframing).** Established that this claim is *equivalent* to
  amenability of `F` (`jones-subgroup-coamenable-iff-thompson-f-amenable`), and to extensive amenability of
  `F ↷ D` (`jones-subgroup-coamenable-iff-dyadic-extensive-amenability`). It is not an intermediate property.
  - *Mechanism.* In the boundary model `Y ↦ ∂(Y Δ S)` of `F/\vec F ≅ F·S`, the cocycle `c(g) = ∂(gS Δ S)`
    has point character `ψ_x(g) = parity of log₂ g'(x⁻)` on `F_x`, which is nontrivial. So every invariant
    mean on `F/\vec F` puts weight `1/2` on each boundary point. The difference of two copies is an untwisted
    invariant mean on `P_f(D)` charging every point, and iterated unions give extensive amenability
    (`twisted-lamplighter-point-character-gives-extensive-amenability`,
    `dyadic-extensive-amenability-if-jones-subgroup-coamenable`). Then JMMS Corollary 1.4 on the breakpoint
    cocycle, which has trivial kernel, gives amenability of `F`.
  - *Class killed.* Any attempt to answer ABC Remark 4.7 positively without proving `F` amenable, or
    negatively without proving `F` nonamenable. In particular, lamplighter models of `F/\vec F` twisted by a
    cocycle with nontrivial point characters give no weaker certificate.
  - *Route recorded.* `thompson-f-amenable-via-jones-subgroup-coamenability`.
  - *Numerical check.* `experiments/jones-mean-collapse-2026-09-17/boundary_cocycle_check.py` verifies the
    germ formula, the cocycle identity and `c(x₀) = {1/2}`, `c(x₁) = {3/4}`.
  - *Not done.* Whether some twisted model with trivial point characters on some orbit (an orbit of a
    commensurated subset of a non-dyadic `F`-set) gives a strictly weaker certificate. That is heuristic
    only and untested.
