---
rg: 2
id: measure-free-steinberg-el-n-reduced-cstar-not-mf
kind: claim
title: Without an invariant measure, reduced C*-algebras of elementary groups over the Steinberg algebra (and of their quotients) are separable, stably finite and not MF
distinct_from:
  no-invariant-measure-steinberg-elementary-no-mf-quotient: that is the group-level statement (no nontrivial MF quotient); this is the C*-algebra consequence for reduced and maximal algebras of every nontrivial quotient, with unique trace for the boundary-action group.
  directly-finite-subshift-el-n-reduced-cstar-is-mf: that asks for reduced MF on the measure side, where it is open; this decides the paradox side negatively.
artifacts:
  - research/artifacts/un-reduced-cstar-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).**

**Setting.** `𝒢` is ample, Hausdorff and second countable, with compact unit space `X` and no `𝒢`-invariant Borel
probability measure. `k` is a countable field, `R = A_k(𝒢)`, and `n ≥ 1` is chosen with `2n[1] ≤ n[1]` in `V(R)`,
as in `no-invariant-measure-steinberg-elementary-no-mf-quotient`.

**Theorem.** For every `N ≥ 2n` and every nontrivial quotient `Q` of `EL_N(R)` (e.g. `EL_N(R)` or `EL_N(R)/Z`):
1. `Q` is not MF, and every homomorphism from `Q` to an MF group is trivial;
2. `C*_r(Q)` is separable, stably finite and not MF;
3. `C*_max(Q)` is not MF.

**Corollaries.**
- **Boundary-action mirror.** For `S_∂ = EL_N(LC(∂F_d,k)⋊F_d)/Z` with `N ≥ 3`, `C*_r(S_∂)` is separable, stably
  finite, not MF, and has a unique tracial state (BKKO Thm 4.1, trivial amenable radical).
- **Necessity for the operator-algebra dichotomy.** If `C*_r(EL_N(R))` is MF for infinitely many `N`, then `X`
  carries a `𝒢`-invariant probability measure.

**Model tests.**
- The Cuntz groupoid (`L_k(1,2)`, `n = 1`) recovers manuscript Cor l.1038 for `N ≥ 2`.
- A minimal ℤ-subshift carries a measure, so the theorem is vacuous there, which is consistent with the open
  measure side.

Proof route: `measure-free-steinberg-el-n-reduced-cstar-not-mf-proof` (artifact §1).
