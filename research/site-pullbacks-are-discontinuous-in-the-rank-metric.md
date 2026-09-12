---
rg: 2
id: site-pullbacks-are-discontinuous-in-the-rank-metric
kind: claim
title: The multiplicativity defect of a fixed coordinate algebra vanishes only at permutation matrices and has rank at least n minus one after a rank-one perturbation
distinct_from:
  monomial-rank-models-are-hamming-models: that shows monomial rank models are Hamming models; this shows that a fixed coordinate algebra is not preserved under rank-small perturbations of a permutation matrix.
  gromov-weiss-is-the-monomial-case-of-the-rank-implication: that proves the rank implication on monomial tuples; this is a separate statement about coordinatewise products, which gives only a heuristic reason why coordinatewise counting does not reach past permutation-like generators.
artifacts:
  - research/artifacts/linear-sofic-rung-rank-implication-2026-09-12.md
  - research/artifacts/gk-vf-positive-b-verification-2026-09-12.md
---

**ESTABLISHED** by `site-pullback-rank-discontinuity-proof`. w4-vf-positive-b re-derived it independently and
it passed (Section 4 of its verification artifact).

Let `F` be a field and `D_n = F^n` with the coordinatewise product and multiplication `m`. For `a` in `GL_n(F)`
put `E(a) = a ∘ m - m ∘ (a ⊗ a)`.
- `E(a) = 0` iff `a` is a permutation matrix.
- Let `n >= 3` with `n + 1 != 0` in `F`, and let `J` be the all-ones matrix. Then `a = I + J` is invertible with
  `rk(a - I) = 1`, and `rk E(a)` is `n - 1` in characteristic two and `n` otherwise.

**Coordinate dependence.** `E` depends on the chosen coordinate algebra, while word ranks do not. For invertible `g`
and a permutation matrix `P`, the defect of `g P g^-1` vanishes when computed in the basis `g e_i`. So the
proposition shows that no fixed coordinate algebra is stable under small rank errors.

**Heuristic reading, not a theorem.**
- **What it suggests.** Nonlinear local rules are evaluated through a coordinatewise product. They commute with a
  generator exactly when the generator preserves that coordinate algebra, and a rank-small error can destroy this
  completely. So counting configurations seems to have no rank-metric version, and a proof of
  `linear-sofic-groups-are-surjunctive` for nonlinear automata would have to linearize on the group side first, or
  find a rank-visible invariant of the rule pair.
- **What it does not say.** It does not identify the models on which counting works. The monomial Hamming models of
  `gromov-weiss-is-the-monomial-case-of-the-rank-implication` count on `F^x × {1, ..., N}`, not on the coordinates
  of `F^n`, and prove the rank implication without evaluating the rules.

## Attempts

Established; artifact Section 3, Proposition 3.1.
