---
rg: 2
id: site-pullbacks-are-discontinuous-in-the-rank-metric
kind: claim
title: The multiplicativity defect of the coordinate algebra vanishes only at permutation matrices and jumps to full rank under a rank-one perturbation
distinct_from:
  monomial-rank-models-are-hamming-models: that shows monomial rank models are Hamming models; this shows that nonmonomial generators, even at rank distance one from a permutation, destroy the coordinatewise product through which nonlinear rules are evaluated.
  gromov-weiss-is-the-monomial-case-of-the-rank-implication: that is the rank implication on monomial tuples; this explains why coordinatewise counting does not extend past near-monomial tuples.
artifacts:
  - research/artifacts/linear-sofic-rung-rank-implication-2026-09-12.md
---

**ESTABLISHED** by `site-pullback-rank-discontinuity-proof`.

Let `F` be a field, `D_n = F^n` with the coordinatewise product and multiplication `m`, and for `a` in `GL_n(F)`
put `E(a) = a ∘ m - m ∘ (a ⊗ a)`.
- `E(a) = 0` iff `a` is a permutation matrix.
- For `n >= 3` with `n + 1 != 0` in `F`, the matrix `a = I + J` (`J` all ones) is invertible with `rk(a - I) = 1`,
  and `rk E(a)` is `n - 1` in characteristic two and `n` otherwise.

**Interpretation.** Nonlinear local rules are evaluated on a model through the coordinatewise product, and they
commute with a model operator only up to `E`. The defect is not continuous in normalized rank. So counting arguments
that run the rules on a model work on permutation-like models only, which reach sofic groups
(`gromov-weiss-is-the-monomial-case-of-the-rank-implication`). A proof of `linear-sofic-groups-are-surjunctive` for
nonlinear automata has to linearize on the group side first, or find a rank-visible invariant of the rule pair that
is not a coordinatewise evaluation.

## Attempts

Established; artifact Section 3, Proposition 3.1.
