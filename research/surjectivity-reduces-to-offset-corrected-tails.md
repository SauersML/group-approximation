---
rg: 2
id: surjectivity-reduces-to-offset-corrected-tails
kind: claim
title: Rows with uniformly invertible own-linear parts peel away any offset, reducing surjectivity to the corrected tail
distinct_from:
  controlled-self-linear-feedback-ca-are-surjunctive: that peels rows whose offsets vanish with the earlier blocks and derives invertibility of the own-linear parts; this allows surviving offsets when the own-linear part is invertible for every value of the later blocks, moves them into a corrected tail, and gives an exact reduction rather than a class theorem.
  recipient-affine-three-factor-ca-are-surjunctive: that is the universal normal-form claim; this shows its first row peels in one step and its corrected tail is a copy of the original automaton.
  nonlinear-certificate-fibers-are-all-surjective-or-all-strict: that is the certificate-fiber dichotomy used at every step; this composes it with offset correction along a block ordering.
artifacts:
  - research/artifacts/offset-corrected-peeling-2026-09-12.md
---

**ESTABLISHED** by `surjectivity-reduces-to-offset-corrected-tails-proof`.

Let `F` be an injective cellular automaton over any group, on blocks
`X_1, ..., X_r` of tracks over a finite ring. Suppose that for each `a < r`, row `a`
of the current tail `F^(a)` has the form

    sum_s C_s(Y)(g) . X_a(g s) + beta_a(Y)(g),       Y = (X_(a+1), ..., X_r),

with local controllers and a local offset reading only later blocks, and is of
one of two types:
- **(O)** `(X_a, Y) -> (row_a, Y)` is bijective. Every own-linear part is
  invertible and the offset is arbitrary. This holds for pure shear rows
  `X_a + beta_a(Y)`, and more generally for identity plus controllers that are
  strictly upper triangular in one fixed flag.
- **(Z)** `beta_a = 0` and the constant own-linear part is bijective.

The *corrected tail* `F^(a+1)` is the later rows evaluated at the solution
`X_a*(Y)` of `row_a = 0`. That solution is `0` in case (Z).

**Theorem.** Every `F^(a)` is injective. If the last tail `F^(r)` is surjective,
then `F` is surjective. If every step is of type (O), then `F` is surjective iff
`F^(r)` is.

**Sharpness.** The recipient-affine normal form `H(x, u) = (x + u, F(x) - x - u)`
peels at `x` in one (O) step. Its corrected tail is `u -> F(-u)`, a copy of `F`.
So type-(O) steps are exact reductions, never class theorems by themselves.
Surjunctivity lives in the corrected tails.
