---
rg: 2
id: top-determined-register-rings-cannot-divide-the-unit
kind: claim
title: A one-register-per-type completion whose harmonic equations eventually determine every top level injectively cannot make an infinite-order unit class divisible by every n, singular top matrix or not
distinct_from:
  dilation-letters-cannot-divide-the-unit-class: that assumes the same-level or top matrix is invertible; this replaces invertibility by injectivity of the stacked top blocks, which covers the singular case for every one-type design and for the loop-plus-dilation examples.
  single-register-rings-divide-unit-at-finitely-many-primes: that covers shift and reset letters through generic freeness; this is a level-recursion argument for all affine letters.
artifacts:
  - research/artifacts/gq-gq-k2-q-dilation.md
---

**ESTABLISHED (2026-09-18)** through `top-determined-register-rings-cannot-divide-the-unit-proof`. Lane proof
(gq-k2-q), elementary, not independently reviewed. As in `dilation-letters-cannot-divide-the-unit-class`, it is an
implication from hypothesis (P) of `resolvent-register-units-give-rational-symbols`.

## Setting

A register completion with:
- finitely many types `τ`, one register `N >= 0` each;
- letters `x` from type `s(x)` to type `t(x)` with affine substitutions `φ_x(n) = p_x n + r_x` (`p_x >= 1`), or
  resets;
- availability eventually constant.

The *harmonic equation* at the point `(σ, k)` is
`h(σ, k) = Σ_(x : s(x) = σ, k ∈ φ_x(N)) h(t(x), φ_x^(-1)(k)) + (tail terms)`. Its *top level* is the largest level
at which the equation, after cancelling the left side against loops, has a nonzero coefficient.

**Top determination (TD).** For all large `j`, stack the equations whose top level is `j` and keep only their
level-`j` coefficients. The resulting integer matrix `M_j` (rows are those equations, columns are the types) is
injective.

## Statement

1. Under (TD), every harmonic functional on `K_0(R)` is determined by its values at finitely many low levels and
   on the tail classes. It takes values in `Z[1/D]` for one `D`. So, by part 1 of
   `dilation-letters-cannot-divide-the-unit-class`, an infinite-order `[1]` is divisible by only finitely many
   primes.
2. **Every one-type design with at least one non-loop letter satisfies (TD)**, whether or not its top matrix is
   singular. In particular this holds for exactly one loop plus downward dilations.
   - The coefficient of each equation on its top level is a positive letter multiplicity, or `1 − a ≠ 0` when the
     number of loops `a` is not `1`.
   - Every large level is the top of some equation.
3. The nonsingular case of `dilation-letters-cannot-divide-the-unit-class` is the special case in which `M_j`
   contains the invertible same-level (or top) block.

## Attempts

1. **What is left (open).** Multi-type designs in which some direction of type space is, for infinitely many
   levels, never determined by an equation having that level as top. Such directions are genuine free parameters.
   - An escape would need their consistency conditions to divide an older free parameter by integers of unbounded
     prime support.
   - In every tested case the consistency conditions have bounded coefficients and collapse instead (artifact §7).

## Scope of hypothesis (P)

`register-completion-pimsner-from-supercoherence` (lane `gq-ring-fp-simple`, 3542cca5d; re-review by `gq-referee-a`
and `gq-referee-b` pending) proves (P) for single-register completions with a *spine*: each type is the range of
a letter available on every target.
- In that setting the statement above holds without assuming (P), provided the coefficient ring contains every point indicator `δ_n`, i.e. `⊕_N Q ⊆ B⁺` at each type (scope amendment db70a3dbb, from `gq-referee-b` 852a0771f). The `B⁺` described here, finitely supported functions plus tails, includes them.
- The hypotheses match: one register per type; shift, dilation and reset letters; `B⁺` the eventually rational
  coefficient ring.
- Designs without a spine still need (P) as a hypothesis.
