---
rg: 2
id: dilation-letters-cannot-divide-the-unit-class
kind: claim
title: Dilation letters N -> pN + r and resolvents cannot make the unit class of a one-register-per-type completion divisible by every n, unless the top-level matrix is singular
distinct_from:
  single-register-rings-divide-unit-at-finitely-many-primes: that covers shift and reset letters through generic freeness; this covers all affine substitutions pN + r, including dilations, through a level recursion and a bounded-denominator functional.
  sl2-vacuum-hosts-admit-verma-type-modules: that is the noncommutative sl_2 loophole; this is the commutative dilation loophole.
artifacts:
  - research/artifacts/gq-gq-k2-q-dilation.md
---

**ESTABLISHED for the nonsingular case (2026-09-18)** through
`dilation-letters-cannot-divide-the-unit-class-proof`. Lane proof (gq-k2-q), elementary, not independently
reviewed. Like `single-register-rings-divide-unit-at-finitely-many-primes`, it is an implication from hypothesis
(P) of `resolvent-register-units-give-rational-symbols`. The singular case is OPEN; see Attempts.

## Setting

A register completion `R` satisfying (P), with:
- finitely many state types, each with one register `N` taking values in `{0,1,2,...}`;
- letters whose substitutions are affine, `N ↦ pN + r` with `p >= 1` and `r ∈ Z`, or constant. This includes
  dilations (`p >= 2`), shifts (`p = 1`), upward letters (`p = 1, r < 0`) and resets. Cross-type letters are
  allowed;
- availability eventually constant in `N`;
- any resolvents in the coefficient ring.

A letter with `p >= 2` sends level `k` to level `(k − r)/p < k` for large `k`, so only `p = 1` letters reach
levels `>= k`.
- Let `c >= 0` be the largest upward step.
- The *top matrix* `M_top` (types × types) is the eventual coefficient of level `k + c` in the relation
  `(1 − [X]) V_(τ,k)`: for `c >= 1` it counts the letters with step `+c`, and for `c = 0` it is `I − A_0`, with
  `A_0` the matrix of level-preserving letters.

## Statement

1. **Bounded-denominator lemma.** If `h : C -> Z[1/D] ⊆ Q` is a homomorphism with `h(x) ≠ 0`, then `x ∈ qC`
   only for the finitely many primes `q` dividing `D` or the numerator of `h(x)`.
2. **Dilation completions.** If `det M_top ≠ 0`, then every `Q`-valued harmonic functional on
   `K_0(R) = coker(1 − [X])` takes values in `Z[1/D]` for some `D`, so part 1 applies. Hence if `[1]` has
   infinite order, it is divisible by only finitely many primes.
   - Resolvents do not change this, because `K_0(B⁺)` consists of indicator classes and resolvents live in
     `K_1`.
   - Dilations do not change it either, because their targets lie strictly below the level being solved.

## Why the hoped-for mechanism fails

- Dilations do give unbounded multiplicities, `p^n` sources over one target at depth `n`. But in `K_0` that
  expresses high classes as sums of low ones, which is multiplication.
- Division needs a *new* class that is the target of a growing family at one stage, i.e. a top determinant that
  grows. With finitely many types and eventually constant availability, `M_top` is eventually constant.
- The growth in `capacity-chain-resolvent-ring-has-rational-k0` came from a growing number of states per level,
  which is two registers.
- Dilations with all residues, `x_(p,r)` for `r < p` and full availability, also give the Cuntz `Q_N` relation
  `X = pX`, so `[1]` is torsion.

## Attempts

1. **Singular top matrix (open).** This is the case `det M_top = 0`, for example one type with exactly one loop
   and only downward letters. The relations then become constraints `Σ_targets V = 0`, and the recursion does not
   apply.
   - Tested examples collapse. With one loop plus dilations by `2` and `3` (all residues), every harmonic
     functional vanishes on the points, and `X = 6X` forces `[1]` to be torsion (artifact §3).
   - No proof for the singular case in general.
2. **Register units.** Dilations force resolvents `(N + c)^(-1)` for `c ∈ Z[1/p]` into `B⁺`, since
   `σ(N + c) = p(N + (r+c)/p)`. The tail-unit lattice is then indexed by `Z[1/p]`, and the test of
   `resolvent-register-units-give-rational-symbols` must be run on it. This was not computed, because `K_0`
   already fails.

## Scope of hypothesis (P)

`register-completion-pimsner-from-supercoherence` (lane `gq-ring-fp-simple`, 3542cca5d; re-review by `gq-referee-a`
and `gq-referee-b` pending) proves (P) for single-register completions with a *spine*: each type is the range of
a letter available on every target.
- In that setting the statement above holds without assuming (P), provided the coefficient ring contains every point indicator `δ_n`, i.e. `⊕_N Q ⊆ B⁺` at each type (scope amendment db70a3dbb, from `gq-referee-b` 852a0771f). The `B⁺` described here, finitely supported functions plus tails, includes them.
- The hypotheses match: one register per type; shift, dilation and reset letters; `B⁺` the eventually rational
  coefficient ring.
- Designs without a spine still need (P) as a hypothesis.
