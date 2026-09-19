---
rg: 2
id: grigorchuk-tip-subshift-is-not-of-finite-type
kind: claim
title: The Schreier-tip subshift of the Grigorchuk group is not of finite type, and no SFT containing it keeps the tip isolated, because the finite-level Schreier graphs give periodic two-tip configurations locally indistinguishable from the tip; residual finiteness of the tree action is the obstruction to finite-type branch seeds
distinct_from:
  grigorchuk-schreier-tip-seeds-a-non-free-orbit: that builds the tip seed and leaves its finite type open; this proves it is not of finite type, and that no SFT containing the tip subshift keeps the tip isolated.
  grigorchuk-type-vertex-groups-fail-ss-hard-at-the-emitter: that finds that Grigorchuk's finitely presented envelope sits at an infinite emitter; this finds that the natural seed which could blow up a parabolic emitter is not of finite type. Both come from the level structure of the tree action.
---

**ESTABLISHED** (lane proof, bh-e3prime, 2026-09-18; elementary; not reviewed).

## Setting

- `G = ⟨a, b, c, d⟩` is the first Grigorchuk group acting on the binary tree, with `ξ = 1^∞` and
  `P = Stab_G(ξ)`.
- `λ(η)` is the set of generators fixing `η ∈ ∂T_2`, and `λ_n(w)` the same for a level-`n` vertex
  `w`.
- `x_η(g) = λ(g^(-1) η)`, `Y = \overline{G x_ξ}`, and `Q` is the pattern "label `{b, c, d}` at `1`".
  So `[Q] ∩ Y = {x_ξ}` (`grigorchuk-schreier-tip-seeds-a-non-free-orbit`, item 3).
- For a level-`n` vertex `v`, put `x_v(g) = λ_n(g^(-1) v)`. This configuration is fixed by the
  finite-index subgroup `St_G(v)`.

## Statement

1. **Periodic obstruction (any group).** If `x` is isolated in an SFT `X` with `[P] ∩ X = {x}`, and
   the orbit of `x` is infinite, then `P` occurs in no configuration of `X` with finite orbit.
2. **Two-tip look-alikes.** For every `r` and every `n` with `2^n − 1 > 2r`, every `r`-ball pattern
   of `x_(1^n)` occurs in `Y`. But `x_(1^n) ∉ Y`: its occurrences of `Q` contain the finite-index
   subgroup `St_G(1^n)`, while in `Y` they form the empty set or a single coset of the infinite-index
   subgroup `P`.
3. **Not of finite type.** `Y` is not an SFT over `G`.
4. **No finite-type repair.** Let `X ⊇ Y` be any SFT, with window radius `r_0`. Then `x_(1^n) ∈ X` for
   all `n > log_2(2 r_0 + 1)`. These configurations have finite orbits, lie in `[Q]`, and converge to
   `x_ξ`. So `x_ξ` is not isolated in `X`, and the tip seed has no finite-type version.

## Proof

**Item 1.** A finite-orbit `z ∈ X` containing `P` at `h` has `h^(-1) z ∈ [P] ∩ X = {x}`. So `x` would
have finite orbit, a contradiction.

**Facts used.**
- (F1) The level-`n` Schreier graph `Γ_n` (generators `a, b, c, d`) is a path with `2^n` vertices,
  whose ends are the tips `1^n` and `1^(n−1)0`. These are the only level-`n` vertices fixed by all of
  `b, c, d`, since `b, c, d ∈ St_G(1)`, and a vertex `1^k 0 y` with `k <= n−2` is fixed by exactly one
  of them. So the tips are at Schreier distance `2^n − 1`.
- (F2) A word of length `ℓ` moves a vertex by Schreier distance at most `ℓ`.
- (F3) If `g` fixes `1^n` and `|g| < 2^(n+1) − 1`, then `g ∈ P`. Indeed, by (F1) at level `n + 1`,
  `g` cannot swap `1^(n+1)` and `1^n 0`, which are at distance `2^(n+1) − 1`. So `g` fixes `1^(n+1)`,
  and iterating gives that `g` fixes every `1^m`, hence `ξ`.
- (F4) Flipping the last letter, `β_n(w'x) = w'(1 − x)`, commutes with every tree automorphism on
  level `n`. So `λ_n ∘ β_n = λ_n`, and `β_n` swaps the two tips.
- (F5) For a non-tip `w` at level `n` and any tail `ζ`, `λ(wζ) = λ_n(w)`: whether `s ∈ {b, c, d}`
  fixes `1^k 0 …` depends only on `k`. Also `x_η ∈ Y` for every `η ∉ Gξ`: `Gξ` is dense, and
  `η ↦ x_η(g)` is continuous at every `η` with `g^(-1) η ≠ ξ`.

**Item 2.** Let `g ∈ G` and `u = g^(-1) 1^n`. The pattern of `x_(1^n)` on `g B_r` is
`(λ_n(w^(-1) u))_(w ∈ B_r)`. By (F2) every `w^(-1) u` is within distance `r` of `u`.
- **Far from both tips.** No `w^(-1) u` is a tip. Pick `ζ` with `uζ ∉ Gξ` and put `η' = uζ`. Since
  `w^(-1) η'` has level-`n` prefix `w^(-1) u`, (F5) makes the pattern equal to that of `x_(η')` at
  `1`, and `x_(η') ∈ Y`.
- **Near the tip `1^n`.** Write `u = h 1^n` with `|h| <= r`, and put `η' = hξ`, so `x_(η') = h x_ξ ∈ Y`.
  - If `w^(-1) u` is not a tip (the far tip is out of reach, since `2^n − 1 > 2r`), then (F5) gives
    `λ(w^(-1) η') = λ_n(w^(-1) u)`.
  - If `w^(-1) u = 1^n`, then `w^(-1) h` fixes `1^n` and has length `<= 2r < 2^(n+1) − 1`. So
    `w^(-1) h ∈ P` by (F3), `w^(-1) η' = ξ`, and both labels are `{b, c, d}`.
- **Near the tip `1^(n−1)0`.** Write `u = β_n(u')` with `u'` near `1^n`. By (F4),
  `λ_n(w^(-1) u) = λ_n(β_n(w^(-1) u')) = λ_n(w^(-1) u')`. So the pattern equals one already handled.
- **Not in `Y`.** `x_(1^n)` has `Q` at every `g ∈ St_G(1^n)`. By the one-defect lemma, the occurrences
  of `Q` in a configuration of `Y` are empty or one coset `hP`. A coset of the infinite-index `P`
  (the orbit `Gξ` is infinite) contains no coset of a finite-index subgroup.

**Item 3.** If `Y` were an SFT of window radius `r_0`, it would contain every configuration whose
`r_0`-patterns occur in `Y`, including `x_(1^n)` for large `n`. This contradicts item 2.

**Item 4.**
- `x_(1^n) ∈ X` by item 2, since `X` is determined by `r_0`-patterns and contains `Y`.
- The configurations `x_(1^n)` have `Q` at `1` and finite orbits.
- For `r < (2^n − 1)/2`, their `r`-patterns at `1` equal those of `x_ξ` (the near-tip case with
  `h = 1`), so they converge to `x_ξ`.
- By item 1, `x_ξ` is not isolated in `X`.

## Comparison with the emitter finding, and E3′ on branch inputs

- **The two findings agree.**
  - `grigorchuk-type-vertex-groups-fail-ss-hard-at-the-emitter` found that finite presentation of the
    branch data (Lysionok's HNN extension) lands the group at an infinite emitter.
  - This node finds that the natural seed which could blow up a parabolic emitter, the Schreier tip,
    cannot be made finite type.
  - Both come from the profinite level structure of the tree action. The substitution image has
    infinite index because it is the graph of a map to the finite level-3 quotient `D_8`. And the
    tip's finite-level approximants `x_(1^n)` are periodic look-alikes that every SFT must admit.
- **Consequence for E3′ on branch inputs.** A finite-type (Li or SFT) host carries an input through
  seeds with no periodic look-alikes (item 1). The seeds that branch structure supplies are
  approximated by finite-level configurations, because branch groups are residually finite through
  their tree. So:
  - branch inputs cannot enter E3′ hosts through their tree structure;
  - a finite-type seed for them must be non-profinite, for instance metric (Cannon cones, open for
    `G`), or come from a structure other than the tree.

## Lesson for general BH

**Finite type forbids periodic look-alikes, and branch structure is made of them.**
- An isolated point of an SFT can never be imitated by a configuration with finite orbit. That is
  the one-line obstruction behind every failed seed.
- Branch groups pin points through their tree, and the tree is a limit of finite levels. So every
  branch seed has periodic approximants. The Grigorchuk tip is imitated by the finite Schreier paths,
  whose two ends look exactly like the tip.

This is the same mechanism that sent Grigorchuk's finitely presented envelope to an infinite emitter.
So branch inputs are closed to finite-type seeds built from their tree. Finite type needs seeds that
residual finiteness cannot approximate.
