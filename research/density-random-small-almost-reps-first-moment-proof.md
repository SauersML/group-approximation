---
rg: 2
id: density-random-small-almost-reps-first-moment-proof
kind: route
title: Swap the first letter to bound the chance one relator is almost satisfied, then union-bound over an operator-norm net
target: density-random-groups-no-small-nondegenerate-almost-reps
requires: []
artifacts:
  - research/artifacts/solve-nh-random-t-2026-09-13.md
---

Notation as in the target. `||·||_op` is the operator norm. For unitaries `X, Y`
and any matrix `Z`, `||ZY||_2 = ||Z||_2` and `||Z||_2 <= ||Z||_op`.

## Step 1: letter swap

Let `ℓ >= 2` and let `r` be a uniform reduced word of length `ℓ`. Write
`r = x·w` with `x ∈ A` the first letter and `w` of length `ℓ − 1`, whose first
letter is `y`. The reduced words of length `ℓ` correspond bijectively to pairs
`(w, x)` with `w` reduced of length `ℓ − 1` and `x ≠ y^{-1}`. Every `w` has
exactly `2n − 1` admissible `x`. So `r` is uniform exactly when `w` is uniform
and `x`, given `w`, is uniform over `A ∖ {y^{-1}}`.

Let `x′` be a second letter, independent of `x` given `w`, with the same
conditional law. Put `r′ = x′·w`, which is again uniform reduced of length `ℓ`.

The first letter `y` of a uniform reduced word is uniform on `A`, since the
automorphisms permuting `A` preserve the uniform measure. For letters `a ≠ b`,
the pair `(a,b)` is admissible exactly when `y^{-1} ∉ {a, b}`, which has
probability `(2n−2)/(2n)`. Hence

```text
P[(x, x′) = (a, b)] = (2n−2) / (2n (2n−1)^2) = 2 κ_n.                (S1)
```

## Step 2: one relator

**Lemma.** Let `ε′ > 0` and `V ∈ U(D)^n`, and suppose `||a(V) − b(V)||_2 > 2ε′`
for some letters `a ≠ b`. Then

```text
p(V) := P_r[ ||r(V) − I||_2 <= ε′ ] <= 1 − κ_n.
```

*Proof.* Suppose `p(V) > 1 − κ_n`. Both `r` and `r′` are uniform, so with
probability at least `2p(V) − 1 > 1 − 2κ_n`, both `r(V)` and `r′(V)` lie within
`ε′` of `I`. On that event

```text
||x(V) − x′(V)||_2 = ||(x(V) − x′(V)) w(V)||_2 = ||r(V) − r′(V)||_2 <= 2ε′,
```

because `w(V)` is unitary. But on `{(x, x′) = (a, b)}`, which has probability
`2κ_n` by (S1), `||x(V) − x′(V)||_2 > 2ε′`. So
`P[||x(V) − x′(V)||_2 <= 2ε′] <= 1 − 2κ_n`, a contradiction. ∎

## Step 3: operator-norm net

For `δ ∈ (0,1]`, take a maximal subset `N_δ ⊂ U(D)` whose points are pairwise at
operator distance `> δ`. By maximality, every `U ∈ U(D)` is within `δ` of a
point of `N_δ`. The operator-norm balls of radius `δ/2` around the points of
`N_δ` are disjoint and lie in the ball of radius `1 + δ/2` in
`M_D(C) ≅ R^{2D^2}`. Comparing volumes of norm balls,

```text
|N_δ| <= (1 + 2/δ)^{2D^2}.                                          (N1)
```

## Step 4: Lipschitz bound

If `max_i ||U_i − V_i||_op <= δ`, then for every word `r` of length `ℓ`,
telescoping over its letters gives `||r(U) − r(V)||_op <= ℓδ`. For letters,
`||a(U) − a(V)||_2 <= δ`.

## Step 5: union bound

Fix `D <= D_ℓ`. Put `δ = ε/(4ℓ)` and `ε′ = ε/2 + ℓδ = 3ε/4`. Suppose `U ∈ U(D)^n`
satisfies `||r(U) − I||_2 <= ε/2` for all `r ∈ R_ℓ`, and `||a(U) − b(U)||_2 > 2ε`
for some `a ≠ b`. Choose `V ∈ N_δ^n` with `||U_i − V_i||_op <= δ`. By Step 4,
`||r(V) − I||_2 <= ε′` for all `r ∈ R_ℓ`. Also

```text
||a(V) − b(V)||_2 >= ||a(U) − b(U)||_2 − 2δ > 2ε − ε/2 = 2ε′.
```

So the event for this `D` is contained in the union, over the `V ∈ N_δ^n` that
are `2ε′`-nondegenerate, of `{ ||r(V) − I||_2 <= ε′ for all r ∈ R_ℓ }`. The
relators are independent. By the Lemma, each such event has probability at most
`(1 − κ_n)^{N_ℓ} <= exp(−κ_n N_ℓ)`. By (N1) with `1 + 2/δ = 1 + 8ℓ/ε`, the
probability for this `D` is at most

```text
exp( 2n D^2 log(1 + 8ℓ/ε) − κ_n N_ℓ ) <= exp( −κ_n N_ℓ / 2 ),
```

since `D <= D_ℓ` gives `2n D^2 log(1 + 8ℓ/ε) <= κ_n N_ℓ / 2`.

Sum over `D = 1, …, D_ℓ`. Because `κ_n < 1` and `log(1 + 8ℓ/ε) > 1`, we have
`D_ℓ <= √N_ℓ`. So the total probability is at most
`√N_ℓ exp(−κ_n N_ℓ / 2) → 0`.

On the complementary event, every `U` as in the target has all letters pairwise
within `2ε`. Taking `a = s_i` and `b = s_i^{-1}` gives
`||U_i^2 − I||_2 = ||U_i − U_i^*||_2 <= 2ε`. ∎
