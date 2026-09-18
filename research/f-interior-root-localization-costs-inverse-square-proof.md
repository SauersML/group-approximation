---
rg: 2
id: f-interior-root-localization-costs-inverse-square-proof
kind: route
title: Proof that interior-root localized switch-walk gaps control the dyadic gap at inverse-square cost
target: f-interior-root-localization-costs-inverse-square
requires: [f-dyadic-endpoint-switch-walk-gaps-are-inverse-square, thompson-f-amenable-iff-dyadic-action-extensively-amenable]
---

Notation is as in the target. Points of `[0,1]` are binary sequences. `[p]` is the closed cylinder
`[0.p, 0.p + 2^{−|p|}]`. The generators act by prefix substitution:

- `x_0`: `0w → 00w`, `10w → 01w`, `11w → 1w`;
- `x_0^{−1}`: `00w → 0w`, `01w → 10w`, `1w → 11w`;
- `x_1`: `0w → 0w`, `1u → 1·x_0(u)`;
- `x_1^{−1}`: `0w → 0w`, `1u → 1·x_0^{−1}(u)`.

These agree with the piecewise-linear maps (`x_0 = t/2, t − 1/4, 2t − 1` on `[0,1/2], [1/2,3/4], [3/4,1]`;
`x_1 = id` on `[0,1/2]` and `1/2 + x_0(2t−1)/2` on `[1/2,1]`). The check is `check()` in
`experiments/f-interior-root-transfer-2026-09-17/dyadic_depth_distance.py`, which is exact on all dyadics
of depth `≤ 7`. The identification is also elementary by hand.

## Step 1. Prefix reading

Each generator reads at most 3 leading letters and changes their number by at most 1. So for a generator
`s` and a string `p` with `|p| ≥ 3` there is `q = s_*(p)` with `||q| − |p|| ≤ 1` and `s(0.pw) = 0.qw` for
all `w`.

**Claim.** Let `g = s_ℓ ⋯ s_1` and `|p| ≥ ℓ + 2`. Then there is `q` with `||q| − |p|| ≤ ℓ` and
`g(0.pw) = 0.qw` for all `w`.

*Proof.* Put `q_0 = p` and `q_i = (s_i)_*(q_{i−1})`. By induction `|q_i| ≥ |p| − i ≥ ℓ + 2 − i`, which is
`≥ 3` for `i ≤ ℓ − 1`. So each step `i ≤ ℓ` is legitimate, and `q = q_ℓ`. ∎

Consequently `g` maps `[p]` affinely onto `[q]` with slope `2^{|p|−|q|}`.

## Step 2. Short words cannot tell `ξ` from `y`

Let `N = 2R + 8`. Let `p` be the first `N` digits of the unique binary expansion of `ξ`, and put
`y = 0.p1`. Since `ξ ∉ D`, `ξ` lies in the interior of `[p]`, and so does `y`.

**Claim.** For `|g| ≤ N − 2`, the following are equivalent: `g ∈ F^0_ξ`; `g|_{[p]} = id`; `g ∈ F_y`.

*Proof.* By Step 1, `g(0.pw) = 0.qw` for all `w`.
- **First equivalence.** `[p]` is a neighbourhood of `ξ` and `g` is affine on it. So `g` is the identity
  near `ξ` exactly when `g|_{[p]} = id`, that is, when `q = p`.
- **Second equivalence.** `g(y) = 0.q1`. Distinct finite strings ending in `1` represent distinct dyadics.
  So `g(y) = y` exactly when `q = p`. ∎

**Ball map.** Define `ψ(w·o) = w·y` for words with `|w| ≤ R + 2`.
- *Well defined and injective.* Suppose `|w|, |w'| ≤ R+2`. Then `|w^{−1}w'| ≤ 2R + 4 = N − 4`, and by the
  Claim `w^{−1}w' ∈ F^0_ξ ⟺ w^{−1}w' ∈ F_y`. So `w·o = w'·o ⟺ w·y = w'·y`.
- *Onto.* By definition `ψ` is onto `B_{R+2}(y)`. Also `ψ(B_r(ξ)) = B_r(y)` for every `r ≤ R+2`.
- *Equivariant.* If `v = w·o` with `|w| ≤ R+1` and `s` is a generator, then `ψ(s·v) = (sw)·y = s·ψ(v)`.
- *Root.* `ψ(o) = y`.

On finite sets `A ⊆ B_{R+2}(ξ)`, `ψ` acts by images. It satisfies `ψ(A Δ {o}) = ψ(A) Δ {y}`, and
`ψ(s·A) = s·ψ(A)` whenever `A ⊆ B_{R+1}(ξ)`.

## Step 3. Localized test functions transfer without loss

Let `f ≠ 0` be supported on configurations `A ⊆ B_R(ξ)`. Put `f' = f∘ψ^{−1}` on configurations inside
`B_R(y)`, and `f' = 0` elsewhere. Then `‖f'‖ = ‖f‖`.

- **Which terms matter.** Fix a triple `(a,s,b)` and write `u = δ^a s δ^b`. A term `|f(u·A) − f(A)|²` is
  nonzero only if `A ⊆ B_R(ξ)` or `u·A ⊆ B_R(ξ)`.
- **Both sets lie in the ball.** Toggling at `o` keeps a set inside `B_r(ξ)` for `r ≥ 0`, and a generator
  moves `B_R` into `B_{R+1}`. So in the first case `u·A ⊆ B_{R+1}(ξ)`. In the second case the same holds
  for `A = u^{−1}·(u·A)`, because `u^{−1} = δ^b s^{−1} δ^a` is also a triple.
- **Terms match.** In both cases every set occurring lies in `B_{R+1}(ξ)`, and `u` applies `s` only to
  points of `B_{R+1}(ξ)`. By Step 2, `ψ(u·A) = u'·ψ(A)`, where `u' = δ_y^a s δ_y^b`.
- **Values match.** For a set `C ⊆ B_{R+1}(ξ)`, `ψ(C) ⊆ B_R(y)` holds exactly when `C ⊆ B_R(ξ)`. So
  `f'(ψ(C)) = f(C)`, including the case where both sides are `0`.
- **Same for `f'`.** The same analysis at `y`, using `ψ^{−1}`, shows that every nonzero term of `E_y(f')`
  comes from such a pair.

So `ψ` is a bijection between the nonzero terms of `E_ξ(f)` and those of `E_y(f')`, and it preserves each
term. Hence `E_y(f') = E_ξ(f)`, and taking the infimum over `f` gives

    gap(y) ≤ κ_ξ(R).

## Step 4. Depth reduction

**Claim.** Let `z = 0.r ∈ D`, where `r` ends in `1` and `|r| = k ≥ 2`. Then some word of length `≤ 3` maps
`z` to a dyadic of depth `< k`. Hence `d(z, 1/2) ≤ 3(k − 1)`.

*Proof.*
- **Depths `2 ≤ k ≤ 12`.** Exhaustive search: field `direct` of
  `experiments/f-interior-root-transfer-2026-09-17/depth_reduction.json`.
- **Depths `k ≥ 6`.** Write `r = uv` with `|u| = 5`, so that `v` ends in `1`. The check records a witness
  word `g_u` with `|g_u| ≤ 3` for the depth-6 point `0.u1`, together with its prefix image `q_u`, and
  asserts `|q_u| < 5` for all 32 strings `u` (field `prefix_reduction`).
- **Why the witness works for every `v`.** Since `|u| = 5 ≥ |g_u| + 2`, Step 1 gives
  `g_u(0.uv) = 0.q_u v`. This string ends in `1` and has length `|q_u| + |v| < k`.
- **Distance bound.** Iterate: at most `k − 1` reductions reach depth 1, and the only dyadic of depth 1
  is `1/2`. ∎

For `y = 0.p1` of depth `N + 1 = 2R + 9`, this gives `d(y, 1/2) ≤ 6R + 24`.

## Step 5. Conclusion

Let `g` be a word with `g·y = 1/2` and `|g| = d ≤ 6R + 24`. Lemma (3a) of
`f-dyadic-endpoint-switch-walk-gaps-are-inverse-square-proof` gives `gap(1/2) ≤ 20(4d+3)² gap(y)`. Since
`4d + 3 ≤ 24R + 99`, Step 3 yields `gap(1/2) ≤ 20(24R+99)² κ_ξ(R)`. ∎

**Consequences.**
- **(a) Sufficient criterion.** Suppose `R_j² κ_ξ(R_j) → 0` along some sequence `R_j → ∞`. Then
  `gap(1/2) = 0`. By Step 1 of `f-dyadic-endpoint-switch-walk-gaps-are-inverse-square-proof`, `F ↷ D` is
  extensively amenable. By `thompson-f-amenable-iff-dyadic-action-extensively-amenable`, `F` is amenable.
- **(b) Uniform lower bound.** If `F` is not amenable, the same citations give `gap(1/2) > 0`, and the
  theorem rearranges to the stated bound.
- **(c) Converse.** Suppose `F` is amenable.
  - `L_ξ` is an extension of a locally finite abelian group by `F`, so it is amenable, and its action on
    `P_f(X_ξ)` has Følner sets.
  - Indicators of those sets are almost invariant under the finitely many `u = δ^a s δ^b`. So
    `inf_f E_ξ(f)/‖f‖² = 0`.
  - Every finitely supported `f` is supported inside some ball, so `κ_ξ(R)` decreases to `0`.
- **(d) Chabauty roots.** Let `y_j → ξ` with `ξ ∉ D`.
  - `F_{y_j} → F^0_ξ` in Chabauty topology. If `g` is the identity near `ξ`, then `g` eventually fixes
    `y_j`.
  - Conversely, suppose `g` fixes infinitely many `y_j`. Breakpoints are dyadic, so `g` is affine near `ξ`.
    Its fixed points there are then not isolated, so `g` is the identity near `ξ`.
  - Step 2 is the quantitative form of this, with the explicit sequence `y_N = 0.p_N 1`.
