---
rg: 2
id: sft-connected-differences-iff-flexible-sets-stay-close-proof
kind: route
title: Glue two independent changes across a gap wider than the window, and cut a split difference set back into two changes
target: sft-connected-differences-iff-flexible-sets-stay-close
requires: []
---

The notation is that of the target. The one fact about SFTs used is this: `z ∈ A^Λ` lies in `X`
iff each window pattern `z|pB_r` is the window pattern `w|pB_r` of some `w ∈ X`.

**Window lemma.** If `d(U_1, U_2) > 2r`, no window `pB_r` meets both `U_1` and `U_2`.
*Proof.* Points `q ∈ U_1 ∩ pB_r` and `q' ∈ U_2 ∩ pB_r` would have `d(q, q') <= 2r`. `∎`

## Part 2 (gluing)

Let `y_i ∈ X`, `y_i ≠ x`, agree with `x` off `U_i`, for `i = 1, 2`, with `d(U_1, U_2) > m >= 2r`.
Define `z = y_1` on `U_1`, `z = y_2` on `U_2`, and `z = x` elsewhere.
- Take a window `W = pB_r`. By the window lemma it misses `U_1` or `U_2`, say `U_2`.
- On `W ∩ U_1` we have `z = y_1`. On `W \ U_1` we have `z = x = y_1`, because `y_1 = x` off `U_1`.
  So `z|W = y_1|W` is allowed. The case where `W` misses `U_1` is symmetric, with `y_2`.
- Hence `z ∈ X`, and `Δ(x, z) = Δ(x, y_1) ⊔ Δ(x, y_2)` with `D_i = Δ(x, y_i) ⊆ U_i` nonempty. `∎`

## Part 1 (characterization)

*If.* Suppose `Δ(x, z) = D_1 ⊔ D_2` with both parts nonempty and `d(D_1, D_2) > m`. Put
`y_1 = z` on `D_1` and `y_1 = x` elsewhere.
- A window `W` misses `D_1` or `D_2` by the window lemma, since `m >= 2r`.
- If `W` misses `D_2`, then `y_1|W = z|W`, because `z = x` off `D_1 ⊔ D_2`.
- If `W` misses `D_1`, then `y_1|W = x|W`.
- So `y_1 ∈ X`. It differs from `x` exactly on `D_1`, so `x` is flexible on `D_1`. Likewise
  `x` is flexible on `D_2`, and `d(D_1, D_2) > m`.

*Only if.* If `x` is flexible on `U_1` and `U_2` with `d(U_1, U_2) > m`, part 2 gives
`Δ(x, z) = D_1 ⊔ D_2` with `d(D_1, D_2) >= d(U_1, U_2) > m`. That set is not `m`-connected. `∎`

## Part 3 (products)

Let `(x, x')` be an `n`-half-space pair of `X`: `x = x'` on `{⟨p, n⟩ >= 0}`, so
`Δ(x, x') ⊆ {⟨p, n⟩ < 0}` and it is nonempty. Let `(y, y')` be a `(-n)`-half-space pair of `Y`:
`Δ(y, y') ⊆ {⟨p, n⟩ > 0}`, nonempty. Fix `m`.
- Pick `v ∈ Z^d` with `⟨v, n⟩ > (m + 1) |n|_2`. Then `D_2 = Δ(v.y, v.y')` is `Δ(y, y')` translated
  by `v`, up to the sign convention for the action. Replacing `v` by `-v` if needed,
  `D_2 ⊆ {⟨p, n⟩ > (m + 1)|n|_2}`.
- Put `D_1 = Δ(x, x')`. For `p ∈ D_1` and `q ∈ D_2`, `⟨q - p, n⟩ > (m + 1)|n|_2`. So
  `|q - p|_1 >= |q - p|_2 > m + 1`. In the standard word metric on `Z^d`, `d(D_1, D_2) > m`.
- The pair `((x, v.y), (x', v.y'))` in `X × Y` has difference set `D_1 ∪ D_2`. Two parts at
  distance `> m` give no `m`-connectivity. `∎`

**The reversal corollary (`d = 2`).** Let `X` be infinite.
- If `X` already has a difference set that is not `m`-connected for every `m`, then so does
  `X × X^rev`: take `((x, w), (y, w))`.
- Otherwise every difference set of `X` is `m_0`-connected, and `2r <= m_0` may be assumed.
  - Boyle--Lind give a line `ℓ = n^⊥` that is nonexpansive. So for every `t` there are
    `x_t ≠ y_t` in `X` agreeing on the strip `{|⟨p, n⟩| <= t}`, with `|n|_2 = 1`.
  - For `t > m_0`, part 1 forbids differences on both sides of the strip. So `x_t = y_t` on
    `{⟨p, σ_t n⟩ >= -t}` for a sign `σ_t`.
  - Translating, `X` has a `(σ n)`-half-space pair for some `σ = ±1`.
- Reversal `p ↦ -p` turns a `(σ n)`-half-space pair of `X` into a `(-σ n)`-half-space pair of
  `X^rev`. Part 3 applies. `∎`
