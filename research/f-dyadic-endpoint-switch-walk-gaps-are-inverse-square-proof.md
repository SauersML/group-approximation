---
rg: 2
id: f-dyadic-endpoint-switch-walk-gaps-are-inverse-square-proof
kind: route
title: Confine the slope walk to a strip near 0 for the upper bound, and compare switch-walk Dirichlet forms along the conjugation by x_0^-(m-1) for the transport
target: f-dyadic-endpoint-switch-walk-gaps-are-inverse-square
requires: [affine-lamplighter-amenable-iff-extensively-amenable, thompson-f-amenable-iff-dyadic-action-extensively-amenable, f-dyadic-ea-iff-inverted-orbit-confinement]
---

Notation is as in the claim. Conventions:
- `x_0(t) = t/2` on `[0,1/2]`, and `x_1` is the identity on `[0,1/2]`, so `x_0^{−1}(t) = 2t` on `[0,1/4]`.
- The measure `ν_y` is the law of `δ_y^a s δ_y^b`, where `a, b ∈ {0,1}` are uniform and `s ~ μ`. So each of the
  20 triples `(a,s,b)` has weight `1/20`.

## Step 0. Elementary facts about `P_y`

**(0a) Self-adjointness.** `P_y f(A) = Σ_u ν_y(u) f(u·A)`. Here `ν_y` is symmetric, because the inverse of
`δ^a s δ^b` is `δ^b s^{−1} δ^a`. Each `u` permutes `P_f(D)`. So `P_y` is self-adjoint and

`E_y(f) := ⟨(I−P_y)f, f⟩ = ½ Σ_{(a,s,b)} (1/20) Σ_A |f(δ^a s δ^b·A) − f(A)|²`.

**(0b) Spectrum.** The triples `(0,e,0)` and `(1,e,1)` both give `e`. So `P_y = (1/10)I + (9/10)Q`, where `Q` is an
average of permutation operators and `‖Q‖ ≤ 1`. Hence `spec P_y ⊆ [−4/5, 1]`, and if `‖P_y‖ > 4/5` then
`‖P_y‖ = sup spec P_y`.

**(0c) Letter weights.** Every element `t ∈ T_y := {δ_y^a s δ_y^b}` has `ν_y(t) ≥ 1/20`, since it is the image of
at least one triple.

**(0d) Generation.** `T_y` contains `x_0^{±1}`, `x_1^{±1}` and `δ_y`. In `L` we have `g δ_y g^{−1} = δ_{gy}`, and
`F` is transitive on `D`. So `T_y` generates `L`.

**(0e) Return probability.** `P_y^n(∅, ∅) = E(2^{−|O_n^y|})`, where `O_n^y = {y, g_1^{−1}y, …, g_n^{−1}y}` and
`g_k = h_k⋯h_1` with `h_i` i.i.d. `~ μ`. This is item 4 of `f-dyadic-ea-iff-inverted-orbit-confinement` (JMBMdlS,
§"The inverted orbit"). Also `P_y^{2n}(∅,∅) = ‖P_y^n δ_∅‖² ≤ ‖P_y‖^{2n}`.

## Step 1. Gap zero is extensive amenability (item 3, first three bullets)

**If `gap(y) = 0`.** Take unit vectors `f` with `⟨P_y f, f⟩ ≥ 1 − η`.
- By (0a) and (0c), `‖f∘t − f‖₂² ≤ 40η` for every `t ∈ T_y`.
- Put `h = |f|²`, a probability vector. By Cauchy–Schwarz, `‖h∘t − h‖₁ ≤ ‖f∘t − f‖₂ ‖f∘t + f‖₂ ≤ 2√(40η)`.
- Let `η → 0` and take a weak* limit of the `h` as means. This gives a mean on `P_f(D)` invariant under `T_y`,
  hence under `L` by (0d).
- By `affine-lamplighter-amenable-iff-extensively-amenable`, `F ↷ D` is extensively amenable.

**Conversely, if `F ↷ D` is extensively amenable.**
- The same citation gives an `L`-invariant mean on `P_f(D)`.
- Reiter's condition gives probability vectors `h` with `‖h∘t − h‖₁ → 0` for `t ∈ T_y`.
- Put `f = √h`. Then `‖f∘t − f‖₂² ≤ ‖h∘t − h‖₁`, since `(√p − √q)² ≤ |p − q|`.
- By (0a), `⟨(I−P_y)f, f⟩ → 0`. So `gap(y) = 0`, and this holds for every `y`.

With `thompson-f-amenable-iff-dyadic-action-extensively-amenable`, amenability of `F` is equivalent to
`gap(y) = 0` for some `y`, and also for every `y`.

## Step 2. The strip strategy (item 1)

Fix `m ≥ 4` and `y = 2^{−m}`. For `h ∈ S` put:
- `σ(h) = +1` if `h = x_0` (so `h^{−1} = x_0^{−1}` doubles near 0);
- `σ(h) = −1` if `h = x_0^{−1}`;
- `σ(h) = 0` otherwise.

Put `S_k = Σ_{l≤k} σ(h_l)`.

**(2a) Linear transport.** Suppose every interval sum satisfies `Σ_{l=j}^{k} σ(h_l) ≤ m − 2` for
`1 ≤ j ≤ k ≤ n`. Then `g_k^{−1} y = 2^{S_k} y` for all `k ≤ n`.

*Proof.* Fix `k` and put `z_j = h_j^{−1} ⋯ h_k^{−1} y`, with `z_{k+1} = y`. By downward induction on `j`,
`z_{j+1} = 2^{T} y` with `T = Σ_{l=j+1}^{k} σ(h_l) ≤ m−2` (the empty sum is `0`). So `z_{j+1} ≤ 1/4`. On `[0,1/4]`:
- `x_0^{−1}` doubles;
- `x_0` halves;
- `x_1^{±1}` and `e` fix.

Hence `z_j = 2^{T+σ(h_j)} y`. At `j = 1` this is `g_k^{−1}y = 2^{S_k}y`. ∎

**(2b) The event.** Let `w = m − 2`, `a = ⌊w/2⌋`, `b = w − a`. Let `E_n` be the event `−a ≤ S_k ≤ b` for all
`k ≤ n`.
- On `E_n` every interval sum `S_k − S_{j−1}` is at most `a + b = w`. So (2a) applies, and
  `O_n^y ⊆ {2^i y : −a ≤ i ≤ b}` has at most `w+1 = m−1` points.
- By (0e), `P_y^n(∅,∅) ≥ 2^{−(m−1)} P(E_n)`.

**(2c) Killed walk.** `S` is the lazy walk with steps `±1` of probability `1/5` each and `0` of probability `3/5`.
- Its kernel `K` killed outside `I = {−a,…,b}` has the positive eigenvector `φ(i) = sin(π(i+a+1)/(w+2))`, with
  eigenvalue `θ_m = 3/5 + (2/5) cos(π/m)`.
- Since `0 < φ ≤ 1` on `I`, `P(E_n) = Σ_i K^n(0,i) ≥ Σ_i K^n(0,i) φ(i) = θ_m^n φ(0)`.
- For `w ≥ 1`, `(a+1)/(w+2) ∈ [1/3, 1/2]`, so `φ(0) ≥ √3/2`.

**(2d) Conclusion.**
- From (0e) and (2b)–(2c), `‖P_y‖^{2n} ≥ 2^{−(m−1)}(√3/2) θ_m^{2n}` for all `n`. Letting `n → ∞` gives
  `‖P_y‖ ≥ θ_m`.
- Since `1 − cos x ≤ x²/2`, `θ_m ≥ 1 − π²/(5m²)`. For `m ≥ 4` this is at least `1 − π²/80 > 4/5`.
- So by (0b), `sup spec P_y = ‖P_y‖ ≥ θ_m`, and `κ(m) ≤ 1 − θ_m ≤ π²/(5m²)`. ∎

## Step 3. Transporting the root (item 2)

**(3a) General comparison lemma.** Let `y, y' ∈ D` and `g ∈ F` with `gy = y'`, and put `d = |g|` in the
generators `x_0^{±1}, x_1^{±1}`. Then `E_{y'}(f) ≤ 20(4d+3)² E_y(f)` for every finitely supported `f`, so
`gap(y') ≤ 20(4d+3)² gap(y)`.

*Proof.*
- **Words.** Each atom `δ_{y'}^a s δ_{y'}^b` of `ν_{y'}` equals `g δ_y^a g^{−1} s g δ_y^b g^{−1}`, because
  `δ_{y'} = g δ_y g^{−1}`. This is a word `u = t_1 ⋯ t_ℓ` in `T_y` of length `ℓ ≤ 4d + 3`. We use a word of
  length `1` when `a = b = 0`.
- **Telescoping.** Write `B_i = t_{i+1} ⋯ t_ℓ·A`. Telescoping and Cauchy–Schwarz give
  `|f(uA) − f(A)|² ≤ ℓ Σ_{i=1}^{ℓ} |f(t_i B_i) − f(B_i)|²`.
- **Summing over `A`.** The map `A ↦ B_i` is a bijection of `P_f(D)`. So
  `Σ_A |f(uA) − f(A)|² ≤ ℓ Σ_i Σ_B |f(t_i B) − f(B)|²`.
- **One letter.** For `t ∈ T_y`, (0a) and (0c) give `Σ_B |f(tB) − f(B)|² ≤ 2E_y(f)/ν_y(t) ≤ 40 E_y(f)`. Hence
  `Σ_A |f(uA) − f(A)|² ≤ 40 ℓ² E_y(f)`.
- **Averaging.** Average over the 20 triples with weight `1/20` and multiply by `½`. This gives
  `E_{y'}(f) ≤ 20(4d+3)² E_y(f)`.
- **Gaps.** By the Rayleigh quotient, `gap(y) = inf_{f ≠ 0} E_y(f)/‖f‖²` over finitely supported `f`. ∎

**(3b) Item 2.** Take `y = 2^{−m}`, `y' = 1/2` and `g = x_0^{−(m−1)}`. Each of the `m−1` doublings is applied to a
point of `[0,1/4]`, so `gy = 1/2` and `d = m − 1`, and `4d + 3 = 4m − 1`. The lemma in both directions (`g` and
`g^{−1}`) gives `κ(1) ≤ 20(4m−1)² κ(m)` and `κ(m) ≤ 20(4m−1)² κ(1)`. ∎

The lemma with an arbitrary `g` also re-proves "some `y`" ⇔ "every `y`" in Step 1.

## Step 4. Items 3 and 4

**Item 3, last bullet.**
- If `liminf m² κ(m) = 0`, then item 2 gives `κ(1) ≤ 320 m² κ(m)` along a subsequence, which tends to `0`. So
  `gap(1/2) = 0`, and Step 1 applies.
- Conversely, amenability gives `κ(m) = 0` for all `m` by Step 1.

**Item 4.**
- If `F` is nonamenable, then `κ(1) > 0` by Step 1. Item 2 gives `κ(m) ≥ κ(1)/(20(4m−1)²) ≥ κ(1)/(320 m²)`, and
  item 1 gives the upper bound.
- If such a `c > 0` exists, then `liminf m² κ(m) ≥ c > 0`, so `F` is nonamenable by item 3. ∎

## Remarks

- **Rate form.** For `m ≥ 4`, `‖P_{2^{−m}}‖ = 1 − κ(m)`. Also `‖P‖ = limsup P^{2n}(∅,∅)^{1/2n}` for reversible
  irreducible chains (Woess, *Random Walks on Infinite Graphs and Groups*, §10). So item 4 says:
  - if `F` is nonamenable, the return probability `E 2^{−|O_n^{2^{−m}}|}` decays at an exponential rate of
    exact order `m^{−2}`;
  - `F` is amenable exactly when the rate is `o(m^{−2})` along a subsequence.

  This remark is not used above.
- **Exponent balance.** In Step 3, any system of words for `δ_{1/2}` in `T_{2^{−m}}` has length at least
  `2(m−2)`, since the `F`-part must carry `2^{−m}` to `1/2` and back. So the comparison loss `m²` is forced
  for path comparison. This is quantified in `f-ea-endpoint-localization-certificates-stall`.
