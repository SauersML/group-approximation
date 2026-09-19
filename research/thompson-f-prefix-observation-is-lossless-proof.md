---
rg: 2
id: thompson-f-prefix-observation-is-lossless-proof
kind: route
title: Push both laws of a shadow pair through the tail truncation; splits commute with it, so the defect of Psi is at most that of Psi composed with the truncation
target: thompson-f-prefix-observation-is-lossless
requires:
  - thompson-f-flow-certificate-observation-gate
  - thompson-f-finite-state-flows-cannot-prove-nonamenability
---

Notation as in the target. Laws are probability vectors on the countable set `M`. Pushforwards of
laws are laws.

**Step 1 (where a split acts).** Let `s = x_(i_1) ... x_(i_d)` be a normal form, with `i_1 <= ... <= i_d`,
all `i_j <= I`, and `z = s y`.
- For `q > I`, `z_q = y_(q+d)`.
- The trees `z_0, ..., z_I` depend only on `y_0, ..., y_(I+d)`.

*Proof,* by induction on `d`. The case `d = 0` is trivial.
- We have `(x_k w)_q = w_q` for `q < k`, `(x_k w)_k = w_k ∧ w_(k+1)`, and `(x_k w)_q = w_(q+1)` for `q > k`.
- Write `s = x_(i_1) s''` and `w = s'' y`. By induction, `w_q = y_(q+d−1)` for `q > I`, and `w_0, ..., w_I`
  depend only on `y_0, ..., y_(I+d−1)`.
- Since `i_1 <= I`, for `q > I` we get `z_q = w_(q+1) = y_(q+d)`.
- For `q <= I`, `z_q` depends only on `w_0, ..., w_(I+1)`. These in turn depend only on
  `y_0, ..., y_(I+d)`, because `w_(I+1) = y_(I+d)`. ∎

**Sharper index.** Let `J(s)` be the largest root of `s y` that holds a caret of `s`.
- `J(s)` does not depend on `y`, because the merge pattern is fixed. By Step 1, `J(s) <= I`.
- All `d` carets of `s` lie in roots `0..J(s)`. So those roots hold exactly `y_0, ..., y_(J(s)+d)`.
  Every later root holds one tree of `y`, in order: `z_q = y_(q+d)` for `q > J(s)`.
- For a Guba set, induction on `j` using `i_j <= m + j − 1` shows that the carets of
  `x_(i_j) ... x_(i_d)` lie in roots `<= m + j − 1`. So `J = m`, and `tail_truncation.py` confirms this.

Put `J = max_(s ∈ S) J(s)`. Then Step 1 holds with `J` in place of `I`.

**Step 2 (two facts).** Let `S` be uniform of degree `d`, `s ∈ S`, and `z ∈ M`.
- (A) `z ∈ sM` if and only if `τ_J z ∈ sM`.
- (B) If so, `split_s(τ_J z) = τ_(J+d)(split_s z)`.

*Proof.*
- Let `z = s y`. Step 1 gives `τ_J z = s(τ_(J+d) y)`: both sides agree on roots `<= J`, because those
  depend only on `y_0 .. y_(J+d)`, and both are trivial beyond `J`. This proves (B) and one direction
  of (A).
- Conversely, let `τ_J z = s y'`. By Step 1, `y'_(q+d) = (τ_J z)_q` is trivial for `q > J`.
- Let `y` agree with `y'` on positions `<= J + d`, and put `y_(q+d) = z_q` for `q > J`.
- By Step 1, `s y` agrees with `s y' = τ_J z` on roots `<= J`, and has `z_q` at every `q > J`.
  So `s y = z`. ∎

**Step 3 (the theorem).** Given laws `μ, η`, put `μ' = (τ_(J+d))_* μ` and `η' = (τ_J)_* η`. For every
`s ∈ S` and `y ∈ M`:

`ρ^(η')_s(y) = η'(s y) = Σ_(z : τ_J z = s y) η(z)`.

By (A) and (B), `{z : τ_J z = s y} = {z ∈ sM : τ_(J+d)(split_s z) = y}`. Hence
`ρ^(η')_s = (τ_(J+d))_* ρ^η_s` as measures on `M`. Therefore

`Ψ_* μ' − λ Ψ_* ρ^(η')_s = (Ψ ∘ τ_(J+d))_* μ − λ (Ψ ∘ τ_(J+d))_* ρ^η_s`

for every `s`. Summing positive parts over `s` gives

`D^Ψ_λ(μ', η') = D^(Ψ∘τ_(J+d))_λ(μ, η)`.

The left side is at least `δ_λ(Ψ)`. Taking the infimum over `(μ, η)` gives
`δ_λ(Ψ) <= δ_λ(Ψ ∘ τ_(J+d))`. ∎

Uniformity is used exactly once. The truncation of `ρ^η_s` is `τ_(J+d_s)`, and it must be the same
for all `s` for it to match the single truncation `τ_(J+d)` applied to `μ`.

**Step 4 (Corollary 1).**
- `τ_(J+d)` and `π_(J+d+1)` carry the same information, so they have the same `δ`.
- `J + d + 1 <= I + d + 1 = K`, so `π_(J+d+1)` is a coarsening of `π_K`, which is a coarsening of `id_M`.
- By Step 3 with `Ψ = id_M`, and then Lemma A.4 of the gate twice:
  `δ_λ(id_M) <= δ_λ(τ_(J+d)) = δ_λ(π_(J+d+1)) <= δ_λ(π_K) <= δ_λ(id_M)`. ∎

**Step 5 (Corollary 2).**
- *Item 1 implies non-amenability,* for any finite `S`, uniform or not. This is the argument already
  in `thompson-f-prefix-observation-shadow-defect`: Theorem A of the gate, then Lemma 2.1(a) of
  `thompson-f-finite-state-flows-cannot-prove-nonamenability-proof`.
- *Non-amenability implies item 1.* By Corollary A.3 of the gate, `δ_λ(id_M) > 0` for some `λ > 1`
  and some Guba set, which is uniform. Step 4 gives `δ_λ(π_K) > 0` for the same `S` and `λ`.
- *Item 2.* Assume `δ_1(π_K) = 0` for every finite `S`.
  - By Step 4, `δ_1(id_M) = 0` on every Guba set.
  - `D_λ` is nonincreasing in `λ`, so `δ_λ(id_M) = 0` for all `λ >= 1`.
  - Corollary A.3 then makes `F` amenable.
  - Now let `S` be any finite set with `δ_1(id_M) > 0`. Theorem A gives a rule with
    `inf out > sup in`. Rescaled, that rule is a certificate with ratio `> 1`, which Lemma 2.1(a)
    excludes. Hence `δ_1(id_M) = 0` for every finite `S`. ∎

**Step 6 (Corollaries 3 and 4).**
- *Corollary 3.* If `Ψ ∘ τ_(J+d)` is a function of `Ψ`, then A.4 gives `δ(Ψ ∘ τ_(J+d)) <= δ(Ψ)`. Step 3
  gives the reverse inequality.
- *`Ξ_(K,Q)`.* We have `Ξ_(K,Q)(τ_(J+d) y) = ((q(t_0), ..., q(t_(J+d)), ℓ, ..., ℓ), (•, •, ...))`.
  This is a function of `q_K`, and `q_K` is a function of `Ξ_(K,Q)`. So
  `δ(Ξ_(K,Q)) <= δ(Ξ_(K,Q) ∘ τ_(J+d)) <= δ(q_K) <= δ(Ξ_(K,Q))`, using Step 3 and then A.4 twice.
  Also `q_K` is a function of `π_K`, which gives `δ(q_K) <= δ(π_K)`.
- *Corollary 4.* For finite `Q`, `q_K` is a function of the profile `p(y) = (q(t_0), q(t_1), ...)` of
  `thompson-f-finite-state-flows-cannot-prove-nonamenability`. That node's Theorem is B.3 of the gate:
  `δ_1(p, N) = 0` for every finite `S`. By A.4, `δ_1(q_K) = 0`, hence `δ_1(Ξ_(K,Q)) = 0`. ∎

**Step 7 (Corollary 5).** Step 3 bounds `δ(Ψ)` by `δ(Ψ ∘ τ_(J+d))`, and `Ψ ∘ τ_(J+d)` factors through
`π_(J+d+1)`. By Theorem A of the gate, a rule reading `Ψ ∘ τ_(J+d)` is a function of the window
`(t_0, ..., t_(J+d))` alone. ∎

**Calibration.**
- *Consistency with the known kills.* Let `Ψ` read only the tail `(t_K, t_(K+1), ...)`. Then
  `Ψ ∘ τ_(J+d)` is constant, so Step 3 and B.1 of the gate give `δ_1(Ψ) = 0`. That agrees with
  Theorem C, of which `Ψ` is the case of the trivial automaton.
- *Consistency with the sharpness remark of the exact-tail node.* That remark says that for
  `S_(2,3)` the model gives total variation `15/16` for `Ξ_(K−1,Q)`.
  - Here `J + d = 2 = K − 1`.
  - `Ξ_(K−1,Q) ∘ τ_2` still reads `t_2` exactly, so it is not a function of the profile, and nothing
    here contradicts that remark.
  - For `S_(3,5)`, by contrast, `J + d + 1 = 5 < K = 6`. So Theorem C holds there with `K` replaced
    by `5`.
- *Nothing about the Ore property.* Step 3 only relocates a defect into the window. It proves no
  defect is zero, and the free-monoid calibration of the gate is untouched.
- *Where uniformity breaks.* For `S = {x_0, x_0 x_0}`, the laws `ρ^η_s` would need truncation at `J + 1`
  and at `J + 2` respectively against one truncation of `μ`, and Step 3 does not go through. No
  statement is made for such `S`.
