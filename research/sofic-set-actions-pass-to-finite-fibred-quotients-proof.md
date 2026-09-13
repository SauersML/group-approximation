---
rg: 2
id: sofic-set-actions-pass-to-finite-fibred-quotients-proof
kind: route
title: Replace each point of the model by the set of images of its fibre, acting on subsets of bounded size
target: sofic-set-actions-pass-to-finite-fibred-quotients
requires:
  - gkp-sofic-action-toolkit
---

# Proof

**Reductions.**
* *Orbitwise.* By `gkp-sofic-action-toolkit` (Propositions 2.15(2) and 2.16), soficity is orbitwise.
  An orbit of `X'` is the image of an orbit of `X` restricted over it, which is again sofic. So assume
  `X'` is transitive.
* *Constant fibres.* Equivariance makes all fibres of the same size `j <= k`.

**Characterization.** We use GKP Proposition 2.9, transcribed in
`research/artifacts/gkp-2401-04945-verified.md`. `G ↷ X` is sofic iff there are a free ultrafilter
`𝒰`, a homomorphism `φ : G → ∏_𝒰 (S_n, d)` and a map `π : X → 𝕏_𝒰 = ∏_𝒰 [n]` with
`φ(g)·π(x) = π(gx)` and `d_𝒰(π(x), π(y)) = 1` for `x ≠ y`. Here `d` is the normalized Hamming
distance, both on `S_n` and on `[n]`, where two points are at distance 1 or 0.

**Construction.** Fix such `(𝒰, φ, π)` for `X`, and choose representatives `φ(g) = (σ_(g,n))_n`.
* *Model set.* Let `B_n` be the set of `j`-element subsets of `[n]`, and let `σ_(g,n)` act on `B_n`
  by images, `σ'_(g,n)`.
* *The group map.* If `σ, τ ∈ S_n` agree outside a set of `δn` points, then `σ'` and `τ'` agree on
  every subset avoiding that set. The fraction of `j`-subsets meeting it is at most `jδ + O(1/n)`. So
  `φ' = (σ'_(g,n))_n` is a homomorphism `G → ∏_𝒰 (S_(B_n), d)`.
* *The point map.* For `x' ∈ X'` with fibre `{x_1, ..., x_j}`, choose representatives
  `π(x_i) = (u_(i,n))_n`. Since `d_𝒰(π(x_i), π(x_l)) = 1` for `i ≠ l`, the points `u_(1,n), ..., u_(j,n)`
  are distinct for `𝒰`-almost every `n`. Put `π'(x') = ({u_(1,n), ..., u_(j,n)})_n ∈ ∏_𝒰 B_n`.

**Checks.**
* *Equivariance.* `φ'(g)·π'(x') = ({σ_(g,n)u_(i,n)})_n`, which is almost everywhere
  `({u'_(i,n)})_n`, where `u'_(i,n)` represents `π(gx_i)`. The `gx_i` are exactly the fibre of
  `gx'`, so `φ'(g)·π'(x') = π'(gx')` in `∏_𝒰 B_n`.
* *Separation.* For `x' ≠ y'` the fibres are disjoint, and all `2j` points have pairwise distance
  1 under `π`. So for almost every `n` the two `j`-subsets are disjoint, hence different, and
  `d_𝒰(π'(x'), π'(y')) = 1`.
* *Conclusion.* By Proposition 2.9, `G ↷ X'` is sofic. For the coset statement take
  `p : G/H → G/K`, whose fibres have `[K : H]` points.

∎
