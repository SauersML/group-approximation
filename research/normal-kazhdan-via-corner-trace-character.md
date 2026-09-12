---
rg: 2
id: normal-kazhdan-via-corner-trace-character
kind: route
title: Evaluate an ultralimit of corner traces at the Kazhdan projection
target: normal-kazhdan-defect-non-mf
requires: []
artifacts:
  - non_mf_groups_exist.tex
---

## Why sufficient

A third complete proof of the target, and the one now printed as
`thm:normal-kazhdan` (commit c156f3d53, after the 2026-09-05 external
review).  It replaces the finite Kazhdan set, the constant `κ`, the positive
element `b ≥ (κ²/|S|)·1`, the passage to the image `Θ(G)`, and the final
subsequence of [[normal-kazhdan-via-corona-image]] by one trace evaluation.

Let `Θ : G → U(Q_d)` be a corona homomorphism nontrivial on the normal
Kazhdan subgroup `K`, let `e_K ∈ C*_max(K)` be the Kazhdan projection, and
let `p` be its image under the homomorphism `C*_max(K) → Q_d` induced by
`Θ|_K`.  Normality of `K` makes `p` commute with `Θ(G)`, and `q = 1 − p ≠ 0`
because `Θ` is nontrivial on `K`.  The central-corner lemma
(`lem:central-corona-corner`) represents `g ↦ qΘ(g)` on the retained
coordinates by an operator-norm asymptotic representation
`W_n : G → U(r_n)`; write `π : C*_max(K) → Q_r` for the induced
homomorphism.  Since `a ↦ qΘ(a)` is a homomorphism on `C*_max(K)` agreeing
with `π` on `K`, `π(e_K)` is the coordinate restriction of `qp = 0`.

For a free ultrafilter `ω`, `T_ω([a_n]) = lim_ω tr_{r_n}(a_n)` is a tracial
state on `Q_r`, since norm-null sequences have vanishing normalized traces.
The hypothesis of the target applies to `(W_n)` itself, which is an
operator-norm asymptotic representation of `G`, and gives
`‖W_n(k) − 1‖_{2,r_n} → 0` in the normalized Hilbert–Schmidt norm of the
corner, whatever the ratio `r_n/d_n`.  Since
`|tr_{r_n}(W_n(k)) − 1| ≤ ‖W_n(k) − 1‖_{2,r_n}`, `T_ω(π(k)) = 1` for all
`k ∈ K`.  So the states `T_ω ∘ π` and the trivial character `χ_1` of `K`
agree on the canonical unitaries, whose span is dense, and therefore on all
of `C*_max(K)`.  But `χ_1(e_K) = 1`, every vector of the trivial
representation being fixed, while `π(e_K) = 0`; so `0 = T_ω(π(e_K)) = 1`.

No Kazhdan constant enters, so nothing has to be bounded below uniformly in
`n`, and no subsequence is chosen, because the ultralimit is taken once.
The step the review singled out is unchanged: the hypothesis is re-applied
to the new models `W_n` with the corner's own normalized trace, and is never
inferred from the original `d_n`-normalized estimate.

## Lean status

No carrier yet.  `Manuscript/OneSidedMFRadical/NormalKazhdanSentences.lean`
transcribes the previous printed route (Kazhdan set, `b ≥ κ²/|S|`, `s₀` on
a subsequence) and remains a sound auxiliary; the endpoint
`manuscriptNormalKazhdanRadical` states the target and is unaffected.
Tracked as issue #186.
