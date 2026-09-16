---
rg: 2
id: parity-clean-arc-counts-see-only-burau-mod-t-plus-one
kind: claim
title: "If Burau of a braid is the identity mod t+1, parity-clean arcs before and after it cross alpha equally often"
distinct_from:
  moody-polynomial-change-certifies-burau-nonkernel: that claim is Moody's criterion over Z[t^{±1}] (a change of the whole polynomial certifies non-membership in ker ρ_n); this claim is the t = −1 analogue together with the parity lemma, and it limits what parity-clean intersection counts can certify
  brunnian-four-braids-admit-parity-correcting-push: that claim asserts that parity-clean arcs with unequal counts exist for every nontrivial Brunnian 4-braid; this claim forbids them whenever the braid is in ker ρ̄
artifacts:
  - research/artifacts/zp-burau-parity-t-minus-one-obstruction-2026-09-16.md
---

**Setting.** Let `n ≥ 3`.
- `D_n` is the disk with marked points `p_1, ..., p_n` on a diameter.
- `α` is the arc from `p_1` to `p_2`, and `β_*^3` is the arc from a boundary point `p_*` to `p_3`.
- `ρ_n` is the unreduced Burau representation, and `ρ̄_n = ρ_n mod (t+1)`.

**Parity condition.** Let `A` be an arc from `p_*` to a marked point, transverse to `α`.
- The crossings `q_1, ..., q_m` with `α` are taken in order along `A`, with signs `ε_i`.
- `Δ_i` is the disk bounded by `A[q_i, q_{i+1}] ∪ α[q_i, q_{i+1}]`.
- `Δ_i` is sign-changing iff `ε_{i+1} = −ε_i`.
- `A` satisfies the parity condition iff each `Δ_i` is sign-changing exactly when it contains an
  odd number of marked points. This is the condition of arXiv:2607.05283, Lemma 4.2.

**Claim.**
1. **Parity lemma.** `A` satisfies the parity condition iff `|𝕄(α, A)(−1)| = |A ∩ α|`, where
   `𝕄` is the Moody polynomial (equivariant algebraic intersection of lifts).
2. **Counts are blind to `ker ρ̄_n`.** Suppose `Ψ ∈ B_n` has `ρ_n(Ψ) ≡ I mod (t+1)`, and
   `Γ ∈ B_n`. Any transverse representatives of `(β_*^3)ΨΓ` and `(β_*^3)Γ` that both satisfy the
   parity condition cross `α` the same number of times.

Contrapositive: a parity-clean pair with unequal counts certifies `ρ̄_n(Ψ) ≠ I`, which is strictly
more than `Ψ ∉ ker ρ_n`.

Route: `parity-clean-arc-counts-see-only-burau-mod-t-plus-one-proof`.
