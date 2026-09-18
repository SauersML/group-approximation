# Adversarial check: Mallery–Zaremsky Question 3.18 (`infinite-shift-similar-groups-need-not-be-strongly-shift-similar`) (bh-refute, 2026-09-18)

This is a self-chosen rotation item, the companion of the Q5.13 check above.

Verdict: **PASS**. Every computation was re-derived.

- **ψ_j at infinity.**
  - `s_j(i) = i+1` for `i >= j`, and `s_{g(j)}^{-1}(y) = y−1` for `y > g(j)`.
  - So `ψ_j(g)(i) = g(i+1) − 1` for large `i`.
  - Hence `(ψ_j(g))‾ = c(ḡ)`, where `c` is conjugation by the shift in the near-symmetric group, a homomorphism.
- **`c(ρ̄_k) = ρ̄_{k+1}`.** Let `x = 2^m − (k+1)`.
  - Then `ρ_k(x+1) − 1 = 2^m − k`.
  - For `x = 2^m − k`, `ρ_k(x+1) − 1 = 2^m − k − 1`.
  - So `σ^{-1}ρ_kσ` is `∏_{m>=k+2} (2^m−(k+1), 2^m−k)`. It differs from `ρ_{k+1}` only in the `m = k+2` factor.
- **Shift-similar.** `G` is the full preimage of `Γ`, and `c(Γ) = ⟨ρ̄_k : k >= 1⟩ ⊆ Γ`.
- **Not strongly shift-similar.** For `m >= K+2`:
  - the `ρ_1,…,ρ_K` preserve each window `[2^m−K, 2^m]`;
  - `2^m + 1` lies in no window, since `2^{m+1} − K > 2^m + 1`;
  - so every word in `ρ_1..ρ_K` fixes `2^m + 1` for all large `m`, while `ρ_0 = ∏(2^i, 2^i+1)` moves each of them.

  Hence `ρ̄_0 ∉ c(Γ)`.
- **Not finitely generated.** The same window argument works one index up.

**Scope.** This answers Q3.18 as printed. The finitely generated version, which is what Obs. 5.12 and the residual
case of Q5.13 need, is correctly left OPEN (`fg-infinite-shift-similar-groups-are-strongly-shift-similar`).

## Lesson for general BH

Shift-similarity is invariance of `G/FSym` under the shift endomorphism `c` of the near-symmetric group.
"Strong" means `c` is onto. Surjectivity can fail only through an infinitely generated tower
`ρ_k ↦ ρ_{k+1}`, a Hilbert-hotel phenomenon. So for finitely generated envelopes, the relevant question is
whether a finitely generated `c`-invariant subgroup of the near-symmetric group can have `c` non-surjective. That
is exactly the open node, and the Houghton-like route to BH depends on it.
