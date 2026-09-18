---
rg: 2
id: lifted-thompson-t-quotients-are-rotation-centralizers-proof
kind: route
title: Conjugating by the dilation x -> 2^k x identifies T-bar with the centralizer of the translation t_k, and the translation number shows that every lift of an element commuting with r_k commutes with t_k
target: lifted-thompson-t-quotients-are-rotation-centralizers
requires: []
---

**Imported fact.**
- (τ) The translation number `τ(g) = lim_n (g^n(x) − x)/n` on the group of homeomorphisms of `R`
  commuting with `z` exists and is independent of `x`. It is invariant under conjugation in that
  group, and `τ(g z^m) = τ(g) + m` (Poincaré; e.g. Navas, *Groups of circle diffeomorphisms*,
  §2.2). For a translation, `τ(t_k) = 2^{-k}`.

**Step 1. `λ^k` is an isomorphism of `T̄` onto `C_{T̄}(t_k)` with `λ^k(z) = t_k`.**
- Let `D(x) = 2^k x`, so `λ^k(g) = D^{-1} g D`.
- For `g ∈ T̄`, set `h = λ^k(g)`. Then
  `h(x + 2^{-k}) = 2^{-k} g(2^k x + 1) = 2^{-k}(g(2^k x) + 1) = h(x) + 2^{-k}`.
  So `h` commutes with `t_k`, and hence with `z = t_k^{2^k}`.
- The breakpoints of `h` are `2^{-k}` times those of `g`, so they are dyadic. There are finitely
  many mod 1, because `g` has finitely many in `[0, 2^k)`. The slopes of `h` are those of `g`. Also
  `h(Z[1/2]) = 2^{-k} g(Z[1/2]) = Z[1/2]`. So `h ∈ C_{T̄}(t_k)`.
- Conversely, let `h ∈ C_{T̄}(t_k)` and set `g = D h D^{-1}`. Then
  `g(x + 1) = 2^k h(2^{-k}x + 2^{-k}) = g(x) + 1`, and `g` is dyadic piecewise linear in the same
  way, so `g ∈ T̄` and `λ^k(g) = h`.
- `λ^k` is clearly an injective homomorphism, and `λ^k(z)(x) = 2^{-k}(2^k x + 1) = t_k(x)`.

**Step 2. `p` maps `C_{T̄}(t_k)` onto `C_T(r_k)`, with kernel `⟨z⟩`.**
- The inclusion `p(C_{T̄}(t_k)) ⊂ C_T(r_k)` is clear.
- Let `f ∈ C_T(r_k)` and let `f̃ ∈ T̄` be any lift. Then `f̃ t_k f̃^{-1}` lifts
  `f r_k f^{-1} = r_k`, so it equals `t_k z^m` for some `m ∈ Z`.
- By (τ), `2^{-k} = τ(f̃ t_k f̃^{-1}) = τ(t_k z^m) = 2^{-k} + m`, so `m = 0` and
  `f̃ ∈ C_{T̄}(t_k)`.
- The kernel is `ker p ∩ C_{T̄}(t_k) = ⟨z⟩`, since `z` is central.

**Step 3. Conclusion.**
- `ι_k = p ∘ λ^k` is onto `C_T(r_k)`, and `ι_k(z) = p(t_k) = r_k`.
- `ker ι_k = (λ^k)^{-1}(⟨z⟩) = ⟨z^{2^k}⟩`, because `λ^k(z^{2^k}) = t_k^{2^k} = z` and `λ^k` is
  injective.

**The descriptions.**
- `λ^k(t_j)(x) = 2^{-k}(2^k x + 2^{-j}) = x + 2^{-j-k}`, so `ι_k(t_j) = r_{j+k}`.
- Let `f̃` fix `Z` pointwise, lifting `f ∈ F`. For `x ∈ [j 2^{-k}, (j+1) 2^{-k}]` we have
  `2^k x − j ∈ [0, 1]` and `f̃(y) = j + f(y − j)` on `[j, j+1]`. So
  `λ^k(f̃)(x) = 2^{-k}(j + f(2^k x − j))`, which is `f` rescaled to that arc.

**The embedding.** `⋂_k ⟨z^{2^k}⟩ = 1` in the infinite cyclic group `⟨z⟩`, so the product of the
`ι_k` is injective. ∎
