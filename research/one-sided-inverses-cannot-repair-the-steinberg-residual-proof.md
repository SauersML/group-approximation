---
rg: 2
id: one-sided-inverses-cannot-repair-the-steinberg-residual-proof
kind: route
title: Finite quotients of St_N(T) factor through finite quotient rings, which kill I_rf and are Dedekind-finite
target: one-sided-inverses-cannot-repair-the-steinberg-residual
requires:
  - steinberg-rf-forces-ring-rf
---

**Part 1.**
- By `steinberg-rf-forces-ring-rf`, every homomorphism of `St_N(T)` onto a finite group factors through
  `St_N(F)` for a finite quotient ring `F = T/J`. Since `J` has finite index, `J ⊇ I_rf(T) ⊇ I`.
- So the finite quotients of `St_N(T)` and of `St_N(T/I)` correspond under the surjection
  `St_N(T) -> St_N(T/I)`, and `St_N(T)_rf` is the preimage of `St_N(T/I)_rf`. The isomorphism of the quotients
  follows.
- *The kernel.* `St_N(T/I)` is `St_N(T)` with the extra relations `x_ij(a) = 1` for `a ∈ I`: both have generators
  `x_ij(r)` subject to the Steinberg relations, and in the quotient `x_ij(r)` depends only on `r mod I`.
  - For `a = Σ t g_t t'`, use additivity of `x_ij`.
  - Pick `k ∉ {i, j}`, which exists since `N >= 3`. Then `x_ij(t g t') = [x_ik(t), x_kj(g t')]` and
    `x_kj(g t') = [x_ki(g), x_ij(t')]`.
  - So every `x_ij(a)` lies in the normal closure of the `x_ij(g_t)`. ∎
  - One index pair suffices (gq-referee-a): conjugation by `w_ab(1)` permutes the index pairs.

**Part 2.** Let `F` be a finite quotient ring. Left multiplication by `π̄` is injective, since `γ̄π̄ f = f`. `F` is
finite, so it is bijective, and `π̄ g = 1` for some `g`. Then `γ̄ = γ̄(π̄ g) = g`, so `π̄ γ̄ = 1`. Hence
`1 − πγ` lies in every finite-index two-sided ideal. ∎

**Part 3.**
- `x^k (1 − π_0 γ_0) x^(-k) = 1 − π_k γ_k`, so the ideal `I = (1 − π_0 γ_0)` contains every `1 − π_k γ_k`. In `T'`,
  `γ_k` is then a two-sided inverse of `π_k`.
- `I ⊆ I_rf(T)` by Part 2, so `Γ_N(T) ≅ Γ_N(T')` by Part 1.
- By Part 1, `St_N(T)_rf` is the preimage of `St_N(T')_rf` under a surjection whose kernel is the normal closure
  of the finitely many `x_ij(1 − π_0 γ_0)`. A preimage of a finitely normally generated normal subgroup under such
  a map is finitely normally generated, and so is an image. `T'` has one more relation than `T`. ∎

