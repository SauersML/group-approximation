---
rg: 2
id: cantor-crossed-product-matrix-ring-iso-forces-soe-proof
kind: route
title: Matrix ring isomorphism to unital ordered K_0 to strong orbit equivalence, through Theorem K, measure rank functions, torsion-freeness and Giordano–Putnam–Skau
target: cantor-crossed-product-matrix-ring-iso-forces-soe
requires:
  - subshift-crossed-product-k0-is-coinvariant-group
  - cantor-z-crossed-product-embeds-in-continuous-factor
  - minimal-cantor-k0-positive-iff-positive-on-all-measures
  - gps-strong-orbit-equivalence-iff-unital-ordered-k0
artifacts:
  - research/artifacts/sk-rigidity-ring-2026-09-13-part1.md
  - research/artifacts/sk-rigidity-ring-2026-09-13-part2.md
---

Full derivation in artifact part 1 §1, steps (R1)–(R6).

1. **(R1)** `ι(Σ f_n u^n) = Σ u^(−n) f_n` is an anti-automorphism of `R_Y`. For `a = f u^p` and `b = g u^q`, both
   `ι(ab)` and `ι(b)ι(a)` equal `u^(−p−q)(g∘T^(−p)) f`. Entrywise `ι` followed by transpose gives
   `M_m(R_Y)^op ≅ M_m(R_Y)`. So assume a ring isomorphism `ψ: M_m(R_X) → M_m(R_Y)`.
2. **(R2)** `ψ` gives `φ: K_0(R_X) → K_0(R_Y)` with `φ(K_0^+) = K_0^+` and `φ(m[1]) = m[1]` (Morita invariance).
3. **(R3)** `K_0(R_X) ≅ C(X,Z)/(1−T_*)C(X,Z)`, with `[χ_U] ↦ [χ_U]`
   (`subshift-crossed-product-k0-is-coinvariant-group`). The proof there uses only that `LC(X,k)` is a directed union
   of the rings `k^P` and that `K_(−1)(k) = 0`, so it applies to every field.
4. **(R4)** `K_0^+(R_X) = {[f] : f ≥ 0}`.
   - (⊇) Nonnegative functions are sums of clopen indicators, which are idempotents.
   - (⊆) For a nonzero idempotent `e` and each ergodic invariant `μ`, the faithful rank function `rk_μ`
     (`cantor-z-crossed-product-embeds-in-continuous-factor`) induces `s_μ` on `K_0` with `s_μ[χ_U] = μ(U)`. So
     `s_μ = ∫ · dμ` and `∫[e] dμ = rk_μ(e) > 0`.
   - By Bauer's maximum principle, `∫[e] dμ > 0` for every invariant `μ`.
   - By `minimal-cantor-k0-positive-iff-positive-on-all-measures`, `[e] ∈ K^0(X,T)^+`.
5. **(R5)** `K^0(X,T)` is torsion-free.
   - If `n f = g − g∘T^(−1)`, then `g mod n` is invariant, so constant `c` by minimality.
   - With `g = c + n h`, this gives `f = h − h∘T^(−1)`.
   - Then `m(φ[1] − [1]) = 0` gives `φ[1] = [1]`.
6. **(R6)** `gps-strong-orbit-equivalence-iff-unital-ordered-k0`. ∎
