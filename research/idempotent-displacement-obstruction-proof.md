---
rg: 2
id: idempotent-displacement-obstruction-proof
kind: route
title: Compress the identity 1 = Σ c_k σ^k by E; displacement kills every term
target: idempotent-displacement-fails-for-polynomially-small-units
requires: []
---

**Lemma.** `E = E·1·E = Σ_k c_k Eσ^kE = 0`.

**Displacement gives the zeros.**
- `E·σEσ^{-1} = 0`: multiplying by `σ` on the right gives `EσE = 0`.
- `σEσ^{-1}·E = 0`: multiplying by `σ^{-1}` on the left gives `Eσ^{-1}E = 0`.
- (C4) at `α = σ` is `σEσ^{-1} ⊥ σ^{-1}Eσ`. `σEσ^{-1}σ^{-1}Eσ = 0` gives `Eσ^{-2}E = 0`, and `σ^{-1}Eσσ Eσ^{-1} = 0` gives `Eσ^2E = 0`.

**Instances.**
- **Involutions:** `1 = σ^2`.
- **`σ = I + N`, `N = E_12 + E_23`, over `F_2`:** `N^3 = 0`, so `σ^{-1} = I + N + N^2` and `σ^2 = I + N^2`. Then `σ + σ^{-1} + σ^2 = (I+N) + (I+N+N^2) + (I+N^2) = I`.
- **Singer cycle `α ∈ GL_3(F_2)` of order 7:** `F_2[α] = F_8`, with `α^3 = α + 1` for a suitable choice. `α^{-1} = α^6` and `α^{-2} = α^5`. `α` and `α^2` are independent, and `α^5 = α^2+α+1` is not in their span. So `α, α^2, α^5` span `F_8`, which contains `1`.
- All three lie in `EL_3(F_2) = SL_3(F_2) ≤ G_X`.
- **No order-3 element of `GL_3(F_2)` satisfies `σ^2+σ+1 = 0`:** that would make `F_2^3` a vector space over `F_4`, of even dimension.
