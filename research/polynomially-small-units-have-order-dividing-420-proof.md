---
rg: 2
id: polynomially-small-units-have-order-dividing-420-proof
kind: route
title: F_2[σ] has dimension at most 4, and units of finite local F_2-algebras of dimension at most 4 have exponent dividing 420
target: polynomially-small-units-have-order-dividing-420
requires: []
---

**Proof.**
- Multiplying `1 = Σ_{k∈{±1,±2}} c_kσ^k` by `σ^2` gives `Q(σ) = 0` for `Q(t) = c_2t^4 + c_1t^3 + t^2 + c_{-1}t + c_{-2} ≠ 0`, whose `t^2` coefficient is `1`. So `A = F_2[σ]` is commutative with `dim_{F_2} A ≤ 4`.
- `A = ∏ A_i` with `A_i` finite local, residue fields `F_{2^{f_i}}`, and `Σ dim A_i ≤ 4`, so `f_i ≤ 4`.
- `A_i^×` is an extension of `F_{2^{f_i}}^×`, of order in `{1,3,7,15}`, by `1+𝔪_i`. Since `𝔪_i^4 = 0` and the characteristic is 2, `(1+x)^4 = 1+x^4 = 1`.
- So the exponent of `A^×` divides `4·lcm(3,7,15) = 420`, and `σ ∈ A^×`. ∎
