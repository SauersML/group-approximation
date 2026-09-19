---
rg: 2
id: abelian-finite-expanders-have-recursively-bounded-order-proof
kind: route
title: Expansion forces exponential ball growth up to half the group, abelian balls grow polynomially
target: abelian-finite-expanders-have-recursively-bounded-order
requires: []
---

We may assume `|Γ| >= 2`. Write `B(r)` for the set of products of at most `r`
elements of `T`, and `x = δ/k`.

1. **`δ <= k`.** Take `A = {1}`. Then `|A \ yA| <= 1` for each `y`, so
   `h <= k`.
2. **Growth step.** Let `A = B(r)` with `|A| <= |Γ|/2`. For `y in T`,
   `|yA \ A| = |yA| - |yA ∩ A| = |A \ yA|`, and `yA \ A ⊂ B(r+1) \ B(r)`. So
   `k |B(r+1) \ B(r)| >= Σ_(y in T) |A \ yA| >= δ |A|`, that is,
   `|B(r+1)| >= (1 + x) |B(r)|`.
3. **Exponential lower bound.** Let `r_0` be the least `r` with
   `|B(r)| > |Γ|/2`. It exists, since `B(r) = Γ` for large `r`. For `r < r_0`
   step 2 applies, so by induction from `|B(0)| = 1`,
   `|B(r_0)| >= (1 + x)^(r_0)`.
4. **Polynomial upper bound.** `Γ` is abelian, so every element of `B(r)` is
   `Σ_(t in T) n_t t` with `n_t >= 0` and `Σ n_t <= r`. Hence
   `|B(r)| <= (r + 1)^k`.
5. **Bounding `r_0`.** Steps 3 and 4 give `r_0 log(1 + x) <= k log(r_0 + 1)`.
   - Since `0 < x <= 1` by step 1, `log(1 + x) >= x log 2 >= x/2`, by concavity.
   - `log(r + 1) <= √r` for `r >= 0`: both sides vanish at `0`, and
     `1/(r+1) <= 1/(2√r)` because `2√r <= r + 1`.
   - So `r_0 x / 2 <= k √(r_0)`, that is, `r_0 <= 4k^2/x^2 = 4k^4/δ^2`.
6. **Conclusion.** By the choice of `r_0` and step 4,
   `|Γ| < 2 |B(r_0)| <= 2 (r_0 + 1)^k <= 2 (4k^4/δ^2 + 1)^k`.

For the consequence, `k = |T| <= L`, and the bound is increasing in `k`. The
remark on polynomial families replaces step 4 by `|B(r)| <= p_k(r)`; step 5
then bounds `r_0` by a computable function of `k` and `δ`. ∎
