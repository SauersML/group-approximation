---
rg: 2
id: fpbs-removal-descendants-of-gapped-sets-proof
kind: route
title: Scaffold a typical level set of the walk by dyadic halving and remove it layer by layer
target: fpbs-removal-descendants-of-gapped-sets
requires:
  - fpbs-random-walk-shannon-and-avez-bounds
  - kesten-amenable-stabilizer-uniform-gap
  - fpbs-spectral-margin-survives-product-generator-moves
---

**Notation.** `d = |S|`, and `mu` is uniform on `S`. For finite `F ⊆ Gamma`
write `A_F = sum_{g ∈ F} R(g)`, where `R(g) f(x) = f(xg)`. Then
`rho = ||sum_g mu(g) R(g)|| < 1` (Kesten, `kesten-amenable-stabilizer-uniform-gap`;
right and left regular representations are unitarily equivalent through
`f -> f(x^{-1})`). Since `mu` is symmetric, this operator is self-adjoint, so

```text
|| sum_g mu^{*n}(g) R(g) || = rho^n .                                   (P1)
```

`h > 0` is the Avez entropy (`fpbs-random-walk-shannon-and-avez-bounds`, item 3),
`X_n = xi_1 ... xi_n`, and `pi_n(eta)` is as in item 2 there.

**Two operator facts.**

- (D) If `0 <= c(g) <= c'(g)` pointwise, with finite support, then
  `||sum c(g) R(g)|| <= ||sum c'(g) R(g)||`. Both are convolution operators
  with nonnegative kernels, and `|<Kf,f'>| <= <K'|f|,|f'|>`.
- (M) `m(F) >= 1 + |F| - 2||A_F||` for every finite symmetric generating `F`
  with `e ∉ F`. This is item 4 of
  `fpbs-spectral-margin-survives-product-generator-moves`.

By (D) and (P1), if `F ∌ e` and `mu^{*n} >= tau` on `F`, then

```text
||A_F|| <= rho^n / tau .                                                 (P2)
```

The same bound holds with `F \ {e}` in place of `F` whenever `mu^{*n} >= tau`
on `F`. Also `||A_{F ∪ F'}|| <= ||A_F|| + ||A_{F'}||` by (D) and the triangle
inequality.

**Parameters.** Fix `eta ∈ (0, h/10)`. Let `r >= 2`, `k = 2^r`, and let `r` be
large, depending on `S`, `eta` and `K`.

1. **Scaffold.** Put `W_0 = S`. For `1 <= l <= r-1` put

```text
tau_l = rho^{2^l} e^{-(h-2 eta) k},
W_l   = { g ∈ W_{l-1} W_{l-1} : mu^{*2^l}(g) >= tau_l } .
```

   By induction each `W_l` is finite and symmetric, since
   `mu^{*n}(g^{-1}) = mu^{*n}(g)`. It may contain `e`. By (P2),

```text
||A_{W_l \ {e}}|| <= e^{(h-2 eta) k} .                                   (S1)
```

2. **Defects.** Let `D_l = P(X_{2^l} ∉ W_l)` and
   `eps_l = P(mu^{*2^l}(X_{2^l}) < tau_l)`. Then `D_0 = 0`. Write
   `X_{2^l} = X_{2^{l-1}} Y`, where `Y = xi_{2^{l-1}+1} ... xi_{2^l}` also has
   law `mu^{*2^{l-1}}`. If `X_{2^{l-1}} ∈ W_{l-1}`, `Y ∈ W_{l-1}` and
   `mu^{*2^l}(X_{2^l}) >= tau_l`, then `X_{2^l} ∈ W_l`. A union bound gives
   `D_l <= 2 D_{l-1} + eps_l`, and so

```text
D_{r-1} <= sum_{l=1}^{r-1} 2^{r-1-l} eps_l =: E_r .                      (S2)
```

3. **Top band.** Let

```text
U = { g ∈ W_{r-1} W_{r-1} : e^{-(h+eta)k} <= mu^{*k}(g) <= e^{-(h-eta)k} } .
```

   The same splitting of `X_k` gives
   `P(X_k ∈ U) >= 1 - 2 D_{r-1} - pi_k(eta) >= 1 - 2E_r - pi_k(eta)`. Split
   `U` into bands `U_i = {g ∈ U : 2^{-i-1} < mu^{*k}(g) <= 2^{-i}}`. At most
   `J_k = 2 eta k / log 2 + 2` of them are nonempty. Choose a nonempty band
   `V = U_i` of maximal mass. Its mass is

```text
beta = P(X_k ∈ V) >= (1 - 2E_r - pi_k(eta)) / J_k .
```

   `V` is symmetric. Every `g ∈ V` has `2^{-i-1} < mu^{*k}(g) <= 2^{-i}`, so
   `|V| >= beta 2^i`. Moreover `2^{-i-1} < e^{-(h-eta)k}` gives
   `2^i > e^{(h-eta)k}/2`, and (P2) with `tau = 2^{-i-1}` gives
   `||A_{V \ {e}}|| <= 2^{i+1} rho^k`. Hence

```text
|V| >= beta e^{(h-eta)k} / 2,     ||A_{V \ {e}}|| / |V| <= 2 rho^k / beta .   (S3)
```

4. **The set `T`.** Put `T = (S ∪ W_1 ∪ ... ∪ W_{r-1} ∪ V) \ {e}`. It is finite
   and symmetric, `e ∉ T`, and `T ⊇ S` generates `Gamma`. By (S1), (S3) and
   subadditivity,

```text
||A_T|| / |V| <= d/|V| + (r-1) e^{(h-2eta)k}/|V| + 2 rho^k/beta
              <= (2d e^{-(h-eta)k} + 2 r e^{-eta k} + 2 rho^k) / beta .
```

   Suppose `E_r -> 0` as `r -> infinity`; step 5 proves this. Also
   `pi_k(eta) -> 0` by item 2 of `fpbs-random-walk-shannon-and-avez-bounds`.
   So `beta >= 1/(2 J_k)` for large `r`, and `1/beta = O(k)`. The right-hand
   side is then `O(k (e^{-(h-eta)k} + e^{-eta k} log k + rho^k)) -> 0`, while
   `|V| >= e^{(h-eta)k}/(4 J_k) -> infinity`. By (M) and `|T| >= |V| - 1`,

```text
m(T) >= |V| (1 - 2 ||A_T||/|V|)  ->  infinity .
```

   Choosing `r` large gives `m(T) > K`. Item 1 of
   `fpbs-spectral-margin-survives-product-generator-moves` then gives
   `p_c(T) < p_u(T)`.

5. **`E_r -> 0`.** Fix `l` with `1 <= l <= r-1`. Write `n = 2^l` and
   `s = r - l ∈ [1, r-1]`, so `k = 2^s n`, `tau_l = rho^n e^{-(h-2eta) 2^s n}`,
   and the weight of `eps_l` in (S2) is `2^{s-1}`. Let `s_0 >= 1` be minimal with
   `2^{s_0 - 1}(h - 2eta) >= log d`. It depends only on `d`, `h` and `eta`.
   - (a) `s >= s_0`. `mu^{*n}` has at most `d^n` atoms, so
     `eps_l <= d^n tau_l <= exp(n log d - (h-2eta) 2^s n)`, which is at most
     `exp(-(h-2eta) k/2)`. These terms contribute at most
     `(sum_{s<r} 2^{s-1}) e^{-(h-2eta)k/2} <= k e^{-(h-2eta)k/2}`.
   - (b) `1 <= s < s_0`. Here `rho <= 1` and `s >= 1`, so
     `tau_l <= e^{-2(h-2eta)n} <= e^{-(h+eta)n}` because `h >= 5 eta`. Hence
     `eps_l <= P(-(1/n) log mu^{*n}(X_n) > h + eta) <= pi_n(eta)`, with
     `n = k/2^s >= k/2^{s_0}`. These terms contribute at most
     `s_0 2^{s_0} sup_{n >= k/2^{s_0}} pi_n(eta)`, which tends to `0` by item 2 of
     `fpbs-random-walk-shannon-and-avez-bounds`.

   So `E_r -> 0`.

6. **Remove-only chain from `T` to `S`.** Put `W_r = V`. For `1 <= l <= r` let

```text
L_l = W_l \ (S ∪ W_1 ∪ ... ∪ W_{l-1} ∪ {e}) .
```

   These sets are symmetric and pairwise disjoint, disjoint from `S`, and
   `T = S ⊔ L_1 ⊔ ... ⊔ L_r`. Remove the pairs `{t, t^{-1}}` of `L_r`, then
   those of `L_{r-1}`, and so on down to `L_1`. When a pair `{t, t^{-1}}` with
   `t ∈ L_l` is removed, the current set `C` contains
   `S ∪ L_1 ∪ ... ∪ L_{l-1} = (S ∪ W_1 ∪ ... ∪ W_{l-1}) \ {e}` together with
   `t` and `t^{-1}`. Since `t ∈ W_l ⊆ W_{l-1} W_{l-1}`, write `t = ab` with
   `a, b ∈ W_{l-1}`.
   - Neither `a` nor `b` is `e`. If `a = e`, then `t = b ∈ W_{l-1}`,
     contradicting `t ∈ L_l`; the case `b = e` is the same.
   - So `a, b ∈ C`.
   - `a, b ∉ {t, t^{-1}}`, because `t ∉ W_{l-1}` and `W_{l-1}` is symmetric.

   So each step is a Remove move of `fpbs-gap-survives-product-generator-moves`
   (`t = ab`, `a, b ∈ C \ {t, t^{-1}}`, and the result contains `S`, so it
   still generates `Gamma`). The chain ends at `S`. This proves the target.

7. **Consequence.** The Remove half of
   `fpbs-gap-survives-product-generator-moves`, applied `N` times along the
   chain of step 6 starting at the gapped `T` from step 4, gives
   `p_c(S) < p_u(S)` for an arbitrary `S`. This is
   `fpbs-benjamini-schramm-universal` for `Gamma`. The converse is immediate.

Step 4 needs only `h > 0` and `rho < 1`, both uniform in `k`. The margin is
`>= e^{(h - eta)k}/O(k)`, while the chain has length about `|T|/2`. So
`fpbs-spectral-margin-survives-product-generator-moves`, item 3 (loss 2 per
move) cannot carry the gap down the chain. That is why the claim is a
decomposition of the goal and not a proof of it.
