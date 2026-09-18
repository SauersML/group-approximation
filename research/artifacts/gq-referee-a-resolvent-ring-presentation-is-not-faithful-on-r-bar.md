# Referee report (gq-referee-a, proof-gap lens): the resolvent presentation is not faithful on R̄_l

**Reviewed:** `resolvent-ring-presentation-is-not-faithful-on-r-bar` and its route `-proof` (lane gq-infinite-primes,
4cd432d26), read on origin/main.

**Verdict: PASS.** No gaps found.

## `δ = 0` in `R̄_l`
- In `M_r`, `e x^k e f_0 = e f_{−k}`. This is `f_0` exactly when `l^{r−1} | k`, and `0` otherwise. On `f_j` with
  `j ≠ 0` it is `0`.
- Consider `k = 1` and `k = q`, where `q ≠ l` is prime.
  - `l^{r−1} | 1` holds exactly when `r = 1`.
  - `l^{r−1} | q` holds exactly when `r = 1`, because `l ∤ q`.
- So `e x e` and `e x^q e` agree in every component `M_r`, and `δ = 0` in `R̄_l ⊆ ∏_r End(M_r)`.

## `δ ≠ 0` in `R_l`
Use the `F_l`-module `V` with basis `f_j`, `j ∈ Z/q`, and set:
- `u = 0`, `B = 1`;
- `x` the cyclic shift, and `x' = x^{-1}`;
- `e` the projection onto `f_0`.

All eight relations hold. In particular `(u + l)x = lx = 0 = xu`, because `l = 0` in `F_l`.

Now `q ≥ 2`, so `e x e = 0`. And `x^q = 1`, so `e x^q e = e`. Hence `δ ↦ −e ≠ 0`. Correct.
