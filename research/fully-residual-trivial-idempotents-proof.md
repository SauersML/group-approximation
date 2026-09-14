---
rg: 2
id: fully-residual-trivial-idempotents-proof
kind: route
title: Push an idempotent to a quotient that is injective on its support together with the identity
target: fully-residual-limits-preserve-trivial-idempotents
requires: []
---

Let `e` in `K[G]` be idempotent, `S = supp(e) ∪ {1}`, and choose `N` as in the
claim. The quotient map `pi: K[G] -> K[G/N]` is a ring homomorphism, so
`pi(e)` is idempotent, hence `pi(e)` is `0` or `1` because `G/N` is in `C_K`.

Because `pi` is injective on `S`, no two elements of `S` collide. So for each
`s` in `S`, the coefficient of `pi(e)` at `sN` equals the coefficient of `e`
at `s`.
- If `pi(e) = 0`, all coefficients of `e` on `S` vanish, so `e = 0`.
- If `pi(e) = 1`, then `pi(e - 1) = 0`. Since `supp(e - 1) ⊆ S`, the same
  coefficient comparison gives `e - 1 = 0`.

So `e` is `0` or `1`.
