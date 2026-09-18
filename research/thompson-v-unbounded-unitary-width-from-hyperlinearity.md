---
rg: 2
id: thompson-v-unbounded-unitary-width-from-hyperlinearity
kind: route
title: Hyperlinearity of V gives unbounded compact unitary relator width
target: thompson-v-has-unbounded-compact-unitary-relator-width
requires:
  - thompson-v-hyperlinear
---

This is the contrapositive argument of `thompson-v-not-hyperlinear-from-bounded-unitary-width`.

1. Suppose V is hyperlinear, and fix `1 != a`. Lifting an injective homomorphism into a metric ultraproduct gives tuples
   `U_m` along which every normalized Hilbert--Schmidt relator defect tends to `0` and the defect of `a` stays bounded below.
2. Fix any finite `R_0 <= R` and any `K`. For large `m`, the subadditive estimate
   `||a(U_m) - I||_2 <= K max_(r in R_0) ||r(U_m) - I||_2` fails.
3. So `a(U_m)` does not lie in `Cons_K(R_0(U_m))`, and no pair `(R_0, K)` bounds the width of `a`.
