---
rg: 2
id: stw01-modular-single-pair-via-universal-order-pair
kind: route
title: Pull a quasitrace on C*(PSL_2(Z)) back along the universal order-pair map
target: stw01-modular-single-pair-quasitrace-additivity
requires:
  - stw01-universal-order-pair-quasitrace-additivity
---

In `Q = C^3 * C^2`, the pair `h = e_1 p e_1`, `k = e_1 p e_2 p e_1` satisfies
`0 <= h <= 1` and `0 <= k <= h - h^2`, because `h - h^2 = k + e_1 p e_3 p e_1`. The
universal property of `U` gives a unital *-homomorphism `phi : U -> Q` with
`h_0 -> h` and `k_0 -> k`.

Let `sigma` be a bounded 2-quasitrace on `Q`. Then `sigma o phi` is a bounded 2-quasitrace on
`U`: composing with a *-homomorphism preserves `x^* x ~ x x^*`, additivity on commuting
positive elements, homogeneity, the 2-amplification and boundedness. By the required claim,

```text
sigma(h + k) = (sigma o phi)(h_0 + k_0) = (sigma o phi)(h_0) + (sigma o phi)(k_0) = sigma(h) + sigma(k).
```

Only the existence of `phi` is used. Its injectivity
(`stw01-modular-test-pair-algebra-is-universal-order-pair`) is not needed. Details:
Section 2 of `research/artifacts/stw01-universal-order-pair-test-2026-09-12.md`.
