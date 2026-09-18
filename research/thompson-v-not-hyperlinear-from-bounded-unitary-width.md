---
rg: 2
id: thompson-v-not-hyperlinear-from-bounded-unitary-width
kind: route
title: Bounded compact unitary relator width makes V not hyperlinear
target: thompson-v-not-hyperlinear
requires:
  - thompson-v-has-bounded-compact-unitary-relator-width
---

Let `1 != a in V` satisfy `a(U) in Cons_K(R(U))` for all `d` and `U`. The normalized Hilbert--Schmidt length
`l(g) = ||g - I||_2 / sqrt(d)` is

- conjugation-invariant;
- symmetric;
- subadditive, because `gh - I = g(h - I) + (g - I)`.

Applying it to the product of at most `K` conjugates gives

```text
||a(U) - I||_2 / sqrt(d)  <=  K max_(r in R) ||r(U) - I||_2 / sqrt(d)      for all d and U.
```

Suppose `V` were hyperlinear, with an injective homomorphism into a metric ultraproduct of the `U(d_m)` for normalized
Hilbert--Schmidt distance.

- Lift the images of the generators to tuples `U_m`.
- Every relator maps to the identity, so `max_R ||r(U_m) - I||_2 / sqrt(d_m) -> 0` along the ultrafilter.
- Since `a != 1`, `||a(U_m) - I||_2 / sqrt(d_m)` stays bounded below by a positive constant along the ultrafilter.

The displayed inequality forbids this, so `V` is not hyperlinear.

Together with `thompson-v-bounded-unitary-width-from-kl-violation`, this factors
`thompson-v-not-hyperlinear-from-kl-violation` through a claim that can be refuted on its own. It does not import
`kervaire-laudenbach-holds-for-hyperlinear`.
