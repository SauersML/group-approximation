---
rg: 2
id: z2-crossed-product-steinberg-kernel-is-nonzero-proof
kind: route
title: Detect the torus commutator by a Hochschild cocycle, lifted through the splitting of central extensions of St_n
target: z2-crossed-product-steinberg-kernel-is-nonzero
requires: [steinberg-group-homology-gives-k2-and-k3]
artifacts:
  - research/artifacts/z2-crossed-product-steinberg-kernel-nonzero-2026-09-16.md
---

The artifact gives the full proof, with exact random checks in
`experiments/z2-crossed-product-steinberg-kernel-2026-09-16/`.

1. **Hochschild chains.** `[g_1|...|g_k] -> (g_1...g_k)^(-1) ⊗ g_1 ⊗ ... ⊗ g_k`, followed by the
   matrix trace, is a chain map from the bar complex of `GL_n(R)` to the Hochschild complex of `R`.
2. **Group chains with coefficients.** On the part of total degree `0`, the map
   `x_0⊗...⊗x_k -> (x_0...x_k)[deg x_1|...|deg x_k]` is a chain map to a bar complex of `Z^2` with
   coefficients in `A`. Commutativity of `A` is used here.
3. **The cocycle.** `N(g,h) = P_1(h_1) t_2^(h_2) P_2(g_2)` is a `Z[Z^2]`-valued 2-cocycle, as the cup
   product of quantum-integer 1-cocycles. So `tau = N~∘psi` vanishes on Hochschild boundaries, and
   `f(g,h) = tau(tr((gh)^(-1)⊗g⊗h))` is a normalized `A`-valued 2-cocycle on `GL_n(R)`.
4. **The value.** `f(D_1,D_2) - f(D_2,D_1) = -1`, computed from `eps N(g,h) = h_1 g_2`.
5. **Lifting.** Pull `f` back to `St_n(R)`. For `n >= 5` the central extension splits
   (`steinberg-group-homology-gives-k2-and-k3` (ii), Weibel III Prop. 5.5.1). The splitting gives
   `sigma` with `sigma(xy) = sigma(x) + sigma(y) + f(pi x, pi y)`, so
   `sigma([x,y]) = f(D_1,D_2) - f(D_2,D_1) = -1`.
6. **Small and stable rank.** Ranks `3` and `4` follow by stabilizing to rank `5`, and the stable
   statement follows by passing to the colimit.
