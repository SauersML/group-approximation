---
rg: 2
id: full-group-units-embed-in-steinberg-algebras-proof
kind: route
title: Indicator functions of bisections multiply as the bisections do, and the unit space is the identity
target: full-group-units-embed-in-steinberg-algebras
requires: []
---

`A_R(G)` is the `R`-span of the indicator functions `1_U` of compact open
bisections `U`, with convolution `(f*g)(gamma) = sum_{alpha beta = gamma} f(alpha) g(beta)`.
This definition, due to Steinberg, needs no Hausdorff hypothesis.

1. **Products of bisections.** For compact open bisections `U, V`, the product
   `UV = {alpha beta : alpha in U, beta in V, s(alpha) = r(beta)}` is a compact
   open bisection.
   - If `gamma in UV`, the factorization `gamma = alpha beta` with `alpha in U`
     and `beta in V` is unique: `beta` is the arrow of `V` with source
     `s(gamma)`, and then `alpha = gamma beta^-1`.
   - If `gamma not in UV`, there is no such factorization.

   So `1_U * 1_V = 1_(UV)`.
2. **Identity.** `G^(0)` is a compact open bisection because `G` is étale and
   `G^(0)` is compact. `1_(G^(0))` is the unit of `A_R(G)`: for a bisection `U`,
   `1_(G^(0)) * 1_U = 1_(r(U) U) = 1_U`, and similarly on the right. Linearity
   extends this to all of `A_R(G)`.
3. **Inverses.** For full `U`, `U U^-1 = r(U) = G^(0)` and
   `U^-1 U = s(U) = G^(0)`. So `1_U * 1_(U^-1) = 1_(U^-1) * 1_U = 1_(G^(0))`, and
   `1_U` is a unit.
4. **Homomorphism.** By step 1, `U |-> 1_U` respects products, hence it is a
   group homomorphism `[[G]] -> A_R(G)^x`.
5. **Injectivity.** If `U != U'` as subsets of `G`, then `1_U` and `1_U'` differ
   at some arrow, because `R != 0`.
