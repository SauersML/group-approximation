---
rg: 2
id: z2-derived-full-group-h2-criterion-proof
kind: route
title: Poincaré duality for Z^2 collapses the Li filtration to Z/2, H^1 and H^2
target: z2-derived-full-group-h2-fg-iff-mod-two-cohomology-finite
requires:
  - derived-full-group-h2-filtered-by-mod-two-groupoid-homology
  - li-derived-full-group-homology-is-k-theory-cover
artifacts:
  - research/artifacts/full-group-homology-fp-obstruction-2026-09-13.md
---

Put `G = Z^2 ⋉ X` and `F_2 = Z/2`. The artifact, Section 4, gives the same argument.

1. **Hypotheses.** `Z^2` is countably infinite of polynomial growth, and it acts freely on the
   compact metrizable totally disconnected `X`. So `G` has comparison
   (`li-derived-full-group-homology-is-k-theory-cover`, item 4).
   - `G` is minimal, because the action is.
   - `X` is a Cantor set, so it has no isolated points.
   - Hence Theorem 1 of `derived-full-group-h2-filtered-by-mod-two-groupoid-homology` applies.
     Its `D(G)` is `D([[Z^2 ~ X]])`, since `F(G) = [[Z^2 ~ X]]`.
2. **Duality.** By item 4, `H_k(G; A) ≅ H_k(Z^2; C(X, A))`.
   - The Koszul resolution `0 -> Z[Z^2] -> Z[Z^2]^2 -> Z[Z^2] -> Z -> 0` is self-dual:
     `Hom(K_j, M) ≅ K_{2-j} ⊗ M`, with the differentials matching up to sign.
   - So `H_k(Z^2; M) ≅ H^{2-k}(Z^2; M)` for every module `M`, and `H_k = 0` for `k >= 3`.
3. **Degree 2.** `H_2(G; A) ≅ H^0(Z^2; C(X, A))`, the invariant continuous functions.
   - By minimality an invariant continuous function is constant on a dense orbit, hence
     constant.
   - So `H_2(G; Z) = Z` and `H_2(G; F_2) = F_2`.
4. **The filtration.** In Theorem 1:
   - `F_0 = H^2` modulo the image of `F_2`. The `d^3` term vanishes, since `H_3(G) = 0`.
   - `F_1/F_0 = H^1`. The `d^2` term vanishes, since `H_3(G) = 0`.
   - `F_2/F_1 = ker(Z -> H_0(G; F_2))`. That is `Z` or `2Z`, hence `≅ Z`.
5. **The criterion.** `π_2 ≅ H_2(D)` is finitely generated iff `F_0` and `F_1/F_0` are finite,
   iff `H^1` and `H^2` are finite.
   - For the class obstruction, a finitely presented group has finitely generated `H_2`.
6. **The shape.** `F_1` is an extension of one `F_2`-vector space by another, so `4 F_1 = 0`.
   - `F_2/F_1 ≅ Z` is free, so the extension splits: `H_2(D) ≅ F_1 ⊕ Z`.
   - `|F_1| = |F_0| · |H^1|` and `|H^2|/2 <= |F_0| <= |H^2|`.
7. **Products.** Take `Z^2 = Z × Z` acting on `X_1 × X_2`.
   - Over the field `F_2`, `C(X_1 × X_2, F_2) = C(X_1, F_2) ⊗ C(X_2, F_2)`, since locally
     constant functions on a product of compact totally disconnected spaces are finite sums of
     products.
   - Künneth for the tensor product of resolutions gives
     `H^n = ⊕_{i+j=n} H^i(Z; C(X_1, F_2)) ⊗ H^j(Z; C(X_2, F_2))`.
   - For a Cantor minimal `Z`-system, `H^0(Z; C(X_i, F_2)) = F_2` by minimality.
     `H^1(Z; C(X_i, F_2))` is the cokernel of `1 - T` on `C(X_i, F_2)`, which is
     `K^0(X_i) ⊗ F_2`, since coinvariants commute with `⊗ F_2`.
   - The product action is free, and it is minimal: the orbit of `(x_1, x_2)` is
     `Orb(x_1) × Orb(x_2)`, which is dense. ∎
