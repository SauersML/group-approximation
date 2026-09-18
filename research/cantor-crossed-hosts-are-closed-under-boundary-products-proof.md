---
rg: 2
id: cantor-crossed-hosts-are-closed-under-boundary-products-proof
kind: route
title: Coordinatewise actions give a tensor factorization, central simple tensor simple is simple, and Wegner closes FJCw under products
target: cantor-crossed-hosts-are-closed-under-boundary-products
requires:
  - boundary-crossed-product-is-a-leavitt-path-algebra
  - boundary-crossed-product-carries-leavitt-family
artifacts:
  - research/artifacts/cantor-crossed-host-boundary-products-2026-09-17.md
  - research/artifacts/fjc-crossed-product-leavitt-hosts-2026-09-16.md
---

Complete proof in Section 1 of the artifact; the imports are in Section 2.

1. **Tensor factorization.** Locally constant functions on a compact product are finite sums of
   clopen-rectangle indicators, so `LC(X × W) ≅ LC(X) ⊗ LC(W)`. The action is coordinatewise, so
   `(f ⊗ f')(g, h) |-> f g ⊗ f' h` is a unital algebra isomorphism.
2. **Finite presentation.** `L_∂ ≅ L_k(E_d)`, a Leavitt path algebra of a finite graph, is finitely
   presented. A tensor product of finitely presented algebras is presented by the union of the
   generators and relations plus the commutators between the two generating sets.
3. **Simplicity.** A central simple algebra tensor a simple algebra is simple, by minimal tensor
   rank:
   - normalize the first coefficient to `1` using simplicity of `B`;
   - commutators with `B ⊗ 1` force the other coefficients into `Z(B) = k`;
   - simplicity of `C` finishes.

   `L_∂` is simple by the reviewed Abrams–Aranda Pino import in
   `boundary-crossed-product-is-a-leavitt-path-algebra`.
4. **Centre.** `Z(A ⊗ C) = Z(A) ⊗ Z(C)`. `Z(L_∂) = k` by Lemma 6.3 of
   `fjc-crossed-product-leavitt-hosts-2026-09-16`: the boundary action is minimal and topologically
   free, since each `g != e` fixes two points.
5. **The group.**
   - A product of torsion-free groups is torsion-free.
   - `F_d` is a CAT(0)-group. Wegner, arXiv:1308.2432, Example ex-FJCw-1(1), verbatim: "Since the
     class of CAT(0)-groups is closed under finite wreath products, we conclude … that
     CAT(0)-groups satisfy FJCw."
   - Proposition prop-FJCw-1, verbatim: "Direct products: If $G_1$ and $G_2$ satisfy FJCw, then
     the direct product $G_1 \times G_2$ satisfies FJCw."
6. **No rank model.** `boundary-crossed-product-carries-leavitt-family` gives `t_i s_j = δ_ij` and
   `Σ s_i t_i = 1` in `1 ⊗ L_∂`. Rank ultraproducts are directly finite, because
   `rk(I − AB) = rk(I − BA)`.
   - A unital `φ` would give `φ(s_1 t_1) = 1`, then `φ(s_2 t_2) = 0`.
   - Then `1 = φ(t_2 (s_2 t_2) s_2) = 0`.
