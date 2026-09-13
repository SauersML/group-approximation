---
rg: 2
id: higman-thompson-cantor-module-fp-via-free-root-centralisers
kind: route
title: Identify the extension with the centralizer in V_(n,|A|) of A permuting the roots freely, and import type F_infinity of centralizers of finite subgroups
target: higman-thompson-cantor-module-products-are-fp
requires: []
artifacts:
  - research/artifacts/leavitt-pbh-general-2026-09-13.md
---

Notation as in the target. Put `r = |A|` and let `X = A × C`, the Cantor space of the forest
with `r` roots labelled by `A`. `V_(n,r)` is the group of bijections of `X` given by a
bijection between two complete prefix codes of this forest, a code word being `(a, u)` with
`a ∈ A` and `u` a word over `{0, ..., n-1}`.

## Part (i): `C_(V_(n,r))(Q) ≅ M_A ⋊ V_(n,1)`

For `λ ∈ A` let `σ_λ(a, w) = (a + λ, w)`. It permutes the roots, so `σ_λ ∈ V_(n,r)`, and
`Q = {σ_λ}` is a finite subgroup isomorphic to `A`.

1. **Coordinates.** For `g ∈ V_(n,r)` write `g(0, w) = (b_g(w), ḡ(w))`. Refine the code of `g`.
   The words over the root `0` are `(0, u_i)`, and their images are `(c_i, z_i)`. Then
   `b_g = c_i` on the cone `[u_i]` and `ḡ(u_i w) = z_i w`. So `b_g ∈ M_A`, and `ḡ` is piecewise
   a prefix replacement on the partition `{[u_i]}` of `C`.
2. **Commuting elements.** If `g σ_λ = σ_λ g` for all `λ`, then
   `g(a, w) = σ_a g(0, w) = (a + b_g(w), ḡ(w))`.
3. **`ḡ ∈ V_(n,1)`.**
   - *Injective.* If `ḡ(w) = ḡ(w')`, put `a' = b_g(w) - b_g(w')`. Then
     `g(a', w') = (b_g(w), ḡ(w)) = g(0, w)`, so `w' = w`.
   - *Surjective.* Given `z`, write `(0, z) = g(a, w)`. Then `ḡ(w) = z`.
   - So `ḡ` is a bijection of `C` that maps the cones `[u_i]`, a partition of `C`, onto cones
     `[z_i]` by prefix replacement. The images partition `C`, so both `{u_i}` and `{z_i}` are
     complete prefix codes, and `ḡ ∈ V_(n,1)`.
4. **Every pair occurs.** For `(f, h) ∈ M_A × V_(n,1)` put `g(a, w) = (a + f(w), h(w))`. Refine
   a code of `h` until `f` is constant on its domain cones. Then `g` is a bijection between
   complete prefix codes of the forest, so `g ∈ V_(n,r)`, and it commutes with `Q`. With step 1,
   `Φ(g) = (b_g, ḡ)` is a bijection `C_(V_(n,r))(Q) -> M_A × V_(n,1)`.
5. **Multiplication.**
   `(g_1 g_2)(0, w) = g_1(b_2(w), ḡ_2(w)) = (b_2(w) + b_1(ḡ_2(w)), ḡ_1 ḡ_2(w))`.
6. **Isomorphism.** In `M_A ⋊ V_(n,1)`, with `(m, v)(m', v') = (m + v·m', v v')` and
   `v·m = m ∘ v^(-1)`, put `Ψ(g) = (b_g ∘ ḡ^(-1), ḡ)`. By step 5,
   `Ψ(g_1 g_2) = (b_2 ∘ ḡ_2^(-1) ∘ ḡ_1^(-1) + b_1 ∘ ḡ_1^(-1), ḡ_1 ḡ_2) = Ψ(g_1) Ψ(g_2)`, and `Ψ`
   is bijective by step 4.

For `n = 2`, `A = F_2` this is the sheet-swap computation of
`cantor-module-thompson-v-product-fp-via-mmn-centralisers`, with the two roots in place of the
cones `[0]`, `[1]`.

## Part (ii): type `F_∞`

From Martínez-Pérez–Matucci–Nucinkis, arXiv:1309.7858v2, TeX source `2014-10-01-F-infty.tex`,
fetched on MSI on 2026-09-13, quoted verbatim in the artifact:

- **Example 2.7(ii)** (l.458–464): "one can also consider $s$ colours, all of arity $n_i=n\in \N,$
  for all $1\leq i\leq s.$ Let $$\Sigma_2:=\{\alpha_i^l\alpha_j^t=\alpha_j^t\alpha_i^l\mid 1\leq i
  \not= j\leq s; 1\leq l,t\leq n \}.$$ Here $V_r(\Sigma)=sV_n$ is Brin's group of arity $n.$ It was
  shown in \cite[Example 2.9]{britaconcha} that in this case $U_r(\Sigma)$ is valid and bounded."
  For `s = 1` the set `Σ_2` is empty.
- **Remark 4.3** (l.847–849): "where the ordinary Higman-Thompson group $V_r(\Sigma)=V_{n,r}$ is
  considered, [...] Here the Cantor set is viewed as the set of right infinite words in the
  descending operations." So `s = 1` gives `V_(n,r)` acting on `X`.
- **Definition 2.14** (l.637–641): completeness is a condition "for all $i\neq i'$, $i,i' \in S$".
  For one colour there is no such pair, so it holds vacuously.
- **Corollary 4.11** (l.1029–1031): "Suppose $U_r(\Sigma)$ is valid, bounded and complete. Then
  $V_r(\Sigma)$ is of type quasi-$\F_\infty$. In particular, centralisers of finite groups are of
  type $\F_\infty$."

Apply Corollary 4.11 to `s = 1`, arity `n`, `r = |A|`, and the finite subgroup `Q`. Then
`C_(V_(n,r))(Q)` is of type `F_∞`, and part (i) transfers this to `M_A ⋊ V_(n,1)`. ∎

**Trust surface.** Validity and boundedness are imported through MMN's citation of their
[britaconcha, Example 2.9]. MMN's proofs of Theorem 3.1 and Corollary 4.11 were not re-read.
