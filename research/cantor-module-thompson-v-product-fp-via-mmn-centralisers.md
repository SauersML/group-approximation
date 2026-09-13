---
rg: 2
id: cantor-module-thompson-v-product-fp-via-mmn-centralisers
kind: route
title: Identify the extension with the centralizer of a sheet-swapping involution in V and import F_infinity of centralizers of finite subgroups
target: cantor-module-thompson-v-product-is-finitely-presented
requires: []
---

Notation as in the target. Every `g ∈ V` is a prefix replacement: there are complete
prefix codes `(u_i)`, `(v_i)` with `g(u_i w) = v_i w`.

## Part (i): `C_V(σ) ≅ M ⋊ V`

1. **Coordinates.** For `g ∈ V` and `w ∈ C` write `g(0 w) = b_g(w) ḡ(w)`, with
   `b_g(w) ∈ {0,1}` the first letter and `ḡ(w) ∈ C` the rest. Refine the codes of `g`
   to at least two words, so that no `u_i` or `v_i` is empty. For the pieces
   `u_i = 0 u_i'` inside `[0]` write `v_i = c_i z_i`. Then `g(0 u_i' w) = c_i z_i w`, so
   `b_g` is constant on each cone `[u_i']` (hence `b_g ∈ M`), and `ḡ(u_i' w) = z_i w` is
   piecewise a prefix replacement on the partition `{[u_i']}` of `C`.
2. **Commuting elements.** If `g σ = σ g`, then `g(1 w) = σ(g(0 w)) = (1 - b_g(w)) ḡ(w)`.
   So `g(c z) = (c + b_g(z)) ḡ(z)` for `c ∈ {0,1}`.
3. **`ḡ` is bijective, so `ḡ ∈ V`.**
   - Injective: if `ḡ(w) = ḡ(w')` and `b_g(w) = b_g(w')`, then `g(0w) = g(0w')`, so
     `w = w'`. If `b_g(w) ≠ b_g(w')`, then `g(0 w') = (1 - b_g(w)) ḡ(w) = g(1 w)`, so
     `0 w' = 1 w`, impossible.
   - Surjective: `0 z = g(y)` for some `y`. If `y = 0 w` then `ḡ(w) = z`; if `y = 1 w`
     then `(1 - b_g(w)) ḡ(w) = 0 z`, so again `ḡ(w) = z`.
   A bijection of `C` that is piecewise a prefix replacement on a finite partition into
   cones lies in `V`.
4. **Every pair occurs.** For `(f, h) ∈ M × V` put `g(a w) = (a + f(w)) h(w)`. Refining
   the code of `h` until `f` is constant on its pieces shows `g ∈ V`, and `g σ = σ g` by
   construction. So `Φ(g) = (b_g, ḡ)` is a bijection `C_V(σ) → M × V`.
5. **Multiplication.** By step 2,
   `(g_1 g_2)(0 w) = g_1(b_2(w) ḡ_2(w)) = (b_2(w) + b_1(ḡ_2(w))) ḡ_1 ḡ_2(w)`,
   so `Φ(g_1 g_2) = (b_2 + b_1 ∘ ḡ_2, ḡ_1 ḡ_2)`.
6. **Isomorphism.** Let `M ⋊ V` have product `(m, v)(m', v') = (m + v·m', v v')` with
   `v · m = m ∘ v^(-1)`, and put `Ψ(g) = (b_g ∘ ḡ^(-1), ḡ)`. Then
   `Ψ(g_1 g_2) = (b_2 ∘ ḡ_2^(-1) ∘ ḡ_1^(-1) + b_1 ∘ ḡ_1^(-1), ḡ_1 ḡ_2) = Ψ(g_1) Ψ(g_2)`,
   and `Ψ` is bijective by step 4. So `C_V(σ) ≅ M ⋊ V`.

This matches Martínez-Pérez–Matucci–Nucinkis Theorem 4.2 and Remark 4.3 for
`Q = ⟨σ⟩`: one orbit type (free orbits of size two), `L = Z/2`, and
`K = Map_0(C, Z/2) = M`.

## Part (ii): type `F_∞`

Martínez-Pérez–Matucci–Nucinkis, arXiv:1309.7858v2, quoted verbatim in the artifact:

- **Example 2.7(ii).** One considers "s colours, all of arity n", where "Vr(Σ) = sVn is
  Brin's group of arity n", and "It was shown in [13, Example 2.9] that in this case
  Ur(Σ) is valid and bounded." Take `s = 1`, `n = 2`, `r = 1`. Their Definition 2.1 ii)
  forms `Σ_2` as a union over pairs `1 ≤ i < i′ ≤ s`, so it is empty. The group is the
  Higman–Thompson group `V_(2,1) = V`. Their Remark 4.3 treats the ordinary
  Higman–Thompson groups `V_(n,r)` inside this framework, and Example 2.8 (Brown–Stein,
  `s = 1`, `P = ⟨2⟩`) gives validity and boundedness a second time.
- **Definition 2.14.** Completeness asks a condition "for all i ≠ i′, i, i′ ∈ S". For one
  colour there is no such pair, so the condition is vacuous. Their Remark 2.15 also
  records that the Brin-like algebras, of which this is the case `m = s = 1`, are
  complete.
- **Corollary 4.11.** "Suppose Ur(Σ) is valid, bounded and complete. Then Vr(Σ) is of type
  quasi-F∞. In particular, centralisers of finite groups are of type F∞."

Applying Corollary 4.11 to the finite subgroup `⟨σ⟩ ≤ V` gives that `C_V(σ)` is of type
`F_∞`. Type `F_∞` implies type `F_2`, which is finite presentability. With part (i),
`M ⋊ V` is finitely presented.
