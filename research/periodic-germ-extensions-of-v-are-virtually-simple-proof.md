---
rg: 2
id: periodic-germ-extensions-of-v-are-virtually-simple-proof
kind: route
title: Check the Belk--Hyde--Matucci hypotheses for Z wr S_l germs at periodic points, compute the germ abelianization, and square away the finite abelianization by diagonal transplanting
target: periodic-germ-extensions-of-v-are-virtually-simple
requires:
  - germ-complex-and-bux-gonzalez-morse-inputs
  - thompson-v-finitely-presented-infinite-simple
---

**Source.** Belk--Hyde--Matucci (BHM), arXiv:2407.03149v1, `main.tex`, 151092 bytes. It was read on
2026-09-18 from the scratch copy of lane `gq-typeA-design`, whose SHA-256 is recorded in
`germ-complex-and-bux-gonzalez-morse-inputs-citation`. Quoted labels:
- `thm:MainFinitenessTheorem` (l.194–200);
- `thm:Simplicity` (l.221) and its refinement `thm:SimplicityRefined` (l.775);
- `thm:ActualVersion` (l.628–642), with `prop:DefinitionSigmap` (l.668);
- `prop:NormalClosuresEqual` (l.792);
- Appendix A, `thm:Stabilizers` (l.1281).

Notation is as in the claim. Write `ℓ = ℓ_v`.

**1. `G_Π` is a group containing `V`.**
- **Every `V`-germ between points of `Ω_Π` is admissible with `π = id`.** Near `p = uv^∞` an element
  of `V` is one prefix replacement `uv^K ζ ↦ wζ`. If it sends `p` to `q = u'v^∞`, then
  `wv^∞ = u'v^∞`. Since `v` is primitive, this gives `w = u'v^L` for some `L ∈ Z` (if `|w| < |u'|`, read it as `u' = wv^{-L}`). So it maps `D_{k,j}(p)` onto
  `D_{k+L-K, j}(q)`.
- **Admissible germs compose.** They compose to admissible germs:
  `(m, π)` followed by `(m', π')` is `(m'∘π + m, π'π)`, and inverses are admissible.
- **Closure.** For `g, h ∈ G_Π`, the product `gh` is a prefix replacement near every point outside
  `P_h ∪ h^{-1}(P_g)`. There its germ is a composite of admissible or `V`-germs. Tail classes are
  preserved throughout.
- So `G_Π` is closed under products and inverses, and `V ≤ G_Π`.

**2. Finite germ extension of `V` (BHM's definition, `germ-complex-and-bux-gonzalez-morse-inputs`
(FGE)).**
- **(1)** `sing(g) ⊆ P_g` is finite.
- **(2)** An element with no singular point is a prefix replacement near every point. By
  compactness it lies in `V`.
- **(3) Localization.** Let `p ∈ sing(g)`. Choose `K` so large that `g` acts on `C_{uv^K}` by its
  admissible rule and `C_{uv^K}` meets `P_g` only in `p`.
  - Put `h = g` on `C_{uv^K}`.
  - The complements of `C_{uv^K}` and of `g(C_{uv^K})` are nonempty clopen sets. Any two nonempty
    clopen subsets of `C` are homeomorphic by a prefix-replacement map, so `h` can be completed on
    the complement.
  - Then `sing(h) = {p}` and `h = g` near `p`.
- **The singular set.** The same construction realizes every admissible `(m, π)` at `p` with
  `q = p`. For `ℓ >= 2` some of these germs are not `V`-germs. So `sing(G_Π) = Ω_Π`.
- **Orbits.** Prefix replacements and admissible germs preserve tail equivalence. `V` acts
  transitively on each tail class (as in step 5). So `G_Π` and `V` have the same orbits.

**3. Germ groups.**
- By step 2, `(G_Π)_p` is the group of all admissible germs fixing `p`, which is `Z^ℓ ⋊ S_ℓ`. By
  step 1, `(V)_p = {(m,…,m; id)}`, which is central.
- The quotient is `(Z^ℓ/diag) ⋊ S_ℓ`. It is virtually free abelian of finite rank, hence of type
  `F_∞`.

**4. Abelianization of the germ groups.**
- `(Z^ℓ ⋊ S_ℓ)^{ab} = (Z^ℓ)_{S_ℓ} × S_ℓ^{ab} = Z × Z/2` for `ℓ >= 2`. The coinvariants are given
  by the coordinate sum, since `[σ, e_i] = e_{σ(i)} - e_i`.
- The diagonal generator maps to `(ℓ, 0)`.
- So `A_p(G_Π) = coker((V)_p^{ab} → (G_Π)_p^{ab}) = Z/ℓ ⊕ Z/2`.
- For `p ∉ Ω_Π`, `(G_Π)_p = (V)_p` and `A_p = 0`.

**5. Finiteness (`thm:MainFinitenessTheorem`).**
- **(1)** `V` has type `F_∞`. `Stab_V(M)` has type `F_∞` for every finite set `M` of eventually
  periodic points, by BHM Appendix A, `thm:Stabilizers` ("rational" means eventually periodic,
  l.1279).
- **(2) Oligomorphic.** Let `x_1..x_n` be distinct and `y_1..y_n` distinct, with each `x_i` tail
  equivalent to `y_i`.
  - Write `x_i = a_i z_i` and `y_i = b_i z_i`. Lengthen the prefixes until the cones `C_{a_i}` are
    disjoint and the cones `C_{b_i}` are disjoint.
  - Map `C_{a_i}` onto `C_{b_i}` by prefix replacement, and match the nonempty clopen complements.
  - So a `V`-orbit on `Ω_Π^n` is determined by the equality pattern and the tail class of each
    coordinate. There are finitely many. BHM l.591 states this as well known.
- **(3)** `(V)_p ⊴ (G_Π)_p`, with quotient of type `F_∞`, by step 3.
- So `G_Π` has type `F_∞`.

**6. Simplicity (`thm:Simplicity`).**
- `V` is simple (`thompson-v-finitely-presented-infinite-simple`).
- `V` is locally moving: every cone supports a nontrivial prefix-replacement map.
- `V` has no global fixed point.
- `V` and `G_Π` have the same orbits, by step 2.
- So `G_Π'` is simple, and every proper quotient of `G_Π` is abelian.

**7. Abelianization (`thm:ActualVersion`).**
- There is an epimorphism `σ = (σ_p)_{p∈R}: G_Π → ⊕_{p∈R} A_p(G_Π)` with `ker σ = G_Π' V`. Here `R`
  is a set of representatives of the tail classes.
- `V ≤ G_Π'` by `prop:NormalClosuresEqual`, since `V` is simple and locally moving. So
  `ker σ = G_Π'`.
- With step 4, `G_Π/G_Π' ≅ ⊕_{v∈Π} (Z/ℓ_v ⊕ Z/2)`.
- So `G_Π'` has finite index. It has type `F_∞` because `G_Π` does, and it is simple by step 6.

**8. The diagonal embedding.**
- **Transplants.** For a cone `c` and `g ∈ G_Π`, let `g^{(c)}` be `cξ ↦ c·g(ξ)` on `C_c`, and the
  identity elsewhere.
  - Its exceptional points are the points `c·x` for `x ∈ P_g`. They have the same tails, and the
    germs there are conjugates of the germs of `g` by the local prefix map `ξ ↦ cξ`. This map sends
    side cones of `x` to side cones of `cx`, with the same word `v` and the same index `j`.
  - Near every other point `g^{(c)}` is a prefix replacement, since `C_c` is clopen.
  - So `g^{(c)} ∈ G_Π`, and `g ↦ g^{(c)}` is an injective homomorphism.
- **`σ` does not see transplanting.** BHM define `σ_p(g) = Σ_q [b_{g(q)}^{-1} g b_q]_p`, where the
  `b_q ∈ V` satisfy `b_q(p) = q` (`prop:DefinitionSigmap`). Take `x ∈ sing(g)`, and let `β, β' ∈ V`
  agree near `x` and near `g(x)` with the prefix map by `c`. Then near `cx`,
  `g^{(c)} = β' g β^{-1}`, and
  `[b_{cgx}^{-1} β' g β^{-1} b_{cx}]_p = [b_{cgx}^{-1}β' b_{gx}]_p + [b_{gx}^{-1} g b_x]_p + [b_x^{-1}β^{-1} b_{cx}]_p`.
  The outer two terms are germs of elements of `V` fixing `p`, and these vanish in `A_p`. So
  `σ(g^{(c)}) = σ(g)`.
- **The embedding.** Let `c_1, …, c_E` be disjoint cones. Then `Δ(g) = ∏_i g^{(c_i)}` is a product
  of commuting transplants, so `Δ` is an injective homomorphism. Its image satisfies
  `σ(Δ(g)) = Eσ(g) = 0`, because `E` kills `⊕(Z/ℓ_v ⊕ Z/2)`. So `Δ(G_Π) ≤ ker σ = G_Π'`.

So every subgroup of `G_Π` embeds in the finitely presented simple group `G_Π'`. ∎
