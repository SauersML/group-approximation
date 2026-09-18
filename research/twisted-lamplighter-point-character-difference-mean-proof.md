---
rg: 2
id: twisted-lamplighter-point-character-difference-mean-proof
kind: route
title: A nontrivial point character halves every point mass, the difference of two twisted means is untwisted, and iterated unions give full weight
target: twisted-lamplighter-point-character-gives-extensive-amenability
requires: []
---

Notation as in the claim. A mean on a set `Y` is a finitely additive probability measure on all subsets of
`Y`, equivalently a positive unital linear form on `ℓ^∞(Y)`. Invariance of a mean `m` under an action means
`m(gU) = m(U)`, equivalently `m(φ∘g) = m(φ)` with `(φ∘g)(y) = φ(gy)`.

**Iterated means.** For means `m₁` on `Y₁`, `m₂` on `Y₂` and a bounded `Φ` on `Y₁ × Y₂`, set
`∫∫ Φ dm₁dm₂ = m₁(y₁ ↦ m₂(y₂ ↦ Φ(y₁,y₂)))`. This is a positive unital linear form on `ℓ^∞(Y₁×Y₂)`. If `G`
acts on both sets and both means are invariant, then `∫∫ Φ(gy₁, gy₂) = ∫∫ Φ(y₁,y₂)`. Indeed the inner
integral `y₁ ↦ m₂(y₂ ↦ Φ(gy₁, gy₂)) = m₂(y₂ ↦ Φ(gy₁, y₂)) =: Ψ(gy₁)` by invariance of `m₂`, and then
`m₁(Ψ∘g) = m₁(Ψ)`.

**0. The point character.** For `g, h ∈ G_x`,
`c(gh)(x) = c(g)(x) + c(h)(g⁻¹x) = c(g)(x) + c(h)(x)`. Conjugation invariance: from the cocycle identity,
`c(k⁻¹) = −k⁻¹·c(k)` and `c(kgk⁻¹) = c(k) + k·c(g) − (kgk⁻¹)·c(k)`. Evaluating at `kx`, and using
`(kgk⁻¹)⁻¹kx = kx`, gives `c(k)(kx) + c(g)(x) − c(k)(kx) = ψ_x(g)`. The action `⋆` is an action:
`g⋆(h⋆f) = gh·f + g·c(h) + c(g) = (gh)⋆f`.

Let `m` be a `⋆`-invariant mean on `A^(X)`.

**1. Every point value is spread.** Fix `x ∈ X` and `a ∈ A`, and let `U_a = {f : f(x) = a}`. Choose
`g ∈ G_x` with `λ = ψ_x(g) ≠ 0`. Then `(g⋆f)(x) = f(g⁻¹x) + c(g)(x) = f(x) + λ`, so `g⋆U_a = U_(a+λ)`.
Invariance gives `m(U_(a+λ)) = m(U_a)`. The two sets are disjoint, so `m(U_a) ≤ 1/2`.

**2. The difference mean is untwisted.** Define `μ(φ) = ∫∫ φ(f₁ − f₂) dm(f₁)dm(f₂)` for `φ ∈ ℓ^∞(A^(X))`.
Since `g·(f₁ − f₂) = g⋆f₁ − g⋆f₂`, the iterated-mean identity applied to `Φ(f₁,f₂) = φ(f₁ − f₂)` gives
`μ(φ∘g) = μ(φ)` for the linear action `g·`. For `x ∈ X`,
`μ({f : f(x) ≠ 0}) = m(f₁ ↦ m({f₂ : f₂(x) ≠ f₁(x)})) ≥ m(f₁ ↦ 1/2) = 1/2`, by step 1.

**3. Pass to supports.** `supp: A^(X) → P_f(X)` is `G`-equivariant for the linear action, so
`ν = supp_* μ`, `ν(φ) = μ(φ∘supp)`, is a `G`-invariant mean on `P_f(X)` with `ν({E : x ∈ E}) ≥ 1/2` for
every `x ∈ X`.

**4. Iterated unions.** Set `ν₁ = ν` and `ν_(r+1)(φ) = ∫∫ φ(E₁ ∪ E₂) dν_r(E₁)dν(E₂)`. Because
`g(E₁ ∪ E₂) = gE₁ ∪ gE₂`, induction and the iterated-mean identity show every `ν_r` is `G`-invariant. For
`x ∈ X`, the indicator of `x ∉ E₁ ∪ E₂` is the product of the indicators, so
`ν_(r+1)({x ∉ E}) = ν_r({x ∉ E}) · ν({x ∉ E}) ≤ 2^(−(r+1))`. For a finite `K ⊂ X`, by finite additivity,
`ν_r({E : K ⊄ E}) ≤ |K|·2^(−r)`.

The means on `P_f(X)` form a weak*-compact set (Banach–Alaoglu), so `(ν_r)` has a cluster point `ν_∞`.
Each condition `ν(φ∘g) = ν(φ)` is weak*-closed, so `ν_∞` is `G`-invariant. For fixed finite `K`,
`ν_∞({K ⊄ E})` is a limit of values `ν_r({K ⊄ E})` along a subnet whose indices `r` eventually exceed any
bound, so it is `0`. Thus `ν_∞` gives full weight to the sets containing any given finite set. This is
extensive amenability, Juschenko–Matte Bon–Monod–de la Salle Definition 1.1, verbatim as imported in
`affine-lamplighter-amenable-iff-extensively-amenable-citation`: "The action of a group G on a set X is
extensively amenable if there is a G-invariant mean on P_f(X) giving full weight to the collection of
subsets that contain any given element of P_f(X)." ∎

**Alternative for step 4.** JMMS Lemma 2.2, (iv) ⇒ (i), read from the arXiv:1503.04977 LaTeX source on
2026-09-17, verbatim: "(iv) There is a $G$-invariant mean on $\Pf(X)$ that gives nonzero weight to
$\{A \in \Pf(X), x_0 \in A\}$ for all $x_0 \in X$." Step 3 supplies exactly this.
