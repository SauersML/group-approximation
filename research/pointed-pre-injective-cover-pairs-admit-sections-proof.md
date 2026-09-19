---
rg: 2
id: pointed-pre-injective-cover-pairs-admit-sections-proof
kind: route
title: Unique pointed lifts are local because lifts away from the identity do not touch it, so they form a cellular automaton that extends by density to a section
target: pointed-pre-injective-cover-pairs-admit-sections
requires:
  - strict-pairs-give-dual-failures-on-bounded-defect-domains
artifacts:
  - research/artifacts/pointed-pre-injective-sections-2026-09-18.md
---

Conventions: `(g.x)(h) = x(g^-1 h)`, so `(g^-1.x)(1) = x(g)`. `Δ(x, x')` is the set of sites where `x, x'` differ.
Lifts are as in the claim: `Δ(x, x') ⊆ Δ(F(x), z) Φ`. The full proof, with the periodic-point variant and a
calibration, is in `research/artifacts/pointed-pre-injective-sections-2026-09-18.md`. Here is the core.

**Step 1 (pointed lift map).** Let `y ~ d^G`. Since `F(c^G) = d^G`, strong post-surjectivity gives `x ∈ X` with
`x ~ c^G` and `F(x) = y`. By injectivity on `Fin_c(X)` it is unique; call it `s(y)`. So
`s : Fin_d(A^G) → Fin_c(X)` is a bijection inverse to `F`.

**Step 2 (locality).** Let `y, y' ~ d^G` agree on `Φ^-1`. Then `Δ = Δ(y, y')` is finite and misses `Φ^-1`, so
`1 ∉ ΔΦ`. Lift `y'` from `s(y)`: there is `x' ∈ X` with `x' ~ s(y) ~ c^G`, `F(x') = y'` and
`Δ(s(y), x') ⊆ ΔΦ`. By uniqueness `x' = s(y')`, and `s(y')(1) = x'(1) = s(y)(1)`. So there is a map
`σ : A^(Φ^-1) → A` with `s(y)(1) = σ(y|_(Φ^-1))` for all `y ~ d^G`. It is defined on every pattern, because each
pattern on `Φ^-1` extends by `d` to a point of `Fin_d`.

**Step 3 (equivariance).** For `g ∈ G`, `g.s(y) ∈ X`, `g.s(y) ~ g.c^G = c^G` and `F(g.s(y)) = g.y`. By
uniqueness `s(g.y) = g.s(y)`. Hence `s(y)(g) = s(g^-1.y)(1) = σ((g^-1.y)|_(Φ^-1))`.

**Step 4 (extension).** Let `s̄` be the cellular automaton with memory `Φ^-1` and local rule `σ`. It is continuous
and equivariant, and it equals `s` on `Fin_d(A^G)` by Step 3. `Fin_d(A^G)` is dense in `A^G`. `X` is closed and
`s̄(Fin_d) ⊆ X`, so `s̄(A^G) ⊆ X`. The maps `F ∘ s̄` and `id` are continuous and agree on a dense set, so
`F ∘ s̄ = id`. This is the section.

**Step 5 (non-surjunctivity).** `F ∘ s̄ = id` makes `s̄` injective. Its image lies in `X`, so if `X ≠ A^G` then
`s̄` is an injective, non-surjective cellular automaton on `A^G`. `∎`

**Theorem P'.** Repeat Steps 1–4 with `p` in place of `c^G` and `q = F(p)` in place of `d^G`. `H` fixes `p` and
`q`, so Step 3 gives only `H`-equivariance. Step 2 is run at every site `t` rather than at `1`: if `y, y' ~ q`
agree on `tΦ^-1`, then `t ∉ Δ(y, y')Φ`, so `s(y)(t) = s(y')(t)`. Choose a finite right transversal `T` of `H`
(`G = ⊔_(t ∈ T) Ht`). The values `s(y)(ht) = s(h^-1.y)(t)` are then given by the finitely many local rules
`σ_t : A^(tΦ^-1) → A`. So `s` is uniformly continuous on the dense set `Fin_q(A^G)`, and Step 4 applies. With
`X ≠ A^G`, recode `A^G ≅ (A^T)^H` by `x ↦ (h ↦ (x(ht))_(t ∈ T))`; this is an `H`-equivariant homeomorphism.
Then `s̄` becomes an injective, non-surjective automaton `θ` over `H` on `B^H` with `B = A^T`, with memory
`N ⊆ H` and local rule `μ`.
- Induce it to `G`. Write `G = ⊔_i g_i H` as a union of left cosets. Let `θ_G(x)(g) = μ((x(gn))_(n ∈ N))`.
- This is an automaton over `G`. On each left coset it acts as a copy of `θ`, through `h ↦ x(g_i h)`.
- So `θ_G` is injective and not surjective.

This is the standard fact that subgroups of surjunctive groups are surjunctive. So `G` is not surjunctive.

**Corollary 1.** It is the contrapositive of P and P', with `p` of finite orbit and `H` its stabilizer.
Pre-injectivity implies injectivity on each `Fin_p(X)`, since all points of `Fin_p(X)` are mutually asymptotic.

**Corollary 2.** CP ⇒ PSD_c is vacuous. For PSD_c ⇒ CP, suppose `(X, F)` is a constant-point cover pair over
`G`. By PSD_c it is pre-injective, so by Theorem P `G` is not surjunctive, and `G` carries a strict pair `(τ, σ)`.
By `strict-pairs-give-dual-failures-on-bounded-defect-domains` (items 1, 2, 4 and 5), `(X_R, σ|_(X_R))` is a
cover pair over the same alphabet. Its domain is a proper strongly irreducible SFT and contains the constant
`τ(a^G)`. The restriction is not pre-injective, which contradicts PSD_c. The SI version is the same argument,
because `X_R` is strongly irreducible.

**Corollary 3.** "⇐" is Theorem P, which uses only that `X` is closed. For "⇒", let `τ` be injective and
non-surjective with memory `M`, and let `X = τ(A^G)`. This is a closed invariant proper subshift containing the
constant `τ(c^G)`. `F = τ^-1 : X → A^G` is continuous (a continuous bijection of compact Hausdorff spaces) and
equivariant, hence an automaton on `X`. For `x = τ(u)` and `z ~ u`, put `x' = τ(z) ∈ X`. Then `F(x') = z`, and
`Δ(x, x') ⊆ Δ(u, z)M^-1`, so the lift constant is `Φ = M^-1`. `F` is injective.

**Corollary 4.** Theorem P gives the section directly, with no seed.
