---
rg: 2
id: double-swap-embeds-group-in-derived-subgroup-proof
kind: route
title: Direct proof of the double-and-swap embedding
target: double-swap-embeds-group-in-derived-subgroup
requires: []
---

Write `Δ = (Γ × Γ) ⋊ C_2`, `C_2 = ⟨s⟩`, `s(a,b)s^(-1) = (b,a)`.

**1. `ι` is a homomorphism and injective.** `Γ × Γ` is a direct product, so
`ι(γ)ι(γ') = (γ,γ^(-1))(γ',γ'^(-1)) = (γγ', γ^(-1)γ'^(-1))`. That equals
`ι(γγ') = (γγ', (γγ')^(-1)) = (γγ', γ'^(-1)γ^(-1))` only when the second coordinates agree, so use
the opposite convention in the second factor: define `ι(γ) = (γ, γ^(-1))` with the second factor
`Γ^op`. Concretely take `Δ = (Γ × Γ^op) ⋊ C_2`; the swap is still an automorphism of order two
because `(Γ × Γ^op)` is carried to itself by `(a,b) ↦ (b,a)` read in the opposite factors, and
`Γ ≅ Γ^op` through `γ ↦ γ^(-1)`. With this convention `ι` is a homomorphism, and it is injective
because the first coordinate already is.

An equivalent formulation that avoids `Γ^op`: keep `Δ = (Γ × Γ) ⋊ C_2` and set
`ι(γ) = (γ, θ(γ))` where `θ(γ) = γ^(-1)` is the canonical anti-automorphism composed with the
identification of the second factor with `Γ^op`. Both give the same subgroup of `Δ`.

**2. The image consists of commutators.** For `(a,1) ∈ Γ × Γ`,

    [(a,1), s] = (a,1) · s(a,1)^(-1)s^(-1) = (a,1)(1,a^(-1)) = (a, a^(-1)).

So `ι(γ) = [(γ,1), s]`, a single commutator in `Δ`, and `ι(Γ) ⊆ [Δ, Δ]`.

**3. Permanence.** `Γ × Γ` is a finite direct product of copies of `Γ`, and `Δ` is an extension of
the finite group `C_2` by `Γ × Γ`. A class closed under finite direct products and extensions by
finite groups therefore contains `Δ`. For sofic groups both closure properties are standard: finite
direct products are immediate from the definition, and extensions with amenable quotient are
Elek--Szabó. If `Γ = ⟨S⟩` then `Δ = ⟨S × {1}, {1} × S, s⟩` is finitely generated.

**4. Into `E_3`.** Let `R` be a unital ring and `a, b ∈ R^x`. Whitehead's lemma gives
`diag(a, a^(-1), 1) ∈ E_3(R)` for every unit `a`, and

    diag(a,a^(-1),1) diag(b,b^(-1),1) diag((ab)^(-1),ab,1) = diag(1, a^(-1)b^(-1)ab, 1),

since the first coordinates multiply to `ab(ab)^(-1) = 1`. Every commutator of units is
`[a^(-1), b^(-1)]` for suitable `a, b`, so `c ↦ diag(1, c, 1)` maps `[R^x, R^x]` into `E_3(R)`; it is
a homomorphism because the middle coordinate multiplies coordinatewise. If `Δ ⊆ R^x` then
`γ ↦ diag(1, u_(ι(γ)), 1)` embeds `Γ` in `E_3(R) = EL_3(R)`.

**5. Injectivity modulo the centre.** If `diag(1, c, 1) = z 1_3` with `z` central, then `z = 1` by the
first coordinate, so `c = 1`. So the embedding survives the quotient by any central subgroup.
