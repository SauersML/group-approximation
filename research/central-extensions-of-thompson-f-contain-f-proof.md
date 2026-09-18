---
rg: 2
id: central-extensions-of-thompson-f-contain-f-proof
kind: route
title: The flip reverses Brown's product and acts by −1 on H_2(F), so the flip-twisted juxtaposition diagonal kills H_2(F) and all trivial-coefficient H^2
target: central-extensions-of-thompson-f-contain-f
requires: []
---

**Source.** K. S. Brown, *The homology of Richard Thompson's group F*, arXiv:math/0411347,
TeX `homology.tex`:
- **l.371--378.** `F → Z×Z` is `f ↦ (log_2 f'(0), log_2 f'(1))`, and "The group~$F'$ is simple
  but infinitely generated; it is the union of an increasing sequence of isomorphic copies
  of~$F$."
- **l.387--400, 423, 426, 441.** The product `μ(f,g) = f*g` is a homomorphism
  `F × F → F`, with `1*f = φ(f)`. Left and right multiplication by the class `ε` of a point
  are induced by `f ↦ 1*f` and `f ↦ f*1`.
- **Theorem, l.677--701.** `H_n(F)` is free abelian of rank 2 for `n ≥ 1`. With
  `α = ζε` and `β = εζ`, the relations are "$\varepsilon\alpha=\beta \varepsilon=0$" and
  "$\alpha \varepsilon =\alpha\;, \quad \varepsilon\beta=\beta$", with `α² = β² = 0`, and the
  alternating products form a basis in positive degrees. So `H_2(F) = Zαβ ⊕ Zβα`.
- **l.796--806.** The diagonal induces a ring homomorphism
  `Δ : H_*(F) → H_*(F) ⊗ H_*(F)` with `Δ(ε) = ε⊗ε` and `α, β` primitive.

**Step 1: the flip on H_1.** Write `χ_0, χ_1` for the two slope coordinates. Then
`χ_0(1*f) = 0`, `χ_1(1*f) = χ_1(f)`, `χ_0(f*1) = χ_0(f)` and `χ_1(f*1) = 0`. Hence
`εα = 0` gives `χ_1(α) = 0`, and `βε = 0` gives `χ_0(β) = 0`. Since `{α, β}` is a basis of
`H_1 ≅ Z^2`, `χ_0(α)` and `χ_1(β)` are `±1`.

The flip `c_R(f) = RfR` is an automorphism of `F` with `(RfR)'(0) = f'(1)`, so
`χ_0 ∘ R_* = χ_1` and `χ_1 ∘ R_* = χ_0`. Therefore `R_*α = sβ` and `R_*β = sα` with
`s = χ_0(α)χ_1(β) = ±1`.

**Step 2: the flip reverses the product.** From the formula for `f*g`,
`R(f*g)R = (RgR)*(RfR)`, that is, `c_R ∘ μ = μ ∘ (c_R × c_R) ∘ τ` with `τ` the swap. The
swap acts on cross products by `τ_*(x×y) = (−1)^{|x||y|} y×x`, so
`R_*(xy) = (−1)^{|x||y|} R_*(y)R_*(x)`. Hence:
- `R_*(αβ) = −(sα)(sβ) = −αβ`;
- `R_*(βα) = −βα`;
- `R_*ε = ε`.

So `R_* = −id` on `H_2(F)`.

**Step 3: δ kills H_2.** We have `δ = μ ∘ (id × c_R) ∘ Δ_F`, so on homology
`δ_*(z) = Σ x_i · R_*(y_i)` when `Δ(z) = Σ x_i ⊗ y_i`. Multiplicativity of `Δ` (with the sign
`(x⊗y)(x'⊗y') = (−1)^{|y||x'|} xx'⊗yy'`) and the relations give:
- `Δ(αβ) = αβ⊗ε + α⊗β − β⊗α + ε⊗αβ`;
- `Δ(βα) = βα⊗ε + ε⊗βα`, because `βε = εα = 0`.

Hence:
- `δ_*(αβ) = (αβ)ε + α(sα) − β(sβ) − ε(αβ) = 0`, since `βε = εα = 0` and `α² = β² = 0`;
- `δ_*(βα) = (βα)ε − ε(βα) = βα − βα = 0`, since `αε = α` and `εβ = β`.

**Step 4: cohomology and splitting.**
- `δ` is injective, since `f*(RfR) = 1` forces `f = 1`.
- Because `H_1(F) ≅ Z^2` is free, the universal coefficient sequence gives a natural
  isomorphism `H^2(F;A) ≅ Hom(H_2(F), A)`. So `δ^* = 0` on `H^2(F;A)`.
- A central extension pulled back along `δ` therefore splits, and its preimage of `δ(F)`
  contains a copy of `F`. This gives (a).
- For (b), restrict the extension of `Q` to a subgroup isomorphic to `F` and apply (a).
