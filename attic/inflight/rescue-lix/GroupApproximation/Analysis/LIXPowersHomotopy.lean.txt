import GroupApproximation.Analysis.LIXPowersNormalise

/-!
# The homotopy `u^{k+1} ≃ u ∘ ψ_k`, with no clutching

**This is the primary export of the powers lane** (lead, 2026-09-10).

The live Corollary-4 chain never clutches.  It glues the two hemisphere frames of
`Analysis/LIXGeneratorUnitary.lean` with a null-homotopy into a continuous unitary field `G`
with `G e₃ = x`; for the `k`-th power the same construction, with the frames pulled back
along `Σψ_k`, has seam `u ∘ ψ_k` and takes `e₃` to `x ∘ Σψ_k`.  What that construction needs
from this lane is therefore a homotopy of **maps** `S^{2n} → U(n)`, not an equivalence of
projections:

```text
u^{k+1}  ≃  u ∘ ψ_k
```

and that is `exists_homotopy_pow_comp` below.  The homotopy is one explicit formula, the
ordered product of the `k+1` angle reparametrisations of
`Analysis/LIXPowersAngle.lean`, with `θ` running the clamped angles.

## No contraction, and no `U(n)`

The only hypothesis is that the generator is the identity matrix on the wall, and
`Analysis/LIXPowersNormalise.lean` supplies that for free: `normGen_wall` holds for the
renormalisation `ũ` of an arbitrary ball unitary.  So `exists_homotopy_pow_comp_normGen`
has no hypothesis on the generator at all beyond ball-unitarity.

Passing from `ũ` back to `u` at the level of maps *would* need the wall part contracted, and
that is the only place path-connectedness of `U(n)` ever threatened to enter.  **It is not
built, because it is not needed**: the endpoint witness is `ũ ⊕ 1_H` rather than `u ⊕ 1_H`
(lead, 2026-09-10), and nothing downstream distinguishes them — `ũ = Aᴴ u` with `A` a ball
unitary, so `ũ ⊕ 1` still contracts in `U(n+1)`, `ũ ∉ U₀` iff `u ∉ U₀`, and the frames gauged
by `A` on one hemisphere have seam `ũ` and still take `e₃` to `x`.

## Consumer

`sp-tower`, who own `LIXGeneratorUnitary` and the stage unitary, and who build the
`k`-indexed Corollary-4 chain around the renormalised generator.  `sp-oddside` consumes
nothing from this file: on the `CharClass` side the `k`-th-power object is
`FHmat_eq_fromBlocks` with the section `b = x ∘ Σψ_k` substituted, which needs no clutching
and no homotopy.
-/

namespace GroupApproximation
namespace LIX
namespace Powers

open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

section Homotopy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e₁ e₂ : E}
  {n : Type*} [Fintype n] [DecidableEq n] {U : E → Matrix n n ℂ}

/-- **The bare Eckmann--Hilton homotopy**, with no clutching anywhere.

For a generator that is already the identity on the wall, `W^{k+1}` and `W ∘ ψ_k` are
homotopic through maps that are unitary on the closed ball, and the homotopy is the ordered
product of the `k+1` angle reparametrisations -- one explicit formula, `θ` running the
clamped angles.

This is the form a Corollary-4-style chain consumes: `Analysis/LIXLemmaSixField.lean` takes
a null-homotopy of the stage unitary and builds a continuous unitary field, and it never
mentions `clutchMat`, so what it needs from this lane is a homotopy of *maps*, not an
equivalence of projections.  Nothing here needs a contraction, and in particular nothing
here needs path-connectedness of `U(n)`: the hypothesis `hwall` is what
`Analysis/LIXPowersNormalise.lean` supplies for free.

Going from this to the *unnormalised* generator does need the wall part contracted, which
the clutched route (`clutchEquiv_pow_pullback`) avoids; see
`notes/lix-stronger-lane-reports/sp-powers.md` §0.3 for the trade. -/
theorem exists_homotopy_pow_comp (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsBallUnitary U)
    (hwall : ∀ y : E, ‖y‖ ≤ 1 → U (wallRetract e₁ e₂ y) = 1) (k : ℕ) :
    ∃ G : ℝ → E → Matrix n n ℂ,
      Continuous (fun p : ℝ × E => G p.1 p.2) ∧
      (∀ y : E, G 0 y = (U y) ^ (k + 1)) ∧
      (∀ y : E, ‖y‖ = 1 → G 1 y = U (joinPowNeg e₁ e₂ k y)) ∧
      (∀ (θ : ℝ) (y : E), ‖y‖ ≤ 1 → (G θ y)ᴴ * G θ y = 1) ∧
      (∀ (θ : ℝ) (y : E), ‖y‖ ≤ 1 → G θ y * (G θ y)ᴴ = 1) := by
  have hPb : ∀ (j : ℕ) (θ : ℝ) (y : E), ‖y‖ ≤ 1 →
      ‖angleFam e₁ e₂ k j θ y‖ ≤ 1 :=
    fun j θ y hy => le_of_eq_of_le (norm_angleFam h₁ h₂ h₁₂ k j θ y) hy
  refine ⟨fun θ y => reparProd U (angleFam e₁ e₂ k) θ y (k + 1),
    continuous_reparProd hU.continuous (continuous_angleFam e₁ e₂ k) (k + 1),
    fun y => reparProd_param_zero (angleFam_param_zero e₁ e₂ k) U y (k + 1),
    fun y hy => pinchIdentification_angleRepar h₁ h₂ h₁₂ k hwall y hy,
    fun θ y hy => (unit_reparProd hU hPb θ hy (k + 1)).1,
    fun θ y hy => (unit_reparProd hU hPb θ hy (k + 1)).2⟩

/-- **The bare homotopy is available for any generator, after renormalisation.**  `ũ` is the
renormalisation of `Analysis/LIXPowersNormalise.lean`; `hwall` is discharged there by
`normGen_wall`, so this needs no hypothesis on the generator at all. -/
theorem exists_homotopy_pow_comp_normGen (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsBallUnitary U) (k : ℕ) :
    ∃ G : ℝ → E → Matrix n n ℂ,
      Continuous (fun p : ℝ × E => G p.1 p.2) ∧
      (∀ y : E, G 0 y = (normGen e₁ e₂ U y) ^ (k + 1)) ∧
      (∀ y : E, ‖y‖ = 1 → G 1 y = normGen e₁ e₂ U (joinPowNeg e₁ e₂ k y)) ∧
      (∀ (θ : ℝ) (y : E), ‖y‖ ≤ 1 → (G θ y)ᴴ * G θ y = 1) ∧
      (∀ (θ : ℝ) (y : E), ‖y‖ ≤ 1 → G θ y * (G θ y)ᴴ = 1) :=
  exists_homotopy_pow_comp h₁ h₂ h₁₂ (isBallUnitary_normGen h₁ h₂ h₁₂ hU)
    (fun _ hy => normGen_wall h₁ h₂ h₁₂ hU hy) k

end Homotopy

end

end Powers
end LIX
end GroupApproximation
