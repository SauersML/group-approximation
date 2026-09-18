import GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.LayerModel
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-11, endpoint: Connes' trick, reduced to layer rounding

The target is `NuclearAmenable.ConnesTrickStatement` (TWWLanes/NuclearAmenable/Glue.lean):
approximately invariant densities give a locally amenable trace. The previous files prove the
structural half of Brown--Ozawa, Thm 6.2.7:

* part 3 diagonalises the density (`hasDiagonalDensities_of_hasApproxInvariantDensities`);
* part 4 shows that for any multiplicities `c`, the layered model `layerLinear c ∘ₗ B` is ucp
  (`layerLinear_comp_ucp`);
* contractivity `‖B x‖ ≤ ‖x‖` is `Quasidiagonal.ucpContractive`, a theorem.

## The one remaining Statement

`LayerRoundingStatement` is the quantitative rounding step. It is purely about one fixed
linear map into one fixed matrix algebra, and it involves no spectral theorem and no complete
positivity. The tolerance `ε₁` may depend only on `F` and `ε`. The multiplicities `c` may
depend on everything, including `card Y`.

**Why it is true.** Put `K = 1 + ∑_{x ∈ F} ‖x‖`, and fix `N ≥ 2 card Y`. Take
`c i = ⌊N μᵢ²⌋₊` and write `S = ∑ᵢ cᵢ`, so `N/2 ≤ N - card Y ≤ S ≤ N`. The matrix entries
satisfy `|B(x)ᵢⱼ| ≤ ‖B x‖ ≤ K`.

* **Trace.** `normTrace (layer c M) = (∑ᵢ cᵢ Mᵢᵢ)/S`, and `∑ᵢ |cᵢ/S - μᵢ²| ≤ 2 card Y / S`.
  So the trace defect is at most `ε₁ + 4 K card Y / N`.
* **Multiplicativity.** Write `E_k = span {i : k < cᵢ}`. Then
  `layer(B(xy)) - layer(Bx) layer(By) = layer Δ + ⊕ₖ E_k Bx (1 - E_k) By E_k`, where
  `Δ = B(xy) - Bx By`.
  * The first summand has unnormalised HS² equal to
    `∑ᵢⱼ |Δᵢⱼ|² min(cᵢ, cⱼ) ≤ N ∑ᵢⱼ |Δᵢⱼ|² μⱼ² ≤ N ε₁`.
  * The second is at most `K² ∑ᵢⱼ |By ᵢⱼ|² |cⱼ - cᵢ|`. Using
    `|cⱼ - cᵢ| ≤ N |μⱼ - μᵢ| (|μᵢ| + |μⱼ|) + 1`, Cauchy--Schwarz, and
    `∑ᵢⱼ |By ᵢⱼ|² μⱼ² = ‖By D‖₂² ≤ K²` (and likewise for `D By`), this is at most
    `K² (2 K N √ε₁ + K² card Y)`.

  Dividing by `S ≥ N/2` gives `hsNorm² ≤ 4 ε₁ + 8 K³ √ε₁ + 4 K⁴ card Y / N`.

Choose `ε₁` with `ε₁ ≤ ε/2` and `4 ε₁ + 8 K³ √ε₁ ≤ ε²/2`, and then take `N` large. Both
defects are then at most `ε`.

**Why it is smaller.** Diagonalisation, complete positivity of the layered model,
unitality, contractivity, and all the plumbing into `IsLocallyAmenableTrace` are proved here.
The Statement asks only for an entrywise estimate about floor rounding. The reduction
`connesTrickStatement_of_layerRounding` is proved, and so are its compositions with the Glue
theorems.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.ConnesTrick

open Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

/-- **Layer rounding** (the quantitative half of Connes' trick, Brown--Ozawa 6.2.7). -/
def LayerRoundingStatement : Prop :=
  ∀ (A : Type u) (_ : CStarAlgebra A) (τ : A → ℂ) (F : Finset A) (ε : ℝ), 0 < ε →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ (Y : FiniteModel) (B : A →ₗ[ℂ] Matrix Y Y ℂ) (μ : Y → ℝ),
        (∀ x, ‖B x‖ ≤ ‖x‖) → ∑ i, μ i ^ 2 = 1 →
        (∀ x ∈ F, ‖τ x - ∑ i, ((μ i ^ 2 : ℝ) : ℂ) * B x i i‖ ≤ ε₁) →
        (∀ x ∈ F, ∑ i, ∑ j, Complex.normSq (B x i j) * (μ j - μ i) ^ 2 ≤ ε₁) →
        (∀ x ∈ F, ∀ y ∈ F,
          ∑ i, ∑ j, Complex.normSq ((B (x * y) - B x * B y) i j) * μ j ^ 2 ≤ ε₁) →
        ∃ c : Y → ℕ,
          (∀ x ∈ F, ∀ y ∈ F,
            hsNorm (layerModel Y c)
              (layer c (B (x * y)) - layer c (B x) * layer c (B y)) ≤ ε) ∧
          (∀ x ∈ F, ‖τ x - normTrace (layerModel Y c) (layer c (B x))‖ ≤ ε)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.LayerRoundingStatement

/-- **Connes' trick, reduced to layer rounding.** -/
theorem connesTrickStatement_of_layerRounding (h : LayerRoundingStatement.{u}) :
    NuclearAmenable.ConnesTrickStatement.{u} := by
  intro A _ τ hτ F ε hε
  obtain ⟨ε₁, hε₁, hround⟩ := h A inferInstance τ F ε hε
  obtain ⟨Y, B, μ, hone, hcp, hμ, htr, hcomm, hmul⟩ :=
    hasDiagonalDensities_of_hasApproxInvariantDensities hτ F ε₁ hε₁
  obtain ⟨c, hc1, hc2⟩ := hround Y B μ
    (ucpContractive.norm_le A inferInstance Y B hone hcp) hμ htr hcomm hmul
  obtain ⟨hone', hcp'⟩ := layerLinear_comp_ucp c B hone hcp
  have e : ∀ x, (layerLinear c ∘ₗ B) x = layer c (B x) := fun x ↦ rfl
  refine ⟨layerModel Y c, layerLinear c ∘ₗ B, hone', hcp', ?_, ?_⟩
  · intro x hx y hy
    first
      | exact hc1 x hx y hy
      | (rw [e, e, e]; exact hc1 x hx y hy)
  · intro x hx
    first
      | exact hc2 x hx
      | (rw [e]; exact hc2 x hx)

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.connesTrickStatement_of_layerRounding

/-- Layer rounding and nuclear approximate densities give locally amenable traces. -/
theorem nuclearLocallyAmenableTrace_of_layerRounding_of_nuclearDensity
    (h : LayerRoundingStatement.{u})
    (h12 : NuclearAmenable.NuclearTraceApproxDensityStatement.{u}) :
    NuclearAmenable.NuclearLocallyAmenableTraceStatement.{u} :=
  NuclearAmenable.nuclearLocallyAmenableTrace_of_connesTrick_of_nuclearDensity
    (connesTrickStatement_of_layerRounding h) h12

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.nuclearLocallyAmenableTrace_of_layerRounding_of_nuclearDensity

/-- Layer rounding and nuclear approximate densities give the separable nuclear amenable
trace Statement. -/
theorem nuclearAmenableTraceSeparable_of_layerRounding_of_nuclearDensity
    (h : LayerRoundingStatement.{u})
    (h12 : NuclearAmenable.NuclearTraceApproxDensityStatement.{u}) :
    NuclearAmenable.NuclearAmenableTraceSeparableStatement.{u} :=
  NuclearAmenable.nuclearAmenableTraceSeparable_of_connesTrick_of_nuclearDensity
    (connesTrickStatement_of_layerRounding h) h12

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.nuclearAmenableTraceSeparable_of_layerRounding_of_nuclearDensity

end

end Manuscript.NonMF.TWWLanes.ConnesTrick
end GroupApproximation
