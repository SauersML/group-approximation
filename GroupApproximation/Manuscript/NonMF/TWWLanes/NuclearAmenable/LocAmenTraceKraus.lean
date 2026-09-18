import GroupApproximation.Analysis.LanceMaximalNuclear
import GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.LayerModel
import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.ChoiEffrosKraus
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-29, part 1: the Kraus column of a cp map out of a matrix block

Let `ψ : M_Z → A` be completely positive (in the `CStarExactness` sense).  Its Choi matrix
factors: `ψ(e_{z z'}) = ∑_k (P k z)⋆ (P k z')` with `k` in `Fin |Z|`
(`LanceMaximal.exists_choi_factor`).  Take `n = |Z|` copies of `Z`, i.e. the layered model
`ConnesTrick.layerModel Z (fun _ ↦ n)` on `Σ z : Z, Fin n`.  Then the column
`G ⟨z, k⟩ = P k z` is a Kraus column for `ψ` after the amplification `M ↦ M ⊗ 1_n`, which is
`ConnesTrick.layer`:

`ψ_G (layer M) = ψ M`   (`locAmenTrace_exists_krausColumn`).

The amplification is unital and preserves form complete positivity by
`ConnesTrick.layerLinear_comp_ucp`.  Everything in this file is proved.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearAmenable

open Matrix Quasidiagonal CStarExactness
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

attribute [local instance] CStarExactness.matrixBlockCStarAlgebraForLanceForward

variable {A : Type u} [CStarAlgebra A]

/-- The Kraus column `⟨z, k⟩ ↦ P k z` on the layered model with `n` copies of `Z`. -/
def locAmenTraceColumn (Z : FiniteModel) (n : ℕ) (P : Fin n → Z → A) :
    ConnesTrick.layerModel Z (fun _ ↦ n) → A :=
  fun p ↦ P p.2 p.1

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.locAmenTraceColumn

theorem locAmenTraceColumn_mk (Z : FiniteModel) (n : ℕ) (P : Fin n → Z → A) (z : Z)
    (k : Fin n) :
    locAmenTraceColumn Z n P (⟨z, k⟩ : ConnesTrick.layerModel Z (fun _ ↦ n)) = P k z := rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.locAmenTraceColumn_mk

/-- Sums over the layered model split as a double sum. -/
theorem locAmenTrace_sum_layerModel (Z : FiniteModel) (n : ℕ)
    (f : ConnesTrick.layerModel Z (fun _ ↦ n) → A) :
    ∑ p, f p = ∑ z : Z, ∑ k : Fin n, f ⟨z, k⟩ :=
  Fintype.sum_sigma f

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.locAmenTrace_sum_layerModel

/-- The amplified matrix acting on the Kraus column. -/
theorem locAmenTrace_act_layer (Z : FiniteModel) (n : ℕ) (P : Fin n → Z → A)
    (M : Matrix Z Z ℂ) (z : Z) (k : Fin n) :
    ∑ q, ConnesTrick.layer (fun _ ↦ n) M ⟨z, k⟩ q • locAmenTraceColumn Z n P q =
      ∑ z', M z z' • P k z' := by
  rw [locAmenTrace_sum_layerModel]
  refine Finset.sum_congr rfl fun z' _ ↦ ?_
  rw [Finset.sum_eq_single k]
  · have hc : (k : ℕ) = (k : ℕ) := rfl
    exact congrArg (· • P k z')
      ((ConnesTrick.layer_apply (fun _ ↦ n) M ⟨z, k⟩ ⟨z', k⟩).trans (if_pos hc))
  · intro b _ hb
    have hc : ¬ ((k : ℕ) = (b : ℕ)) := fun h ↦ hb (Fin.ext h).symm
    exact (congrArg (· • locAmenTraceColumn Z n P ⟨z', b⟩)
      ((ConnesTrick.layer_apply (fun _ ↦ n) M ⟨z, k⟩ ⟨z', b⟩).trans (if_neg hc))).trans
      (zero_smul ℂ _)
  · intro h
    exact absurd (Finset.mem_univ _) h

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.locAmenTrace_act_layer

/-- **The Kraus identity.** `ψ_G (layer M) = ∑_{z, z'} M_{z z'} • ∑_k (P k z)⋆ (P k z')`. -/
theorem locAmenTrace_krausMap_layer (Z : FiniteModel) (n : ℕ) (P : Fin n → Z → A)
    (M : Matrix Z Z ℂ) :
    NuclearDensity.choiEffrosKrausMap (locAmenTraceColumn Z n P)
        (ConnesTrick.layer (fun _ ↦ n) M) =
      ∑ z, ∑ z', M z z' • ∑ k : Fin n, star (P k z) * P k z' := by
  show ∑ p, star (locAmenTraceColumn Z n P p) *
      ∑ q, ConnesTrick.layer (fun _ ↦ n) M p q • locAmenTraceColumn Z n P q = _
  rw [locAmenTrace_sum_layerModel]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  calc ∑ k : Fin n, star (locAmenTraceColumn Z n P ⟨z, k⟩) *
        ∑ q, ConnesTrick.layer (fun _ ↦ n) M ⟨z, k⟩ q • locAmenTraceColumn Z n P q
      = ∑ k : Fin n, ∑ z', M z z' • (star (P k z) * P k z') := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [locAmenTrace_act_layer, locAmenTraceColumn_mk, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z' _ ↦ ?_
        rw [mul_smul_comm]
    _ = ∑ z', ∑ k : Fin n, M z z' • (star (P k z) * P k z') := Finset.sum_comm
    _ = ∑ z', M z z' • ∑ k : Fin n, star (P k z) * P k z' :=
        Finset.sum_congr rfl fun z' _ ↦ Finset.smul_sum.symm

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.locAmenTrace_krausMap_layer

/-- **Kraus form of a cp map out of a matrix block.**  A completely positive
`ψ : M_Z → A` is `ψ_G ∘ layer` for a column `G` on the layered model with `|Z|` copies. -/
theorem locAmenTrace_exists_krausColumn (Z : FiniteModel) [Nonempty Z]
    (ψ : Matrix Z Z ℂ →ₗ[ℂ] A) (hψ : IsCompletelyPositive ψ) :
    ∃ P : Fin (Fintype.card Z) → Z → A, ∀ M : Matrix Z Z ℂ,
      NuclearDensity.choiEffrosKrausMap (locAmenTraceColumn Z (Fintype.card Z) P)
        (ConnesTrick.layer (fun _ ↦ Fintype.card Z) M) = ψ M := by
  obtain ⟨P, hP⟩ := LanceMaximal.exists_choi_factor Z ψ hψ
  refine ⟨fun k z ↦ P k (Fintype.equivFin Z z), fun M ↦ ?_⟩
  rw [locAmenTrace_krausMap_layer, LanceMaximal.linearMap_eq_sum_single Z ψ M]
  exact Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun z' _ ↦
    congrArg (M z z' • ·) (hP z z').symm

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.locAmenTrace_exists_krausColumn

end

end Manuscript.NonMF.TWWLanes.NuclearAmenable
end GroupApproximation
