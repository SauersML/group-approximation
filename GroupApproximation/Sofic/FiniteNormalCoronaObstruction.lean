import GroupApproximation.Sofic.FiniteNormalCompressionObstruction
import GroupApproximation.Sofic.NormMFCoronaRadical
import GroupApproximation.Analysis.NormMatrixCoronaUnitary

/-!
# Finite-normal obstruction in the manuscript's cofinite-corona language

`FiniteNormalCompressionObstruction` proves the analytic statement at the
ultraproduct-residual level.  This file transports it first to the
unitary-sequence cofinite corona and then, through the formal polar-correction
equivalence, to the unitary group of the genuine C-star quotient.
-/

namespace GroupApproximation
namespace KazhdanCompressionCore

variable {Γ E : Type} [Group Γ] [Group E]

/-- A finite normal subgroup contained in the compression defect lies in the
universal cofinite norm-matrix-corona residual.  This is the subgroup-valued
form of `finiteNormal_le_normMatrixCoronaKernel`: it quantifies over all
positive-size matrix sequences and all corona homomorphisms at once. -/
theorem finiteNormal_le_coronaMFResidual
    [Countable E] (C : KazhdanCompressionCore Γ E)
    (F : Subgroup E) [Finite F] [F.Normal]
    (hF : F ≤ C.defectNormal) :
    F ≤ coronaMFResidual E := by
  rw [coronaMFResidual_eq_normMFResidual]
  exact C.finiteNormal_le_normMFResidual F hF

/-- **Finite-normal unitary-sequence-corona obstruction.**  If a finite normal
subgroup lies in the compression-defect normal closure, every homomorphism to
every standard positive-size unitary-sequence corona kills that subgroup. -/
theorem finiteNormal_le_normMatrixCoronaKernel
    [Countable E] (C : KazhdanCompressionCore Γ E)
    (F : Subgroup E) [Finite F] [F.Normal]
    (hF : F ≤ C.defectNormal)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (rho : E →* NormMatrixCoronaUnitary X) :
    F ≤ rho.ker := by
  intro f hf
  have hinvisible : NormMFInvisible (f : E) :=
    mem_normMFResidual_iff.mp
      (C.finiteNormal_le_normMFResidual F hF hf)
  exact NormMFInvisible.toCoronaMFInvisible (G := E) hinvisible X hX rho

/-- **Finite-normal C-star-corona obstruction.**  If a finite normal subgroup
lies in the compression-defect normal closure, every homomorphism into the
unitary group of the genuine norm-matrix C-star quotient kills it.  The proof
uses the inverse of the canonical polar-correction equivalence and then the
unitary-sequence theorem above. -/
theorem finiteNormal_le_normMatrixCStarCoronaKernel
    [Countable E] (C : KazhdanCompressionCore Γ E)
    (F : Subgroup E) [Finite F] [F.Normal]
    (hF : F ≤ C.defectNormal)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ rho : E →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      F ≤ rho.ker := by
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  let sigma : E →* NormMatrixCoronaUnitary X :=
    (normMatrixCoronaUnitaryEquiv X).symm.toMonoidHom.comp rho
  intro f hf
  have hkernel : f ∈ sigma.ker :=
    C.finiteNormal_le_normMatrixCoronaKernel F hF X hX sigma hf
  apply MonoidHom.mem_ker.mpr
  apply (normMatrixCoronaUnitaryEquiv X).symm.injective
  simpa [sigma] using MonoidHom.mem_ker.mp hkernel

/-- The same finite subgroup is killed by every homomorphism into a group
which embeds in a standard cofinite norm-matrix corona.  This composition
form is the group-theoretic core of the manuscript's extension from corona
targets to unitary groups of C*-subalgebras of coronas. -/
theorem finiteNormal_le_kernel_of_target_embeds
    [Countable E] (C : KazhdanCompressionCore Γ E)
    (F : Subgroup E) [Finite F] [F.Normal]
    (hF : F ≤ C.defectNormal)
    {H : Type*} [Group H] (rho : E →* H)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ (j : H →* unitary (NormMatrixCStarCorona (fun n ↦ X n))),
      Function.Injective j → F ≤ rho.ker := by
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro j hj f hf
  have hcomp : f ∈ (j.comp rho).ker :=
    C.finiteNormal_le_normMatrixCStarCoronaKernel F hF X hX (j.comp rho) hf
  apply MonoidHom.mem_ker.mpr
  apply hj
  simpa only [MonoidHom.coe_comp, Function.comp_apply, map_one] using
    MonoidHom.mem_ker.mp hcomp

/-- A nontrivial finite normal subgroup inside the compression defect rules
out operator MF in the unitary-sequence cofinite-corona presentation. -/
theorem not_isOperatorMF_of_finiteNormal_le_defect
    [Countable E] (C : KazhdanCompressionCore Γ E)
    (F : Subgroup E) [Finite F] [F.Normal] [Nontrivial F]
    (hF : F ≤ C.defectNormal) :
    ¬ IsOperatorMF E := by
  rintro ⟨X, hX, rho, hrho⟩
  obtain ⟨f, hf⟩ := exists_ne (1 : F)
  have hker : (f : E) ∈ rho.ker :=
    C.finiteNormal_le_normMatrixCoronaKernel F hF X hX rho f.property
  have hfeq : (f : E) = 1 := by
    apply hrho
    simpa using (MonoidHom.mem_ker.mp hker)
  exact hf (Subtype.ext hfeq)

end KazhdanCompressionCore

namespace MarkedCompressionInclusionData

variable {Gamma E : Type} [Group Gamma] [Group E]

/-- Marked compatibility form of the finite-normal cofinite-corona
obstruction. -/
theorem not_isOperatorMF_of_mem_finiteNormal
    [Countable E] (D : MarkedCompressionInclusionData Gamma E)
    (F : Subgroup E) [Finite F] [F.Normal]
    (hF : F ≤ D.toKazhdanCompressionCore.defectNormal)
    (hword : D.word ∈ F) (hne : D.word ≠ 1) :
    ¬ IsOperatorMF E := by
  rintro ⟨X, hX, rho, hrho⟩
  have hker : D.word ∈ rho.ker :=
    D.toKazhdanCompressionCore.finiteNormal_le_normMatrixCoronaKernel
      F hF X hX rho hword
  exact hne (hrho (by simpa using (MonoidHom.mem_ker.mp hker)))

end MarkedCompressionInclusionData
end GroupApproximation
