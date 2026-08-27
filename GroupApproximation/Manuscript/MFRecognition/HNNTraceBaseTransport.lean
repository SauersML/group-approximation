import GroupApproximation.Analysis.StarSubalgebraMapEquiv
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceSetup

/-!
# Transporting the regular trace to the HNN base algebra
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- The closed range of the corona embedding, as a star subalgebra. -/
def HNNTraceIotaRange (data : CoronaConjugator G S T phi A X) :
    StarSubalgebra ℂ (Corona X) :=
  (⊤ : StarSubalgebra ℂ A).map data.iota

theorem HNNTraceIotaRange_isClosed
    (data : CoronaConjugator G S T phi A X) :
    IsClosed ((HNNTraceIotaRange data : StarSubalgebra ℂ (Corona X)) :
      Set (Corona X)) := by
  have hrange : ((HNNTraceIotaRange data : StarSubalgebra ℂ (Corona X)) :
      Set (Corona X)) = Set.range data.iota := by
    ext q
    constructor
    · rintro ⟨a, _, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, Set.mem_univ a, rfl⟩
  rw [hrange]
  have hiso : Isometry data.iota :=
    NonUnitalStarAlgHom.isometry data.iota data.iota_injective
  exact hiso.isUniformInducing.isComplete_range.isClosed

/-- Every element of `D = C*(ιρ(G))` lies in the range of `ι`. -/
theorem baseAlgebra_le_HNNTraceIotaRange
    (data : CoronaConjugator G S T phi A X) :
    baseAlgebra data ≤ HNNTraceIotaRange data := by
  apply StarSubalgebra.topologicalClosure_minimal
  · apply StarAlgebra.adjoin_le
    rintro q ⟨g, rfl⟩
    exact ⟨data.realization.rho g, Set.mem_univ _, rfl⟩
  · exact HNNTraceIotaRange_isClosed data

/-- Regard the base algebra as a subalgebra of the range of `ι`. -/
def HNNTraceBaseToIotaRange
    (data : CoronaConjugator G S T phi A X) :
    baseAlgebra data →⋆ₐ[ℂ] HNNTraceIotaRange data :=
  ((baseAlgebra data).subtype).codRestrict (HNNTraceIotaRange data)
    (fun d ↦ baseAlgebra_le_HNNTraceIotaRange data d.property)

/-- The inverse of `ι` on `D`. -/
def HNNTraceBaseRecovery
    (data : CoronaConjugator G S T phi A X) : baseAlgebra data →⋆ₐ[ℂ] A :=
  ((⊤ : StarSubalgebra ℂ A).subtype).comp
    ((starSubalgebraMapEquivOfInjective (⊤ : StarSubalgebra ℂ A)
      data.iota data.iota_injective).symm.toStarAlgHom.comp
        (HNNTraceBaseToIotaRange data))

theorem HNNTraceBaseRecovery_iota
    (data : CoronaConjugator G S T phi A X) (d : baseAlgebra data) :
    data.iota (HNNTraceBaseRecovery data d) = (d : Corona X) := by
  exact starSubalgebraMapEquivOfInjective_symm_coe
    (⊤ : StarSubalgebra ℂ A) data.iota data.iota_injective
      (HNNTraceBaseToIotaRange data d)

@[simp] theorem HNNTraceBaseRecovery_generator
    (data : CoronaConjugator G S T phi A X) (g : G) :
    HNNTraceBaseRecovery data
        (((baseUnitaryHom data g : unitary (baseAlgebra data)) :
          baseAlgebra data)) =
      ((data.realization.rho g : unitary A) : A) := by
  apply data.iota_injective
  rw [HNNTraceBaseRecovery_iota]
  rfl

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
