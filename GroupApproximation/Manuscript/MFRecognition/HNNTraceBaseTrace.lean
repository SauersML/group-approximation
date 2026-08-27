import GroupApproximation.Analysis.MaximalGroupCStarTrace
import GroupApproximation.Analysis.HNNTraceGeneratedDensity
import GroupApproximation.Analysis.HNNTraceStarAlgHomDescent
import GroupApproximation.Analysis.HNNTraceTracialStateContinuous
import GroupApproximation.Manuscript.MFRecognition.HNNTraceBaseTransport

/-!
# The transported base trace in the HNN argument

The regular trace is transported through the corona embedding and compared on
the maximal group C-star algebra with its canonical trace.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
open ReducedGroupCStarTrace
open GroupApproximation.HNNTrace

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

local instance maximalGroupCStarNontrivial : Nontrivial (MaximalGroupCStar G) := by
  refine ⟨1, 0, fun h ↦ ?_⟩
  have heval := congrArg (maximalGroupCStarEval G
    (CStarUnitaryRepresentation.reduced G)) h
  rw [map_one, map_zero] at heval
  exact one_ne_zero heval

/-- The printed trace `T` on `D`. -/
def baseTrace (data : CoronaConjugator G S T phi A X) :
    TracialState (baseAlgebra data) :=
  data.realization.tau.compStarAlgHom (HNNTraceBaseRecovery data)

/-- Printed: *"`T(ιρ(g)) = 0` for `g ≠ 1`"*. -/
theorem baseTrace_regular
    (data : CoronaConjugator G S T phi A X) (g : G) (hg : g ≠ 1) :
    baseTrace data
        (((baseUnitaryHom data g : unitary (baseAlgebra data)) :
          baseAlgebra data)) = 0 := by
  rw [baseTrace, TracialState.compStarAlgHom_apply,
    HNNTraceBaseRecovery_generator]
  exact data.realization.regular g hg

/-- The maximal group C-star algebra maps onto `D = C*(ιρ(G))`. -/
def maximalToBase (data : CoronaConjugator G S T phi A X) :
    MaximalGroupCStar G →⋆ₐ[ℂ] baseAlgebra data :=
  maximalGroupCStarLift G (baseUnitaryHom data)

@[simp] theorem maximalToBase_generator
    (data : CoronaConjugator G S T phi A X) (g : G) :
    maximalToBase data (maximalGroupCStarGenerator G g) =
      ((baseUnitaryHom data g : unitary (baseAlgebra data)) :
        baseAlgebra data) :=
  maximalGroupCStarLift_generator G (baseUnitaryHom data) g

theorem maximalToBase_denseRange
    (data : CoronaConjugator G S T phi A X) :
    DenseRange (maximalToBase data) := by
  have hspan : Submodule.span ℂ
      (Set.range (fun g : G ↦
        ((baseUnitaryHom data g : unitary (baseAlgebra data)) :
          baseAlgebra data))) ≤ Set.range (maximalToBase data) := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem d hd =>
        obtain ⟨g, rfl⟩ := hd
        exact ⟨maximalGroupCStarGenerator G g, maximalToBase_generator data g⟩
    | zero => exact ⟨0, map_zero _⟩
    | add x y _ _ hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact ⟨a + b, map_add _ _ _⟩
    | smul c x _ hx =>
        obtain ⟨a, rfl⟩ := hx
        exact ⟨c • a, map_smul _ _ _⟩
  exact (groupGeneratedCStar_dense_span (coronaRepresentation data)).mono hspan

theorem maximalToBase_surjective
    (data : CoronaConjugator G S T phi A X) :
    Function.Surjective (maximalToBase data) := by
  rw [← Set.range_eq_univ]
  calc
    Set.range (maximalToBase data) = closure (Set.range (maximalToBase data)) :=
      (isClosed_range_starAlgHom (maximalToBase data)).closure_eq.symm
    _ = Set.univ := (maximalToBase_denseRange data).closure_eq

/-- The pulled-back base trace is the canonical maximal trace. -/
theorem baseTrace_comp_maximalToBase
    (data : CoronaConjugator G S T phi A X) :
    compContinuousFunctional G (maximalToBase data)
        (tracialStateCLM (baseTrace data)) = canonicalMaximalTrace G := by
  apply canonicalMaximalTrace_eq_of_generator G
  · change baseTrace data
      (maximalToBase data (maximalGroupCStarGenerator G 1)) = 1
    rw [maximalToBase_generator]
    simp
  · intro g hg
    change baseTrace data
      (maximalToBase data (maximalGroupCStarGenerator G g)) = 0
    rw [maximalToBase_generator]
    exact baseTrace_regular data g hg

end


end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
