import GroupApproximation.Analysis.ShulmanTraceClasses
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Pointwise weak-star topology on tracial states

The bundled `TracialState` type in this project has no topology in Mathlib.
We equip it with the topology induced by all evaluation maps.  This is the
literal pointwise (weak-star on a norm-bounded state space) topology used by
the trace simplex.
-/

namespace GroupApproximation

noncomputable section

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

/-- The evaluation embedding of bundled tracial states into the product of
copies of `ℂ`. -/
def tracialStateEvaluation : TracialState A → (A → ℂ) :=
  fun tau a ↦ tau a

/-- The pointwise weak-star topology on bundled tracial states. -/
instance tracialStateWeakStarTopology : TopologicalSpace (TracialState A) :=
  TopologicalSpace.induced (tracialStateEvaluation (A := A)) inferInstance

/-- Evaluation at every algebra element is weak-star continuous. -/
theorem continuous_tracialState_apply (a : A) :
    Continuous (fun tau : TracialState A ↦ tau a) := by
  exact (continuous_apply a).comp continuous_induced_dom

/-- Bundled tracial states are determined by their pointwise values. -/
theorem tracialStateEvaluation_injective :
    Function.Injective (tracialStateEvaluation (A := A)) := by
  intro tau sigma h
  cases tau with
  | mk f hf1 hfp hft =>
    cases sigma with
    | mk g hg1 hgp hgt =>
      have hfg : f = g := LinearMap.ext fun a ↦ congrFun h a
      subst g
      rfl

/-- The evaluation map is a topological embedding by construction. -/
theorem isEmbedding_tracialStateEvaluation :
    Topology.IsEmbedding (tracialStateEvaluation (A := A)) :=
  ⟨⟨rfl⟩, tracialStateEvaluation_injective⟩

/-- The pointwise weak-star trace space is Hausdorff. -/
instance tracialStateWeakStarT2Space : T2Space (TracialState A) :=
  isEmbedding_tracialStateEvaluation.t2Space

end

end GroupApproximation
