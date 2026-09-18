import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Polar.AbsStar
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.Sequences
import GroupApproximation.Meta.AxiomGuard

/-!
# Absolute value, lane `nm-tww-17a`: `adjSub E` is a unital C⋆-algebra

Assume `E` is complete. Then `E.carrier →L[ℂ] E.carrier` is complete, and `adjSub E` is closed in
it. Proof: let `u n → f` with each `u n` adjointable.
* The adjoints `u n⋆` form a Cauchy sequence, because
  `‖u m⋆ - u n⋆‖ = ‖(u m - u n)⋆‖ ≤ ‖u m - u n‖`. So they converge to some `g`.
* Passing to the limit in `⟨u n x, y⟩ = ⟨x, u n⋆ y⟩` gives `⟨f x, y⟩ = ⟨x, g y⟩`.

Together with `AbsStar`, `cstarAlgebra hE` makes `adjSub E` a `CStarAlgebra`. It is a
`def`, not an instance, because it depends on the proof `hE`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp

open GroupApproximation.HilbertModule Filter Topology

universe v

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {E : CStarModule.{v, v} B}

/-- On a complete module, the adjointable bounded operators form a closed set. -/
theorem isClosed_adjSub (hE : IsCompleteModule E) :
    IsClosed (adjSub E : Set (E.carrier →L[ℂ] E.carrier)) := by
  haveI : CompleteSpace E.carrier := completeSpace_of_isCompleteModule hE
  refine IsSeqClosed.isClosed fun u f hu hlim => ?_
  have hu' : ∀ n, u n ∈ adjSub E := hu
  have hc : CauchySeq fun n => adjCLM (hu' n) := by
    refine Metric.cauchySeq_iff'.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hlim.cauchySeq ε hε
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [dist_eq_norm_sub] at h
    rw [dist_eq_norm_sub, ← adjCLM_sub (hu' n) (hu' N) (sub_mem (hu' n) (hu' N))]
    exact lt_of_le_of_lt (adjCLM_norm_le _) h
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hc
  refine (mem_adjSub_iff E f).mpr ⟨g, fun x y => ?_⟩
  have h1 : Tendsto (fun n => E.inner (u n x) y) atTop (𝓝 (E.inner (f x) y)) :=
    tendsto_inner_left_of_tendsto (hlim.eval_const x) y
  have h2 : Tendsto (fun n => E.inner x (adjCLM (hu' n) y)) atTop (𝓝 (E.inner x (g y))) :=
    tendsto_inner_right_of_tendsto (hg.eval_const y) x
  have h3 : (fun n => E.inner (u n x) y) = fun n => E.inner x (adjCLM (hu' n) y) :=
    funext fun n => inner_apply_adjCLM (hu' n) x y
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.isClosed_adjSub

theorem completeSpace_adjSub (hE : IsCompleteModule E) : CompleteSpace (adjSub E) := by
  haveI : CompleteSpace E.carrier := completeSpace_of_isCompleteModule hE
  exact IsClosed.completeSpace_coe (hs := isClosed_adjSub hE)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.completeSpace_adjSub

/-- **`adjSub E` is a C⋆-algebra** when `E` is complete. -/
@[reducible] noncomputable def cstarAlgebra (hE : IsCompleteModule E) :
    CStarAlgebra (adjSub E) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := completeSpace_adjSub hE
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.cstarAlgebra

end GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp
