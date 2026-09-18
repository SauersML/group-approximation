import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Polar.AbsComplete
import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Polar.AbsCFC
import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Polar.AbsStatement
import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Approx
import GroupApproximation.Meta.AxiomGuard

/-!
# Absolute value, lane `nm-tww-17a`: `AbsOperatorStatement` holds

Let `E` be complete and `T : E → F` adjointable. Then:
* `T⋆T` is bounded, by the closed graph theorem `isBounded_of_isCompleteModule`. So it is an
  element `opTT T hE` of the C⋆-algebra `adjSub E`, and it is self-adjoint.
* Positivity test: suppose `b⋆ (T⋆T) b = -(c⋆ c)`. Pairing with `y` gives
  `⟨T b y, T b y⟩ = -⟨c y, c y⟩`, and both inner products are `≥ 0`. So `⟨c y, c y⟩ = 0`, hence
  `c y = 0` for every `y`, so `c = 0`.
* `exists_isSelfAdjoint_mul_self_eq_of_test` therefore gives a self-adjoint `s` with
  `s * s = T⋆T`, and `S := s` satisfies both clauses:
  * `⟨S x, S x⟩ = ⟨x, S S x⟩ = ⟨x, T⋆T x⟩ = ⟨T x, T x⟩`;
  * `T⋆T x = S (S x)` lies in the range of `S`, so it is approximated exactly.

No order instance on `adjSub E` appears in any statement here. The spectral order is used only
inside `AbsCFC`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp

open GroupApproximation.HilbertModule

universe v

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {E F : CStarModule.{v, v} B}

/-- `T⋆T`, as an element of `adjSub E`. -/
noncomputable def opTT (T : Adjointable E F) (hE : IsCompleteModule E) : adjSub E :=
  ⟨clmOf ((Adjointable.adjoint T).comp T)
      (Classical.choose_spec
        (isBounded_of_isCompleteModule ((Adjointable.adjoint T).comp T) hE hE)).2,
    clmOf_mem _ _⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.opTT

theorem opTT_apply (T : Adjointable E F) (hE : IsCompleteModule E) (x : E.carrier) :
    ((opTT T hE : adjSub E) : E.carrier →L[ℂ] E.carrier) x = T.adj (T.toFun x) :=
  rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.opTT_apply

theorem star_opTT (T : Adjointable E F) (hE : IsCompleteModule E) :
    star (opTT T hE) = opTT T hE :=
  ext_apply fun y =>
    star_apply_eq (opTT T hE) (fun z => T.adj (T.toFun z))
      (fun x z => by
        change E.inner (T.adj (T.toFun x)) z = E.inner x (T.adj (T.toFun z))
        rw [← T.inner_adj' z (T.toFun x), T.inner_adj x (T.toFun z)]) y

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.star_opTT

/-- **The positivity test** for `T⋆T`, stated with inner products only. -/
theorem test_opTT (T : Adjointable E F) (hE : IsCompleteModule E) :
    ∀ b c : adjSub E, star b * opTT T hE * b = -(star c * c) → c = 0 := by
  intro b c h
  refine ext_apply fun y => ?_
  have hy := congrArg (fun g : adjSub E => E.inner y ((g : E.carrier →L[ℂ] E.carrier) y)) h
  change E.inner y (((star b : adjSub E) : E.carrier →L[ℂ] E.carrier)
      (T.adj (T.toFun ((b : E.carrier →L[ℂ] E.carrier) y))))
    = E.inner y (-(((star c : adjSub E) : E.carrier →L[ℂ] E.carrier)
      ((c : E.carrier →L[ℂ] E.carrier) y))) at hy
  have hneg : ∀ w : E.carrier, E.inner y (-w) = -E.inner y w := by
    intro w
    rw [← zero_sub w, E.inner_sub_right, E.inner_zero_right, zero_sub]
  rw [hneg, ← inner_apply_star b, ← T.inner_adj, ← inner_apply_star c] at hy
  have hnp : E.inner ((c : E.carrier →L[ℂ] E.carrier) y) ((c : E.carrier →L[ℂ] E.carrier) y)
      ≤ 0 := by
    have h0 := F.inner_self_nonneg (T.toFun ((b : E.carrier →L[ℂ] E.carrier) y))
    rw [hy] at h0
    exact neg_nonneg.mp h0
  have hz : E.inner ((c : E.carrier →L[ℂ] E.carrier) y) ((c : E.carrier →L[ℂ] E.carrier) y)
      = 0 :=
    le_antisymm hnp (E.inner_self_nonneg _)
  exact E.inner_self_eq_zero _ hz

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.test_opTT

/-- **`T⋆T` has a self-adjoint square root in `adjSub E`.** -/
theorem exists_sqrt_opTT (T : Adjointable E F) (hE : IsCompleteModule E) :
    ∃ s : adjSub E, star s = s ∧ s * s = opTT T hE := by
  letI : CStarAlgebra (adjSub E) := cstarAlgebra hE
  obtain ⟨s, hs, hss⟩ := exists_isSelfAdjoint_mul_self_eq_of_test (A := adjSub E)
    (a := opTT T hE) (star_opTT T hE) (test_opTT T hE)
  exact ⟨s, hs, hss⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.exists_sqrt_opTT

end GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab

open GroupApproximation.HilbertModule
open GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp

universe v

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **The absolute value exists**: `S = |T| = √(T⋆T)`. -/
theorem absOperatorStatement_holds : AbsOperatorStatement B := by
  intro E F T hE
  obtain ⟨s, hs, hss⟩ := exists_sqrt_opTT T hE
  have h2 : ∀ x : E.carrier, (s : E.carrier →L[ℂ] E.carrier) ((s : E.carrier →L[ℂ] E.carrier) x)
      = T.adj (T.toFun x) :=
    fun x => congrArg (fun g : adjSub E => (g : E.carrier →L[ℂ] E.carrier) x) hss
  refine ⟨toAdj s.2, fun x => ?_, fun x => ?_⟩
  · change E.inner ((s : E.carrier →L[ℂ] E.carrier) x) ((s : E.carrier →L[ℂ] E.carrier) x)
      = F.inner (T.toFun x) (T.toFun x)
    rw [inner_apply_star s, hs, h2]
    exact (T.inner_adj x (T.toFun x)).symm
  · have h := isApprox_apply (toAdj s.2) ((s : E.carrier →L[ℂ] E.carrier) x)
    change IsApprox (toAdj s.2) ((s : E.carrier →L[ℂ] E.carrier)
      ((s : E.carrier →L[ℂ] E.carrier) x)) at h
    rwa [h2] at h

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.absOperatorStatement_holds

end GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab
