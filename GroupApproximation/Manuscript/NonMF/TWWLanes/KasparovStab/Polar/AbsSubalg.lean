import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Polar.AbsNormed
import Mathlib.Analysis.Normed.Operator.NormedSpace
import GroupApproximation.Meta.AxiomGuard

/-!
# Absolute value, lane `nm-tww-17a`: the subalgebra of adjointable bounded operators

With the scoped normed instances of `AbsNormed`, `E.carrier →L[ℂ] E.carrier` is a normed
algebra. `adjSub E` is its subalgebra of operators that have an adjoint *function*. Contents:
* `toAdj`: a member of `adjSub E`, read as an `Adjointable E E`.
* `adjCLM`: its adjoint, a bounded operator (`‖f⋆‖ ≤ ‖f‖`), which lies in `adjSub E` again.
* `clmOf`: a bounded `Adjointable E E`, read as a member of `adjSub E`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp

open GroupApproximation.HilbertModule

universe v

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A bounded operator `f` has an adjoint function. -/
def IsAdj (E : CStarModule.{v, v} B) (f : E.carrier →L[ℂ] E.carrier) : Prop :=
  ∃ g : E.carrier → E.carrier, ∀ x y : E.carrier, E.inner (f x) y = E.inner x (g y)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.IsAdj

theorem isAdj_mul {E : CStarModule.{v, v} B} {f g : E.carrier →L[ℂ] E.carrier}
    (hf : IsAdj E f) (hg : IsAdj E g) : IsAdj E (f * g) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  refine ⟨fun y => g' (f' y), fun x y => ?_⟩
  change E.inner (f (g x)) y = E.inner x (g' (f' y))
  rw [hf', hg']

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.isAdj_mul

theorem isAdj_add {E : CStarModule.{v, v} B} {f g : E.carrier →L[ℂ] E.carrier}
    (hf : IsAdj E f) (hg : IsAdj E g) : IsAdj E (f + g) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  refine ⟨fun y => f' y + g' y, fun x y => ?_⟩
  change E.inner (f x + g x) y = E.inner x (f' y + g' y)
  rw [E.inner_add_left, E.inner_add_right, hf', hg']

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.isAdj_add

theorem isAdj_algebraMap (E : CStarModule.{v, v} B) (c : ℂ) :
    IsAdj E (algebraMap ℂ (E.carrier →L[ℂ] E.carrier) c) := by
  refine ⟨fun y => (starRingEnd ℂ c) • y, fun x y => ?_⟩
  rw [Algebra.algebraMap_eq_smul_one]
  change E.inner (c • x) y = E.inner x ((starRingEnd ℂ c) • y)
  rw [E.inner_smul_left, E.inner_smul_right]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.isAdj_algebraMap

theorem isAdj_one (E : CStarModule.{v, v} B) : IsAdj E (1 : E.carrier →L[ℂ] E.carrier) :=
  ⟨fun y => y, fun _ _ => rfl⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.isAdj_one

theorem isAdj_zero (E : CStarModule.{v, v} B) : IsAdj E (0 : E.carrier →L[ℂ] E.carrier) := by
  refine ⟨fun _ => 0, fun x y => ?_⟩
  change E.inner 0 y = E.inner x 0
  rw [E.inner_zero_left, E.inner_zero_right]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.isAdj_zero

/-- The bounded operators on `E` that have an adjoint function. -/
noncomputable def adjSub (E : CStarModule.{v, v} B) :
    Subalgebra ℂ (E.carrier →L[ℂ] E.carrier) where
  carrier := {f | IsAdj E f}
  mul_mem' hf hg := isAdj_mul hf hg
  one_mem' := isAdj_one E
  add_mem' hf hg := isAdj_add hf hg
  zero_mem' := isAdj_zero E
  algebraMap_mem' c := isAdj_algebraMap E c

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.adjSub

theorem mem_adjSub_iff (E : CStarModule.{v, v} B) (f : E.carrier →L[ℂ] E.carrier) :
    f ∈ adjSub E ↔ IsAdj E f :=
  Iff.rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.mem_adjSub_iff

variable {E : CStarModule.{v, v} B}

/-- A member of `adjSub E`, read as an adjointable operator. -/
noncomputable def toAdj {f : E.carrier →L[ℂ] E.carrier} (hf : f ∈ adjSub E) :
    Adjointable E E where
  toFun := f
  adj := Classical.choose ((mem_adjSub_iff E f).mp hf)
  inner_adj := Classical.choose_spec ((mem_adjSub_iff E f).mp hf)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.toAdj

theorem toAdj_isBoundedBy {f : E.carrier →L[ℂ] E.carrier} (hf : f ∈ adjSub E) :
    (toAdj hf).IsBoundedBy ‖f‖ :=
  fun x => f.le_opNorm x

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.toAdj_isBoundedBy

/-- An adjointable operator, read as a linear map. -/
def linOf (S : Adjointable E E) : E.carrier →ₗ[ℂ] E.carrier where
  toFun := S.toFun
  map_add' := S.map_add
  map_smul' := fun c x => by
    rw [RingHom.id_apply]
    exact S.map_smul c x

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.linOf

/-- A bounded adjointable operator, read as a continuous linear map. -/
noncomputable def clmOf (S : Adjointable E E) {C : ℝ} (hC : S.IsBoundedBy C) :
    E.carrier →L[ℂ] E.carrier :=
  (linOf S).mkContinuous C hC

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.clmOf

theorem clmOf_apply (S : Adjointable E E) {C : ℝ} (hC : S.IsBoundedBy C) (x : E.carrier) :
    clmOf S hC x = S.toFun x :=
  rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.clmOf_apply

theorem clmOf_mem (S : Adjointable E E) {C : ℝ} (hC : S.IsBoundedBy C) :
    clmOf S hC ∈ adjSub E :=
  (mem_adjSub_iff E _).mpr ⟨S.adj, S.inner_adj⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.clmOf_mem

/-- The adjoint of a member of `adjSub E`, as a bounded operator. -/
noncomputable def adjCLM {f : E.carrier →L[ℂ] E.carrier} (hf : f ∈ adjSub E) :
    E.carrier →L[ℂ] E.carrier :=
  clmOf (Adjointable.adjoint (toAdj hf)) ((toAdj_isBoundedBy hf).adjoint (norm_nonneg f))

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.adjCLM

theorem inner_apply_adjCLM {f : E.carrier →L[ℂ] E.carrier} (hf : f ∈ adjSub E)
    (x y : E.carrier) : E.inner (f x) y = E.inner x (adjCLM hf y) :=
  (toAdj hf).inner_adj x y

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.inner_apply_adjCLM

theorem inner_adjCLM_apply {f : E.carrier →L[ℂ] E.carrier} (hf : f ∈ adjSub E)
    (x y : E.carrier) : E.inner (adjCLM hf x) y = E.inner x (f y) :=
  ((toAdj hf).inner_adj' y x).symm

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.inner_adjCLM_apply

theorem adjCLM_eq {f : E.carrier →L[ℂ] E.carrier} (hf : f ∈ adjSub E)
    (g : E.carrier → E.carrier) (hg : ∀ x y : E.carrier, E.inner (f x) y = E.inner x (g y))
    (y : E.carrier) : adjCLM hf y = g y :=
  ((toAdj hf).adj_unique g hg y).symm

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.adjCLM_eq

theorem adjCLM_mem {f : E.carrier →L[ℂ] E.carrier} (hf : f ∈ adjSub E) :
    adjCLM hf ∈ adjSub E :=
  (mem_adjSub_iff E _).mpr ⟨f, inner_adjCLM_apply hf⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.adjCLM_mem

theorem adjCLM_norm_le {f : E.carrier →L[ℂ] E.carrier} (hf : f ∈ adjSub E) :
    ‖adjCLM hf‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
    (fun y => (toAdj_isBoundedBy hf).adjoint (norm_nonneg f) y)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.adjCLM_norm_le

theorem adjCLM_sub {f₁ f₂ : E.carrier →L[ℂ] E.carrier} (h₁ : f₁ ∈ adjSub E)
    (h₂ : f₂ ∈ adjSub E) (h₁₂ : f₁ - f₂ ∈ adjSub E) :
    adjCLM h₁₂ = adjCLM h₁ - adjCLM h₂ := by
  refine ContinuousLinearMap.ext fun y => ?_
  refine adjCLM_eq h₁₂ (fun z => adjCLM h₁ z - adjCLM h₂ z) (fun x z => ?_) y
  change E.inner (f₁ x - f₂ x) z = E.inner x (adjCLM h₁ z - adjCLM h₂ z)
  rw [E.inner_sub_left, E.inner_sub_right, inner_apply_adjCLM h₁, inner_apply_adjCLM h₂]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.adjCLM_sub

end GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp
