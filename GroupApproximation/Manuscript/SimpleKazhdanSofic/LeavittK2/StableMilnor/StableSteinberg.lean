import GroupApproximation.Steinberg.QuotientExactness
import GroupApproximation.KOne.MoritaKOne
import GroupApproximation.KOne.AlgebraicKOneFunctor
import Mathlib.Data.Fin.Embedding
import GroupApproximation.Meta.AxiomGuard

/-!
# The stable Steinberg group `St(R)` and stable `K₂(R)`

Lane sk-leavitt-16, first module.  Milnor, *Introduction to algebraic K-theory*, §5–§6.

* `steinbergTransition R n m h : St_n(R) →* St_m(R)` is the relabelling of generators
  along `Fin.castLE h` (`SteinbergGroup.indexMap (Fin.castLEEmb h)`), the same convention
  as `LeavittK2/StableReduction/StableKTwo.lean`.
* `steinbergDirectedSystem` packages the two functoriality laws, checked on generators.
* `stableSteinberg R` is Mathlib's `DirectLimit` of that system, so the group structure is
  inherited, exactly as `ClassicalGLColim R` is built in `KOne/ClassicalKOne.lean`.
* `stableProjection R : St(R) →* GL(R)` is assembled from the rank-`n` projections
  `St_n(R) → E_n(R) ⊆ GL_n(R) → GL(R)`; compatibility is `glStab_elementaryUnit` on
  generators.
* `stableK2 R` is its kernel; `stableK2_eq_ker_toElementary` identifies it with the kernel of
  the corestriction `St(R) →* E(R)` named in the lane.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation GroupApproximation.AlgebraicK

section Stable

variable (R : Type*) [Ring R]

/-- The stabilization `St_n(R) →* St_m(R)` along `Fin.castLE`. -/
def steinbergTransition (n m : ℕ) (h : n ≤ m) :
    SteinbergGroup (Fin n) R →* SteinbergGroup (Fin m) R :=
  SteinbergGroup.indexMap (Fin.castLEEmb h)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.steinbergTransition

theorem steinbergTransition_x {n m : ℕ} (h : n ≤ m) (i j : Fin n) (hij : i ≠ j) (a : R) :
    steinbergTransition R n m h (SteinbergGroup.x i j hij a)
      = SteinbergGroup.x (Fin.castLE h i) (Fin.castLE h j) (castLE_ne h hij) a :=
  SteinbergGroup.indexMap_x (R := R) (Fin.castLEEmb h) i j hij a

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.steinbergTransition_x

/-- The stabilizations form a directed system; both laws are checked on generators, where
they are the identities `castLE le_rfl i = i` and `castLE hjk (castLE hij i) = castLE _ i`
(both definitional). -/
instance steinbergDirectedSystem :
    DirectedSystem (fun n : ℕ => SteinbergGroup (Fin n) R)
      (fun i j h => ⇑(steinbergTransition R i j h)) where
  map_self := fun n t => by
    have hid : steinbergTransition R n n le_rfl = MonoidHom.id _ := by
      apply PresentedGroup.ext
      rintro ⟨a, b, hab, c⟩
      exact (steinbergTransition_x R le_rfl a b hab c).trans rfl
    exact DFunLike.congr_fun hid t
  map_map := fun k j i hij hjk t => by
    have hcomp : (steinbergTransition R j k hjk).comp (steinbergTransition R i j hij)
        = steinbergTransition R i k (hij.trans hjk) := by
      apply PresentedGroup.ext
      rintro ⟨a, b, hab, c⟩
      exact (congrArg (steinbergTransition R j k hjk)
          (steinbergTransition_x R hij a b hab c)).trans
        ((steinbergTransition_x R hjk _ _ _ c).trans
          (steinbergTransition_x R (hij.trans hjk) a b hab c).symm)
    exact DFunLike.congr_fun hcomp t

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.steinbergDirectedSystem

/-- **The stable Steinberg group** `St(R) = colim_n St_n(R)`. -/
noncomputable abbrev stableSteinberg :=
  DirectLimit (fun n : ℕ => SteinbergGroup (Fin n) R) (steinbergTransition R)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableSteinberg

/-- The canonical map `St_n(R) →* St(R)`. -/
noncomputable def stableSteinbergOf (n : ℕ) :
    SteinbergGroup (Fin n) R →* stableSteinberg R where
  toFun t := ⟦⟨n, t⟩⟧
  map_one' := by
    show (⟦⟨n, 1⟩⟧ : stableSteinberg R) = 1
    exact (DirectLimit.one_def (f := steinbergTransition R) n).symm
  map_mul' u v := by
    show (⟦⟨n, u * v⟩⟧ : stableSteinberg R) = ⟦⟨n, u⟩⟧ * ⟦⟨n, v⟩⟧
    exact (DirectLimit.mul_def (f := steinbergTransition R) n u v).symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableSteinbergOf

theorem stableSteinbergOf_apply (n : ℕ) (t : SteinbergGroup (Fin n) R) :
    stableSteinbergOf R n t = ⟦⟨n, t⟩⟧ := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableSteinbergOf_apply

/-- The rank-`n` component of the stable projection: `St_n(R) → E_n(R) ⊆ GL_n(R) → GL(R)`. -/
noncomputable def stableProjectionComponent (n : ℕ) :
    SteinbergGroup (Fin n) R →* ClassicalGLColim R :=
  (glColimOf R n).comp ((elementaryGroup (Fin n) R).subtype.comp SteinbergGroup.projection)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableProjectionComponent

theorem stableProjectionComponent_x (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : R) :
    stableProjectionComponent R n (SteinbergGroup.x i j hij a)
      = glColimOf R n (elementaryUnit i j hij a) := by
  change glColimOf R n ((SteinbergGroup.projection (SteinbergGroup.x i j hij a) :
      elementaryGroup (Fin n) R) : (Matrix (Fin n) (Fin n) R)ˣ) = _
  rw [SteinbergGroup.projection_x, elementaryRoot_val]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableProjectionComponent_x

/-- The components are compatible with the stabilizations. -/
theorem stableProjectionComponent_transition {n m : ℕ} (h : n ≤ m)
    (t : SteinbergGroup (Fin n) R) :
    stableProjectionComponent R m (steinbergTransition R n m h t)
      = stableProjectionComponent R n t := by
  have hcomp : (stableProjectionComponent R m).comp (steinbergTransition R n m h)
      = stableProjectionComponent R n := by
    apply PresentedGroup.ext
    rintro ⟨i, j, hij, a⟩
    change stableProjectionComponent R m (steinbergTransition R n m h (SteinbergGroup.x i j hij a))
      = stableProjectionComponent R n (SteinbergGroup.x i j hij a)
    rw [steinbergTransition_x, stableProjectionComponent_x, stableProjectionComponent_x,
      ← glStab_elementaryUnit h i j hij a, glColimOf_glStab]
  exact DFunLike.congr_fun hcomp t

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableProjectionComponent_transition

/-- The underlying function of `stableProjection`. -/
noncomputable def stableProjectionFun : stableSteinberg R → ClassicalGLColim R :=
  DirectLimit.lift (steinbergTransition R) (fun n t => stableProjectionComponent R n t)
    (fun _ _ h t => (stableProjectionComponent_transition R h t).symm)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableProjectionFun

/-- **The stable projection** `St(R) →* GL(R)`. -/
noncomputable def stableProjection : stableSteinberg R →* ClassicalGLColim R where
  toFun := stableProjectionFun R
  map_one' := by
    have h0 : (1 : stableSteinberg R) = stableSteinbergOf R 0 1 := (map_one _).symm
    rw [h0]
    exact map_one (stableProjectionComponent R 0)
  map_mul' s t := by
    obtain ⟨n, u, v, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ (f := steinbergTransition R) s t
    have hu : (⟦⟨n, u⟩⟧ : stableSteinberg R) = stableSteinbergOf R n u := rfl
    have hv : (⟦⟨n, v⟩⟧ : stableSteinberg R) = stableSteinbergOf R n v := rfl
    rw [hu, hv, ← map_mul (stableSteinbergOf R n)]
    exact map_mul (stableProjectionComponent R n) u v

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableProjection

theorem stableProjection_of (n : ℕ) (t : SteinbergGroup (Fin n) R) :
    stableProjection R (stableSteinbergOf R n t) = stableProjectionComponent R n t := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableProjection_of

/-- **Stable `K₂(R)`**: the kernel of `St(R) → GL(R)`. -/
noncomputable def stableK2 : Subgroup (stableSteinberg R) :=
  (stableProjection R).ker

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableK2

/-- The stable projection lands in `E(R) = elementaryColim R`. -/
theorem stableProjection_mem_elementaryColim (s : stableSteinberg R) :
    stableProjection R s ∈ elementaryColim R := by
  obtain ⟨n, t, rfl⟩ := DirectLimit.exists_eq_mk (f := steinbergTransition R) s
  exact glColimOf_mem_elementaryColim R (SteinbergGroup.projection t).2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableProjection_mem_elementaryColim

/-- The corestriction `St(R) →* E(R)` of the lane statement. -/
noncomputable def stableProjectionToElementary : stableSteinberg R →* elementaryColim R :=
  (stableProjection R).codRestrict (elementaryColim R) (stableProjection_mem_elementaryColim R)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableProjectionToElementary

/-- `stableK2 R = ker (St(R) → E(R))`, the lane's definition. -/
theorem stableK2_eq_ker_toElementary :
    stableK2 R = (stableProjectionToElementary R).ker :=
  (MonoidHom.ker_codRestrict _ _ _).symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableK2_eq_ker_toElementary

end Stable

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
