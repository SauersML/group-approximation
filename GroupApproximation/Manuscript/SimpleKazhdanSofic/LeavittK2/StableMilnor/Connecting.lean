import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableMilnor.RelativeKOne
import GroupApproximation.Meta.AxiomGuard

/-!
# The connecting map `K₂(S) → K₁(R, ker f)`

Lane sk-leavitt-16, fourth module.  Milnor §6: for surjective `f : R →+* S`, an element
`y ∈ K₂(S) ⊆ St(S)` lifts to `s ∈ St(R)` (`stableRingMap_surjective`), the matrix
`φ(s) ∈ GL(R)` lies in `GL(R, ker f)`, and `∂ y = [φ(s)] ∈ K₁(R, ker f)`.

* **Well-definedness** (`stableProjection_mem_relativeElementaryColim_of_stableRingMap_eq_one`):
  if `f_* s = 1` then `φ(s) ∈ E'(R, ker f)`.  The relation `f_* s = 1` in the direct limit
  already holds at some finite rank `m`, where `SteinbergGroup.ringMap_ker_eq_kernelRootClosure`
  writes the kernel as the normal closure of the roots `x_{ij}(a)`, `f a = 0`; their images
  are relative elementary units.  This replaces Milnor's double-ring argument.
* The map is built without choices of lifts: `P = f_*⁻¹ K₂(S) ≤ St(R)`, `liftToK2 : P ↠ K₂(S)`,
  and `∂ = (P ⧸ ker liftToK2 → K₁(R, ker f)) ∘ (P ⧸ ker liftToK2 ≃* K₂(S))⁻¹`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation GroupApproximation.AlgebraicK

section Connecting

variable {R S : Type*} [Ring R] [Ring S]

/-- **Well-definedness of the connecting map**: an element of `St(R)` dying in `St(S)` projects
into `E'(R, ker f)`. -/
theorem stableProjection_mem_relativeElementaryColim_of_stableRingMap_eq_one
    (f : R →+* S) (hf : Function.Surjective f) {s : stableSteinberg R}
    (hs : stableRingMap f s = 1) :
    stableProjection R s ∈ relativeElementaryColim f := by
  obtain ⟨n, t, rfl⟩ := DirectLimit.exists_eq_mk (f := steinbergTransition R) s
  have hs' : (⟦⟨n, SteinbergGroup.ringMap f t⟩⟧ : stableSteinberg S) = 1 := hs
  obtain ⟨m, hnm, hm⟩ := (DirectLimit.exists_eq_one (f := steinbergTransition S)
    (⟨n, SteinbergGroup.ringMap f t⟩ : Σ k : ℕ, SteinbergGroup (Fin k) S)).mp hs'
  have hker : steinbergTransition R n m hnm t ∈ (SteinbergGroup.ringMap (I := Fin m) f).ker :=
    MonoidHom.mem_ker.mpr ((steinbergTransition_ringMap f hnm t).symm.trans hm)
  rw [SteinbergGroup.ringMap_ker_eq_kernelRootClosure (I := Fin m) f hf] at hker
  have hle : SteinbergGroup.kernelRootClosure (I := Fin m) f
      ≤ (relativeElementaryColim f).comap (stableProjectionComponent R m) := by
    apply Subgroup.normalClosure_le_normal
    rintro g ⟨i, j, hij, a, ha, rfl⟩
    show stableProjectionComponent R m (SteinbergGroup.x i j hij a) ∈ relativeElementaryColim f
    rw [stableProjectionComponent_x]
    exact glColimOf_elementaryUnit_mem_relativeElementaryColim f i j hij ha
  have hmem := hle hker
  rw [Subgroup.mem_comap, stableProjectionComponent_transition] at hmem
  exact hmem

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableProjection_mem_relativeElementaryColim_of_stableRingMap_eq_one

/-- `P = f_*⁻¹ K₂(S)`: the lifts to `St(R)` of elements of `K₂(S)`. -/
noncomputable def stableK2Lifts (f : R →+* S) : Subgroup (stableSteinberg R) :=
  (stableK2 S).comap (stableRingMap f)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableK2Lifts

theorem stableProjection_mem_relativeGL_of_mem_stableK2Lifts (f : R →+* S)
    {s : stableSteinberg R} (hs : s ∈ stableK2Lifts f) :
    stableProjection R s ∈ relativeGL f := by
  refine MonoidHom.mem_ker.mpr ?_
  rw [← stableProjection_stableRingMap]
  exact MonoidHom.mem_ker.mp (Subgroup.mem_comap.mp hs)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableProjection_mem_relativeGL_of_mem_stableK2Lifts

/-- `P → K₂(S)`, `s ↦ f_* s`. -/
noncomputable def liftToK2 (f : R →+* S) : stableK2Lifts f →* stableK2 S :=
  ((stableRingMap f).comp (stableK2Lifts f).subtype).codRestrict (stableK2 S)
    (fun p => Subgroup.mem_comap.mp p.2)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.liftToK2

/-- `P → GL(R, ker f)`, `s ↦ φ(s)`. -/
noncomputable def liftToRelativeGL (f : R →+* S) : stableK2Lifts f →* relativeGL f :=
  ((stableProjection R).comp (stableK2Lifts f).subtype).codRestrict (relativeGL f)
    (fun p => stableProjection_mem_relativeGL_of_mem_stableK2Lifts f p.2)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.liftToRelativeGL

theorem liftToK2_surjective (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (liftToK2 f) := by
  rintro ⟨y, hy⟩
  obtain ⟨s, rfl⟩ := stableRingMap_surjective f hf y
  exact ⟨⟨s, hy⟩, rfl⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.liftToK2_surjective

/-- The kernel of `P ↠ K₂(S)` maps to `1` in `K₁(R, ker f)`. -/
theorem liftToK2_ker_le (f : R →+* S) (hf : Function.Surjective f) :
    (liftToK2 f).ker
      ≤ ((QuotientGroup.mk' ((relativeElementaryColim f).subgroupOf (relativeGL f))).comp
          (liftToRelativeGL f)).ker := by
  intro p hp
  have hp1 : stableRingMap f (p : stableSteinberg R) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hp)
  have hmem : liftToRelativeGL f p ∈ (relativeElementaryColim f).subgroupOf (relativeGL f) :=
    Subgroup.mem_subgroupOf.mpr
      (stableProjection_mem_relativeElementaryColim_of_stableRingMap_eq_one f hf hp1)
  exact MonoidHom.mem_ker.mpr ((QuotientGroup.eq_one_iff (liftToRelativeGL f p)).mpr hmem)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.liftToK2_ker_le

/-- **The connecting map** `∂ : K₂(S) → K₁(R, ker f)` of Milnor §6. -/
noncomputable def connecting (f : R →+* S) (hf : Function.Surjective f) :
    stableK2 S →* relativeKOne f :=
  (QuotientGroup.lift (liftToK2 f).ker
      ((QuotientGroup.mk' ((relativeElementaryColim f).subgroupOf (relativeGL f))).comp
        (liftToRelativeGL f))
      (liftToK2_ker_le f hf)).comp
    (QuotientGroup.quotientKerEquivOfSurjective (liftToK2 f)
      (liftToK2_surjective f hf)).symm.toMonoidHom

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.connecting

/-- `∂ (f_* s) = [φ(s)]` for every lift `s ∈ P`. -/
theorem connecting_apply (f : R →+* S) (hf : Function.Surjective f) (p : stableK2Lifts f) :
    connecting f hf (liftToK2 f p) = ((liftToRelativeGL f p : relativeGL f) : relativeKOne f) := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective (liftToK2 f)
      (liftToK2_surjective f hf)).symm (liftToK2 f p)
        = (p : ↥(stableK2Lifts f) ⧸ (liftToK2 f).ker) := by
    rw [MulEquiv.symm_apply_eq]
    exact (QuotientGroup.kerLift_mk (liftToK2 f) p).symm
  change QuotientGroup.lift (liftToK2 f).ker
      ((QuotientGroup.mk' ((relativeElementaryColim f).subgroupOf (relativeGL f))).comp
        (liftToRelativeGL f))
      (liftToK2_ker_le f hf)
      ((QuotientGroup.quotientKerEquivOfSurjective (liftToK2 f)
        (liftToK2_surjective f hf)).symm (liftToK2 f p)) = _
  rw [h]
  exact QuotientGroup.lift_mk _ (liftToK2_ker_le f hf) p

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.connecting_apply

end Connecting

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
