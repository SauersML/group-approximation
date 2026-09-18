import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableMilnor.StableSteinberg
import GroupApproximation.Meta.AxiomGuard

/-!
# Functoriality of `St(R)` and the image of the stable projection

Lane sk-leavitt-16, second module.

* `stableRingMap f : St(R) →* St(S)` for a ring map `f : R →+* S`, via `DirectLimit.map` of the
  coefficientwise maps `SteinbergGroup.ringMap f`; it is surjective when `f` is
  (`stableRingMap_surjective`), from `SteinbergGroup.ringMap_surjective_of_surjective`.
* `stableProjection_stableRingMap`: the square with `glColimMap f` commutes (on generators).
* `stableProjection_range`: the image of `St(R) → GL(R)` is exactly `E(R) = elementaryColim R`,
  from `SteinbergGroup.projection_surjective` at each rank.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation GroupApproximation.AlgebraicK

section Image

variable (R : Type*) [Ring R]

/-- **The image of the stable projection is `E(R)`.** -/
theorem stableProjection_range :
    (stableProjection R).range = elementaryColim R := by
  apply le_antisymm
  · intro g hg
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hg
    exact stableProjection_mem_elementaryColim R s
  · show (⨆ n : ℕ, (elementaryGroup (Fin n) R).map (glColimOf R n)) ≤ _
    refine iSup_le fun n => ?_
    rw [Subgroup.map_le_iff_le_comap]
    intro u hu
    rw [Subgroup.mem_comap]
    obtain ⟨t, ht⟩ := SteinbergGroup.projection_surjective (I := Fin n) (R := R) ⟨u, hu⟩
    refine MonoidHom.mem_range.mpr ⟨stableSteinbergOf R n t, ?_⟩
    exact congrArg (fun p : elementaryGroup (Fin n) R =>
      glColimOf R n (p : (Matrix (Fin n) (Fin n) R)ˣ)) ht

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableProjection_range

theorem mem_range_stableProjection_of_mem_elementaryColim {g : ClassicalGLColim R}
    (hg : g ∈ elementaryColim R) : ∃ s : stableSteinberg R, stableProjection R s = g := by
  rw [← stableProjection_range R] at hg
  exact MonoidHom.mem_range.mp hg

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.mem_range_stableProjection_of_mem_elementaryColim

end Image

section RingMap

variable {R S : Type*} [Ring R] [Ring S]

/-- Coefficient maps commute with the stabilizations. -/
theorem steinbergTransition_ringMap (f : R →+* S) {n m : ℕ} (h : n ≤ m)
    (t : SteinbergGroup (Fin n) R) :
    steinbergTransition S n m h (SteinbergGroup.ringMap f t)
      = SteinbergGroup.ringMap f (steinbergTransition R n m h t) := by
  have hcomp : (steinbergTransition S n m h).comp (SteinbergGroup.ringMap (I := Fin n) f)
      = (SteinbergGroup.ringMap (I := Fin m) f).comp (steinbergTransition R n m h) := by
    apply PresentedGroup.ext
    rintro ⟨i, j, hij, a⟩
    change steinbergTransition S n m h (SteinbergGroup.ringMap f (SteinbergGroup.x i j hij a))
      = SteinbergGroup.ringMap f (steinbergTransition R n m h (SteinbergGroup.x i j hij a))
    rw [SteinbergGroup.ringMap_x, steinbergTransition_x, steinbergTransition_x,
      SteinbergGroup.ringMap_x]
  exact DFunLike.congr_fun hcomp t

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.steinbergTransition_ringMap

/-- The underlying function of `stableRingMap`. -/
noncomputable def stableRingMapFun (f : R →+* S) : stableSteinberg R → stableSteinberg S :=
  DirectLimit.map (steinbergTransition R) (steinbergTransition S)
    (fun n => ⇑(SteinbergGroup.ringMap (I := Fin n) f))
    (fun _ _ h t => steinbergTransition_ringMap f h t)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableRingMapFun

/-- **The map of stable Steinberg groups induced by a ring map.** -/
noncomputable def stableRingMap (f : R →+* S) : stableSteinberg R →* stableSteinberg S where
  toFun := stableRingMapFun f
  map_one' := by
    have h0 : (1 : stableSteinberg R) = stableSteinbergOf R 0 1 := (map_one _).symm
    rw [h0]
    show stableSteinbergOf S 0 (SteinbergGroup.ringMap f 1) = 1
    rw [map_one, map_one]
  map_mul' s t := by
    obtain ⟨n, u, v, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ (f := steinbergTransition R) s t
    have hu : (⟦⟨n, u⟩⟧ : stableSteinberg R) = stableSteinbergOf R n u := rfl
    have hv : (⟦⟨n, v⟩⟧ : stableSteinberg R) = stableSteinbergOf R n v := rfl
    rw [hu, hv, ← map_mul (stableSteinbergOf R n)]
    show stableSteinbergOf S n (SteinbergGroup.ringMap f (u * v))
      = stableSteinbergOf S n (SteinbergGroup.ringMap f u)
        * stableSteinbergOf S n (SteinbergGroup.ringMap f v)
    rw [map_mul, map_mul]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableRingMap

theorem stableRingMap_of (f : R →+* S) (n : ℕ) (t : SteinbergGroup (Fin n) R) :
    stableRingMap f (stableSteinbergOf R n t)
      = stableSteinbergOf S n (SteinbergGroup.ringMap f t) := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableRingMap_of

/-- A surjective ring map induces a surjection of stable Steinberg groups. -/
theorem stableRingMap_surjective (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (stableRingMap f) := by
  intro s
  obtain ⟨n, t, rfl⟩ := DirectLimit.exists_eq_mk (f := steinbergTransition S) s
  obtain ⟨u, rfl⟩ := SteinbergGroup.ringMap_surjective_of_surjective (I := Fin n) f hf t
  exact ⟨stableSteinbergOf R n u, rfl⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableRingMap_surjective

/-- **Naturality of the stable projection**: `St(R) → GL(R) → GL(S)` equals
`St(R) → St(S) → GL(S)`. -/
theorem stableProjection_stableRingMap (f : R →+* S) (s : stableSteinberg R) :
    stableProjection S (stableRingMap f s) = glColimMap f (stableProjection R s) := by
  obtain ⟨n, t, rfl⟩ := DirectLimit.exists_eq_mk (f := steinbergTransition R) s
  change stableProjectionComponent S n (SteinbergGroup.ringMap f t)
    = glColimMap f (stableProjectionComponent R n t)
  have hcomp : (stableProjectionComponent S n).comp (SteinbergGroup.ringMap (I := Fin n) f)
      = (glColimMap f).comp (stableProjectionComponent R n) := by
    apply PresentedGroup.ext
    rintro ⟨i, j, hij, a⟩
    change stableProjectionComponent S n (SteinbergGroup.ringMap f (SteinbergGroup.x i j hij a))
      = glColimMap f (stableProjectionComponent R n (SteinbergGroup.x i j hij a))
    rw [SteinbergGroup.ringMap_x, stableProjectionComponent_x, stableProjectionComponent_x,
      glColimMap_glColimOf, elementaryMatrixUnitMap_elementaryUnit]
  exact DFunLike.congr_fun hcomp t

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stableProjection_stableRingMap

end RingMap

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
