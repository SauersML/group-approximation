import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCountParityCycles
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01HoldingSmallFaces.FaceClassTools
import GroupApproximation.Meta.AxiomGuard

/-!
# The outside face classes are the orbits of the face permutation

Lane gl-p10-44.  Notation: `M = X.toCombMap`, `c = K.boundary.cycle`, `keep = walkKeep M c`,
`R = FaceClassStep M keep`, `P = walkMap M c`, `f = extremalJordanPickCountParity_perm K`.

**Claims.**
1. `faceOf x ∈ K.faces` is constant along `R`-classes (`extremalJordanPickCyc_faces_iff`).  A face
   step keeps the face.  An unkept crossing `x ↦ α x` has `x ∉ c` and `α x ∉ c`.  Since
   `c` is exactly the boundary darts of `K.faces`, neither `x` nor `α x` crosses from inside to
   outside, so both lie inside or both lie outside.
2. Every dart `r` based outside `K.faces` is `R`-equivalent to `α d` for some `d ∈ c`
   (`extremalJordanPickCyc_exists_of_outside`).  `M` is connected, so `r` is `R`-equivalent to a
   kept dart `w` (`exists_keep_of_connected`).  By 1, `w` is based outside, so `w ∉ c`, so
   `α w ∈ c`.  Conversely `α d` is based outside for `d ∈ c`.  So the outside classes are the
   classes of the `α d`, `d ∈ c` (`extremalJordanPickCyc_outside_eq`).
3. `α d ~R α (f d)` for `d ∈ c` (`extremalJordanPickCyc_class_perm`).  Here `α (f d) = σ_P d =
   σ^m d`, and the darts `σ^t d`, `0 < t < m`, are unkept.  So the run
   `α d → σ (α α d) = σ d → … → σ^m d` is a chain of `R`-steps (`faceClass_run`).  Hence
   `SameCycle f d d'` gives `α d ~R α d'` (`extremalJordanPickCyc_class_of_sameCycle`).
4. Conversely, let `α d ~R α d'` with `d, d' ∈ c`.  The separation theorem for the connected
   restriction `P` (`IsRestriction.faceOf_eq_of_faceClass`) puts `α d` and `α d'` on one face
   of `P`.  On reversed walk darts the face permutation of `P` is `α e ↦ σ_P e = α (f e)`
   (`extremalJordanPickCyc_facePerm_val`).  So `α d' = α (f^n d)`, and `d' = f^n d`
   (`extremalJordanPickCyc_sameCycle_of_class`).

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open scoped Classical

section CycClass

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Claim 1**: being based inside `K.faces` is constant along face classes off the walk. -/
theorem extremalJordanPickCyc_faces_iff (K : PocketFaceSet D eps X lo hi)
    {x y : X.toCombMap.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle)) x y) :
    X.toCombMap.faceOf x ∈ K.faces ↔ X.toCombMap.faceOf y ∈ K.faces := by
  induction h with
  | rel a b hab =>
    rcases hab with rfl | ⟨hk, rfl⟩
    · rw [X.toCombMap.faceOf_facePerm]
    · have ha : ¬ (X.toCombMap.faceOf a ∈ K.faces ∧
          X.toCombMap.faceOf (X.toCombMap.alpha a) ∉ K.faces) :=
        fun hb => hk (Or.inl ((K.boundary.cycle_mem_iff a).mpr hb))
      have hb : ¬ (X.toCombMap.faceOf (X.toCombMap.alpha a) ∈ K.faces ∧
          X.toCombMap.faceOf a ∉ K.faces) := fun hb => hk (Or.inr
        ((K.boundary.cycle_mem_iff (X.toCombMap.alpha a)).mpr
          (show X.toCombMap.faceOf (X.toCombMap.alpha a) ∈ K.faces ∧
              X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha a)) ∉ K.faces from by
            rw [X.toCombMap.alpha_involutive a]; exact hb)))
      constructor
      · intro hA
        by_contra hB
        exact ha ⟨hA, hB⟩
      · intro hB
        by_contra hA
        exact hb ⟨hB, hA⟩
  | refl a => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b e _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Claim 2**: a dart based outside `K.faces` is in the face class of a reversed walk dart. -/
theorem extremalJordanPickCyc_exists_of_outside (K : PocketFaceSet D eps X lo hi)
    {r : X.toCombMap.Dart} (hr : X.toCombMap.faceOf r ∉ K.faces) :
    ∃ d ∈ K.boundary.cycle, Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle)) r (X.toCombMap.alpha d) := by
  obtain ⟨w', hw', hrw⟩ := P01HoldingSmallFaces.exists_keep_of_connected
    (M := X.toCombMap) (K := walkKeep X.toCombMap K.boundary.cycle)
    (walkKeep_alpha X.toCombMap K.boundary.cycle) X.planar.1
    (w₀ := K.boundary.cycle.head K.boundary.cycle_nonempty)
    (Or.inl (List.head_mem K.boundary.cycle_nonempty)) r
  have hwf : X.toCombMap.faceOf w' ∉ K.faces := fun h =>
    hr ((extremalJordanPickCyc_faces_iff K hrw).mpr h)
  have hwc : w' ∉ K.boundary.cycle := fun h => hwf ((K.boundary.cycle_mem_iff w').mp h).1
  rcases hw' with hw' | hw'
  · exact absurd hw' hwc
  · refine ⟨X.toCombMap.alpha w', hw', ?_⟩
    rw [X.toCombMap.alpha_involutive w']
    exact hrw

/-- **Claim 2, image form**: the outside classes are the classes of the reversed walk darts. -/
theorem extremalJordanPickCyc_outside_eq (K : PocketFaceSet D eps X lo hi) :
    extremalJordanPickCount_outside K = K.boundary.cycle.toFinset.image (fun d =>
      Quot.mk (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
        (X.toCombMap.alpha d)) := by
  unfold extremalJordanPickCount_outside
  ext q
  rw [Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨d, hd, hrd⟩ := extremalJordanPickCyc_exists_of_outside K (Finset.mem_filter.mp hr).2
    exact ⟨d, List.mem_toFinset.mpr hd, (Quot.eqvGen_sound hrd).symm⟩
  · rintro ⟨d, hd, rfl⟩
    refine ⟨X.toCombMap.alpha d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact ((K.boundary.cycle_mem_iff d).mp (List.mem_toFinset.mp hd)).2

end CycClass

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_faces_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_exists_of_outside
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_outside_eq
