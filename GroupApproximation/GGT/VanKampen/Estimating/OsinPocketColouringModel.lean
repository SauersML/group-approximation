import GroupApproximation.GGT.VanKampen.ClosedWalkFaceColouring
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchedTwoGonNoncrossing
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeModel
import GroupApproximation.Meta.AxiomGuard

/-!
# Orienting the face colouring on a pinched pocket and a lake

A model test for the orientation step of `ClosedWalkFaceColouring.lean`.  In a planar map a closed
walk two-colours the faces, and the colour changes exactly across the edges of the walk
(`exists_faceSet_colouring`).  The walk is a boundary cycle of a colour class once the faces of all
walk darts get one colour (`boundaryCycleOfColouring`).  The test runs on two noncrossing walks that
are not simple, and on one walk that crosses itself.

* The pinched pocket `[5,3,4,6]` of `Estimating/OsinPocketPinchedTwoGonRegion.lean`.  In every
  colouring its darts get one colour (`pinchCycle_orient`).  The class of that colour is the pocket
  face set, the two digons (`pinchCycle_colourClass`).  So the colouring recovers the pocket
  (`exists_boundaryCycle_pinchCycle`).
* The walk `[3,1]` on the rose of `Estimating/OsinPocketLakeModel.lean`, the outer cycle of the
  lake walk.  Its darts get one colour (`outerCycle_orient`), and the class is `{Π, O}`, the
  complement of the annulus `K` (`outerCycle_colourClass`, `exists_boundaryCycle_outerCycle`).
  Every edge at `Π` or `O` has `K` on its other side (`faceOf_alpha_of_ne`).  So the class holds no
  edge, and `Π` and `O` get one colour only through the two changes across `K`.
* The walk `[0,3]` on the same rose uses no edge twice and crosses itself at the vertex
  (`crossCycle_not_isNoncrossingClosedWalk`).  Some colouring gives its two darts different colours
  (`crossCycle_not_orient`), so the orientation hypothesis of `exists_boundaryCycle_of_orient` is
  not vacuous.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 1636, through Osin's Lemma 9.7(b)); certifies no
printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketColouringModel

open Surgery.MapCollapse (BoundaryCycle)
open SimpleClosedWalkSides (walkKeep)
open ClosedWalkFaceColouring

universe u

/-- Two propositions that both differ from a third agree. -/
theorem colour_iff_of_not_iff {a b c : Prop} (ha : ¬ (a ↔ c)) (hb : ¬ (b ↔ c)) : a ↔ b := by
  tauto

theorem walkKeep_iff_mem {M : CombMap.{u}} {w : List M.Dart} {d : M.Dart} :
    walkKeep M w d ↔ d ∈ w ∨ M.alpha d ∈ w :=
  Iff.rfl

#audit_axioms colour_iff_of_not_iff
#audit_axioms walkKeep_iff_mem

namespace PinchedTwoGon

open OsinPocketPinchedTwoGonModel

/-- The colour relations along the pocket cycle: each digon differs from the relator cell, and the
outer face agrees with it across the edge `{2,7}` off the walk. -/
theorem pinchCycle_colour (faces : Finset diagram.toCombMap.Face)
    (hcol : ∀ d, ¬ (diagram.toCombMap.faceOf (diagram.toCombMap.alpha d) ∈ faces ↔
      diagram.toCombMap.faceOf d ∈ faces) ↔
        walkKeep diagram.toCombMap ([5, 3, 4, 6] : List (Fin 10)) d) :
    ¬ (face 1 ∈ faces ↔ face 0 ∈ faces) ∧ ¬ (face 2 ∈ faces ↔ face 0 ∈ faces) ∧
      (face 3 ∈ faces ↔ face 0 ∈ faces) := by
  have e0 : diagram.toCombMap.faceOf (0 : Fin 10) = face 0 := (faceOf_eq_face _ 0).mpr (by decide)
  have e1 : diagram.toCombMap.faceOf (1 : Fin 10) = face 0 := (faceOf_eq_face _ 0).mpr (by decide)
  have e2 : diagram.toCombMap.faceOf (2 : Fin 10) = face 0 := (faceOf_eq_face _ 0).mpr (by decide)
  have a0 : diagram.toCombMap.faceOf (diagram.toCombMap.alpha (0 : Fin 10)) = face 1 :=
    (faceOf_eq_face _ 1).mpr (by decide)
  have a1 : diagram.toCombMap.faceOf (diagram.toCombMap.alpha (1 : Fin 10)) = face 2 :=
    (faceOf_eq_face _ 2).mpr (by decide)
  have a2 : diagram.toCombMap.faceOf (diagram.toCombMap.alpha (2 : Fin 10)) = face 3 :=
    (faceOf_eq_face _ 3).mpr (by decide)
  have h0 := (hcol (0 : Fin 10)).mpr (walkKeep_iff_mem.mpr (by decide))
  have h1 := (hcol (1 : Fin 10)).mpr (walkKeep_iff_mem.mpr (by decide))
  have h2 : diagram.toCombMap.faceOf (diagram.toCombMap.alpha (2 : Fin 10)) ∈ faces ↔
      diagram.toCombMap.faceOf (2 : Fin 10) ∈ faces :=
    mem_iff_mem_alpha_of_not_walkKeep hcol (walkKeep_iff_mem.not.mpr (by decide))
  rw [e0, a0] at h0
  rw [e1, a1] at h1
  rw [e2, a2] at h2
  exact ⟨h0, h1, h2⟩

/-- **In every colouring along the pocket cycle, its darts get one colour.** -/
theorem pinchCycle_orient (faces : Finset diagram.toCombMap.Face)
    (hcol : ∀ d, ¬ (diagram.toCombMap.faceOf (diagram.toCombMap.alpha d) ∈ faces ↔
      diagram.toCombMap.faceOf d ∈ faces) ↔
        walkKeep diagram.toCombMap ([5, 3, 4, 6] : List (Fin 10)) d) :
    ∀ d ∈ ([5, 3, 4, 6] : List (Fin 10)), ∀ e ∈ ([5, 3, 4, 6] : List (Fin 10)),
      (diagram.toCombMap.faceOf d ∈ faces ↔ diagram.toCombMap.faceOf e ∈ faces) := by
  obtain ⟨h0, h1, -⟩ := pinchCycle_colour faces hcol
  have key : face 1 ∈ faces ↔ face 2 ∈ faces := colour_iff_of_not_iff h0 h1
  have e3 : diagram.toCombMap.faceOf (3 : Fin 10) = face 1 := (faceOf_eq_face _ 1).mpr (by decide)
  have e4 : diagram.toCombMap.faceOf (4 : Fin 10) = face 1 := (faceOf_eq_face _ 1).mpr (by decide)
  have e5 : diagram.toCombMap.faceOf (5 : Fin 10) = face 2 := (faceOf_eq_face _ 2).mpr (by decide)
  have e6 : diagram.toCombMap.faceOf (6 : Fin 10) = face 2 := (faceOf_eq_face _ 2).mpr (by decide)
  intro d hd e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd he
  rcases hd with rfl | rfl | rfl | rfl <;> rcases he with rfl | rfl | rfl | rfl <;>
    simp only [e3, e4, e5, e6] <;> first | exact Iff.rfl | exact key | exact key.symm

/-- **The colour class of the pocket cycle is the pocket face set.**  If the faces of the darts of
`[5,3,4,6]` lie in a colour class, that class is the two digons. -/
theorem pinchCycle_colourClass (faces : Finset diagram.toCombMap.Face)
    (hcol : ∀ d, ¬ (diagram.toCombMap.faceOf (diagram.toCombMap.alpha d) ∈ faces ↔
      diagram.toCombMap.faceOf d ∈ faces) ↔
        walkKeep diagram.toCombMap ([5, 3, 4, 6] : List (Fin 10)) d)
    (hin : ∀ d ∈ ([5, 3, 4, 6] : List (Fin 10)), diagram.toCombMap.faceOf d ∈ faces) :
    faces = pinchFaces := by
  obtain ⟨h0, -, h3⟩ := pinchCycle_colour faces hcol
  have e3 : diagram.toCombMap.faceOf (3 : Fin 10) = face 1 := (faceOf_eq_face _ 1).mpr (by decide)
  have e5 : diagram.toCombMap.faceOf (5 : Fin 10) = face 2 := (faceOf_eq_face _ 2).mpr (by decide)
  have hf1 : face 1 ∈ faces := by
    rw [← e3]
    exact hin 3 (by decide)
  have hf2 : face 2 ∈ faces := by
    rw [← e5]
    exact hin 5 (by decide)
  have hf0 : face 0 ∉ faces := fun h => h0 (iff_of_true hf1 h)
  have hf3 : face 3 ∉ faces := fun h => hf0 (h3.mp h)
  have hnp : ∀ i : Fin 4, i ≠ 1 → i ≠ 2 → face i ∉ pinchFaces := fun i h1 h2 h =>
    (Finset.mem_cons.mp h).elim (fun h => h1 ((face_eq_iff i 1).mp h))
      fun h => h2 ((face_eq_iff i 2).mp (Finset.mem_singleton.mp h))
  have hi : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  ext f
  obtain ⟨i, rfl⟩ : ∃ i, face i = f :=
    ⟨faceEquiv f, faceEquiv.injective (faceEquiv_face (faceEquiv f))⟩
  rcases hi i with rfl | rfl | rfl | rfl
  · exact iff_of_false hf0 (hnp 0 (by decide) (by decide))
  · exact iff_of_true hf1 (Finset.mem_cons.mpr (Or.inl rfl))
  · exact iff_of_true hf2 (Finset.mem_cons.mpr (Or.inr (Finset.mem_singleton_self _)))
  · exact iff_of_false hf3 (hnp 3 (by decide) (by decide))

theorem exists_boundaryCycle_of_colour (faces : Finset diagram.toCombMap.Face)
    (hcol : ∀ d, ¬ (diagram.toCombMap.faceOf (diagram.toCombMap.alpha d) ∈ faces ↔
      diagram.toCombMap.faceOf d ∈ faces) ↔
        walkKeep diagram.toCombMap ([5, 3, 4, 6] : List (Fin 10)) d)
    (hall : ∀ d ∈ ([5, 3, 4, 6] : List (Fin 10)), diagram.toCombMap.faceOf d ∈ faces) :
    ∃ B : BoundaryCycle diagram.toCombMap pinchFaces,
      B.cycle = ([5, 3, 4, 6] : List (Fin 10)) := by
  obtain rfl := pinchCycle_colourClass faces hcol hall
  exact ⟨boundaryCycleOfColouring isNoncrossingClosedWalk_pinchCycle.ne_nil
    isNoncrossingClosedWalk_pinchCycle.nodup hcol hall, rfl⟩

/-- **The colouring recovers the pinched pocket:** the pocket cycle `[5,3,4,6]` is a boundary cycle
of the two digons, through `exists_faceSet_colouring`, `pinchCycle_orient` and
`boundaryCycleOfColouring`. -/
theorem exists_boundaryCycle_pinchCycle :
    ∃ B : BoundaryCycle diagram.toCombMap pinchFaces,
      B.cycle = ([5, 3, 4, 6] : List (Fin 10)) := by
  classical
  have hw := isNoncrossingClosedWalk_pinchCycle
  obtain ⟨faces, hcol⟩ := exists_faceSet_colouring diagram.planar hw.ne_nil hw.nodup
    hw.alpha_not_mem hw.chain hw.closes
  by_cases hin : diagram.toCombMap.faceOf (5 : Fin 10) ∈ faces
  · exact exists_boundaryCycle_of_colour faces hcol
      fun d hd => (pinchCycle_orient faces hcol d hd 5 (by decide)).mpr hin
  · exact exists_boundaryCycle_of_colour facesᶜ (colouring_compl hcol)
      fun d hd => Finset.mem_compl.mpr
        fun h => hin ((pinchCycle_orient faces hcol d hd 5 (by decide)).mp h)

#audit_axioms pinchCycle_colour
#audit_axioms pinchCycle_orient
#audit_axioms pinchCycle_colourClass
#audit_axioms exists_boundaryCycle_of_colour
#audit_closed_axioms exists_boundaryCycle_pinchCycle

end PinchedTwoGon

namespace Lake

open OsinPocketLakeModel

theorem faceEquiv_faceOf_faceRep (i : Fin 3) : faceEquiv (M.faceOf (faceRep i)) = i := by
  change faceClass (faceRep i) = i
  fin_cases i <;> rfl

theorem faceOf_eq_iff (d e : Fin 4) : M.faceOf d = M.faceOf e ↔ faceClass d = faceClass e := by
  rw [← faceEquiv.injective.eq_iff]
  rfl

/-- **The colour class `{Π, O}` holds no edge:** every edge at `Π` or `O` has the annulus `K` on its
other side. -/
theorem faceOf_alpha_of_ne (d : Fin 4) (hd : M.faceOf d ≠ M.faceOf (0 : Fin 4)) :
    M.faceOf (M.alpha d) = M.faceOf (0 : Fin 4) :=
  (faceOf_eq_iff (M.alpha d) 0).mpr
    ((show ∀ x : Fin 4, faceClass x ≠ faceClass 0 → faceClass (M.alpha x) = faceClass 0 by
      decide) d ((faceOf_eq_iff d 0).not.mp hd))

/-- One rotation step from the reversal of each dart of `[3,1]` reaches a dart of the walk. -/
theorem sigma_alpha_mem_outerCycle :
    ∀ d ∈ ([3, 1] : List M.Dart), M.sigma (M.alpha d) ∈ ([3, 1] : List M.Dart) := by
  decide

/-- **The outer cycle of the lake walk is a noncrossing closed walk.** -/
theorem isNoncrossingClosedWalk_outerCycle :
    IsNoncrossingClosedWalk M ([3, 1] : List (Fin 4)) where
  ne_nil := List.cons_ne_nil _ _
  nodup := by decide
  chain := List.isChain_cons_cons.mpr
    ⟨vertexEquiv.injective (by decide), List.isChain_singleton _⟩
  closes := vertexEquiv.injective (by decide)
  alpha_not_mem := by decide
  turn_mem d hd := NoncrossingClosedWalkSides.turn_mem_of_first Nat.one_pos
    (by rw [pow_one]; exact sigma_alpha_mem_outerCycle d hd)
    fun _ hk0 hk1 => absurd hk0 (Nat.not_lt.mpr (Nat.le_of_lt_succ hk1))

/-- The colour relations along `[3,1]`: the lake `Π` and the outside `O` each differ from `K`. -/
theorem outerCycle_colour (faces : Finset M.Face)
    (hcol : ∀ d, ¬ (M.faceOf (M.alpha d) ∈ faces ↔ M.faceOf d ∈ faces) ↔
      walkKeep M ([3, 1] : List (Fin 4)) d) :
    ¬ (M.faceOf (1 : Fin 4) ∈ faces ↔ M.faceOf (0 : Fin 4) ∈ faces) ∧
      ¬ (M.faceOf (3 : Fin 4) ∈ faces ↔ M.faceOf (0 : Fin 4) ∈ faces) := by
  have a0 : M.alpha (0 : Fin 4) = (1 : Fin 4) := by decide
  have a2 : M.alpha (2 : Fin 4) = (3 : Fin 4) := by decide
  have e2 : M.faceOf (2 : Fin 4) = M.faceOf (0 : Fin 4) := (faceOf_eq_iff 2 0).mpr (by decide)
  have h0 := (hcol (0 : Fin 4)).mpr (walkKeep_iff_mem.mpr (by decide))
  have h2 := (hcol (2 : Fin 4)).mpr (walkKeep_iff_mem.mpr (by decide))
  rw [a0] at h0
  rw [a2, e2] at h2
  exact ⟨h0, h2⟩

/-- **In every colouring along `[3,1]`, its darts get one colour.** -/
theorem outerCycle_orient (faces : Finset M.Face)
    (hcol : ∀ d, ¬ (M.faceOf (M.alpha d) ∈ faces ↔ M.faceOf d ∈ faces) ↔
      walkKeep M ([3, 1] : List (Fin 4)) d) :
    ∀ d ∈ ([3, 1] : List (Fin 4)), ∀ e ∈ ([3, 1] : List (Fin 4)),
      (M.faceOf d ∈ faces ↔ M.faceOf e ∈ faces) := by
  obtain ⟨h1, h3⟩ := outerCycle_colour faces hcol
  have key : M.faceOf (3 : Fin 4) ∈ faces ↔ M.faceOf (1 : Fin 4) ∈ faces :=
    colour_iff_of_not_iff h3 h1
  intro d hd e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd he
  rcases hd with rfl | rfl <;> rcases he with rfl | rfl
  exacts [Iff.rfl, key, key.symm, Iff.rfl]

/-- **The colour class of `[3,1]` is `{Π, O}`,** the faces other than `K`. -/
theorem outerCycle_colourClass (faces : Finset M.Face)
    (hcol : ∀ d, ¬ (M.faceOf (M.alpha d) ∈ faces ↔ M.faceOf d ∈ faces) ↔
      walkKeep M ([3, 1] : List (Fin 4)) d)
    (hin : ∀ d ∈ ([3, 1] : List (Fin 4)), M.faceOf d ∈ faces) :
    ∀ f, f ∈ faces ↔ f ≠ M.faceOf (0 : Fin 4) := by
  obtain ⟨h1, -⟩ := outerCycle_colour faces hcol
  have hf1 : M.faceOf (1 : Fin 4) ∈ faces := hin 1 (by decide)
  have hf3 : M.faceOf (3 : Fin 4) ∈ faces := hin 3 (by decide)
  have hf0 : M.faceOf (0 : Fin 4) ∉ faces := fun h => h1 (iff_of_true hf1 h)
  have r0 : M.faceOf (faceRep 0) = M.faceOf (0 : Fin 4) := (faceOf_eq_iff _ _).mpr (by decide)
  have r1 : M.faceOf (faceRep 1) = M.faceOf (1 : Fin 4) := (faceOf_eq_iff _ _).mpr (by decide)
  have r2 : M.faceOf (faceRep 2) = M.faceOf (3 : Fin 4) := (faceOf_eq_iff _ _).mpr (by decide)
  have hi : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  intro f
  obtain ⟨i, rfl⟩ : ∃ i, M.faceOf (faceRep i) = f :=
    ⟨faceEquiv f, faceEquiv.injective (faceEquiv_faceOf_faceRep (faceEquiv f))⟩
  rcases hi i with rfl | rfl | rfl
  · rw [r0]
    exact iff_of_false hf0 fun h => h rfl
  · rw [r1]
    exact iff_of_true hf1 fun h => absurd ((faceOf_eq_iff 1 0).mp h) (by decide)
  · rw [r2]
    exact iff_of_true hf3 fun h => absurd ((faceOf_eq_iff 3 0).mp h) (by decide)

theorem exists_boundaryCycle_of_colour (faces : Finset M.Face)
    (hcol : ∀ d, ¬ (M.faceOf (M.alpha d) ∈ faces ↔ M.faceOf d ∈ faces) ↔
      walkKeep M ([3, 1] : List (Fin 4)) d)
    (hall : ∀ d ∈ ([3, 1] : List (Fin 4)), M.faceOf d ∈ faces) :
    ∃ (U : Finset M.Face) (B : BoundaryCycle M U), B.cycle = ([3, 1] : List (Fin 4)) ∧
      ∀ f, f ∈ U ↔ f ≠ M.faceOf (0 : Fin 4) :=
  ⟨faces, boundaryCycleOfColouring isNoncrossingClosedWalk_outerCycle.ne_nil
    isNoncrossingClosedWalk_outerCycle.nodup hcol hall, rfl,
    outerCycle_colourClass faces hcol hall⟩

/-- **The colouring along `[3,1]` gives the complement of the annulus:** `[3,1]` is a boundary cycle
of `{Π, O}`, a face set holding no edge. -/
theorem exists_boundaryCycle_outerCycle :
    ∃ (U : Finset M.Face) (B : BoundaryCycle M U), B.cycle = ([3, 1] : List (Fin 4)) ∧
      ∀ f, f ∈ U ↔ f ≠ M.faceOf (0 : Fin 4) := by
  classical
  have hw := isNoncrossingClosedWalk_outerCycle
  obtain ⟨faces, hcol⟩ := exists_faceSet_colouring planar hw.ne_nil hw.nodup hw.alpha_not_mem
    hw.chain hw.closes
  by_cases hin : M.faceOf (3 : Fin 4) ∈ faces
  · exact exists_boundaryCycle_of_colour faces hcol
      fun d hd => (outerCycle_orient faces hcol d hd 3 (by decide)).mpr hin
  · exact exists_boundaryCycle_of_colour facesᶜ (colouring_compl hcol)
      fun d hd => Finset.mem_compl.mpr
        fun h => hin ((outerCycle_orient faces hcol d hd 3 (by decide)).mp h)

/-- **The walk `[0,3]` crosses itself.**  Rotating from the reversal `1` of `0`, the first dart on
an edge of the walk is `2`, the reversal of `3`. -/
theorem crossCycle_not_isNoncrossingClosedWalk :
    ¬ IsNoncrossingClosedWalk M ([0, 3] : List (Fin 4)) := by
  intro h
  have hmem := h.turn_mem 0 (by decide) 1 Nat.one_pos
    (by rw [pow_one]; exact walkKeep_iff_mem.mpr (by decide))
    fun _ hk0 hk1 => absurd hk0 (Nat.not_lt.mpr (Nat.le_of_lt_succ hk1))
  rw [pow_one] at hmem
  exact absurd hmem (by decide)

/-- **A crossing walk fails the orientation.**  Some colouring along `[0,3]` gives `0` and `3`
different colours: the colour changes across the edge `{2,3}`, and `2` lies on the face `K` of `0`. -/
theorem crossCycle_not_orient :
    ∃ faces : Finset M.Face,
      (∀ d, ¬ (M.faceOf (M.alpha d) ∈ faces ↔ M.faceOf d ∈ faces) ↔
        walkKeep M ([0, 3] : List (Fin 4)) d) ∧
      ¬ (M.faceOf (0 : Fin 4) ∈ faces ↔ M.faceOf (3 : Fin 4) ∈ faces) := by
  obtain ⟨faces, hcol⟩ := exists_faceSet_colouring planar (w := ([0, 3] : List (Fin 4)))
    (List.cons_ne_nil _ _) (by decide) (by decide)
    (List.isChain_cons_cons.mpr
      ⟨vertexEquiv.injective (by decide), List.isChain_singleton _⟩)
    (vertexEquiv.injective (by decide))
  refine ⟨faces, hcol, fun h => ?_⟩
  have a2 : M.alpha (2 : Fin 4) = (3 : Fin 4) := by decide
  have e2 : M.faceOf (2 : Fin 4) = M.faceOf (0 : Fin 4) := (faceOf_eq_iff 2 0).mpr (by decide)
  have h2 := (hcol (2 : Fin 4)).mpr (walkKeep_iff_mem.mpr (by decide))
  rw [a2, e2] at h2
  exact h2 h.symm

#audit_axioms faceEquiv_faceOf_faceRep
#audit_axioms faceOf_eq_iff
#audit_axioms faceOf_alpha_of_ne
#audit_axioms sigma_alpha_mem_outerCycle
#audit_closed_axioms isNoncrossingClosedWalk_outerCycle
#audit_axioms outerCycle_colour
#audit_axioms outerCycle_orient
#audit_axioms outerCycle_colourClass
#audit_axioms exists_boundaryCycle_of_colour
#audit_closed_axioms exists_boundaryCycle_outerCycle
#audit_closed_axioms crossCycle_not_isNoncrossingClosedWalk
#audit_closed_axioms crossCycle_not_orient

end Lake

end GroupApproximation.GGT.VanKampen.OsinPocketColouringModel
