import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalGFace
import GroupApproximation.Meta.AxiomGuard

/-!
# Face-set colourings of a boundary cycle

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-49.

Route: a colouring `z` of the walk regions of a boundary cycle `c` of `F` is the same datum as
the face set `F' = flipFaces M F z`.  This module gives the dictionary in both directions, for a
generic combinatorial map `M`:

* `extremalGFaceProve_colour M F F'` colours a dart `true` when its face is in exactly one of
  `F`, `F'`.
* `extremalGFaceProve_colour_step`: the colour is constant along the walk regions of `c` as soon
  as `F'` does not separate the two sides of any dart off the walk.
* `extremalGFaceProve_colour_indep`: no side pair of a walk dart is coloured twice as soon as
  every boundary dart of `F'` lies on `c`.
* `extremalGFaceProve_flipFaces_colour`: flipping `F` at the colour gives `F'`; and
  `extremalGFaceProve_colour_flipFaces` is the converse.
* `extremalGFaceProve_touch`: in a connected map, some walk dart is touched when `F' ≠ F`.
* `extremalGFaceProve_movePred_colour_of_mem`: on `c`, the kept darts of the colour are the
  boundary darts of `F'` (`extremalGFaceProve_bd`).
* `extremalGFaceProve_flip_union`, `extremalGFaceProve_flip_boundary`,
  `extremalGFaceProve_flip_ne`, `extremalGFaceProve_movePred_flip`: the converse facts for the
  face set `flipFaces M F z` of a colouring `z`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- The colour of a face: `true` when it lies in exactly one of `F`, `F'`. -/
noncomputable def extremalGFaceProve_colourFace (M : CombMap.{v}) (F F' : Finset M.Face)
    (f : M.Face) : Bool :=
  @decide (¬(f ∈ F ↔ f ∈ F')) (Classical.propDecidable _)

/-- The colour of a dart: the colour of its face. -/
noncomputable def extremalGFaceProve_colour (M : CombMap.{v}) (F F' : Finset M.Face)
    (x : M.Dart) : Bool :=
  extremalGFaceProve_colourFace M F F' (M.faceOf x)

/-- The boundary darts of a face set, as a Boolean predicate. -/
noncomputable def extremalGFaceProve_bd (M : CombMap.{v}) (F' : Finset M.Face)
    (d : M.Dart) : Bool :=
  @decide (M.faceOf d ∈ F' ∧ M.faceOf (M.alpha d) ∉ F') (Classical.propDecidable _)

theorem extremalGFaceProve_colour_eq_false_iff (M : CombMap.{v}) (F F' : Finset M.Face)
    (x : M.Dart) :
    extremalGFaceProve_colour M F F' x = false ↔ (M.faceOf x ∈ F ↔ M.faceOf x ∈ F') := by
  unfold extremalGFaceProve_colour extremalGFaceProve_colourFace
  exact (@decide_eq_false_iff_not _ (Classical.propDecidable _)).trans Classical.not_not

theorem extremalGFaceProve_bd_eq_true_iff (M : CombMap.{v}) (F' : Finset M.Face)
    (d : M.Dart) :
    extremalGFaceProve_bd M F' d = true ↔
      M.faceOf d ∈ F' ∧ M.faceOf (M.alpha d) ∉ F' := by
  unfold extremalGFaceProve_bd
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

theorem extremalGFaceProve_bool_eq_of_false_iff {a b : Bool} (h : a = false ↔ b = false) :
    a = b := by
  cases a <;> cases b
  · rfl
  · exact absurd (h.mp rfl) (by decide)
  · exact absurd (h.mpr rfl) (by decide)
  · rfl

theorem extremalGFaceProve_bool_eq_of_true_iff {a b : Bool} (h : a = true ↔ b = true) :
    a = b := by
  cases a <;> cases b
  · rfl
  · exact absurd (h.mpr rfl) (by decide)
  · exact absurd (h.mp rfl) (by decide)
  · rfl

theorem extremalGFaceProve_colour_eq_of_iff (M : CombMap.{v}) (F F' : Finset M.Face)
    {x y : M.Dart} (h1 : M.faceOf x ∈ F ↔ M.faceOf y ∈ F)
    (h2 : M.faceOf x ∈ F' ↔ M.faceOf y ∈ F') :
    extremalGFaceProve_colour M F F' x = extremalGFaceProve_colour M F F' y := by
  apply extremalGFaceProve_bool_eq_of_false_iff
  rw [extremalGFaceProve_colour_eq_false_iff M F F' x,
    extremalGFaceProve_colour_eq_false_iff M F F' y]
  exact ⟨fun h => h1.symm.trans (h.trans h2), fun h => h1.trans (h.trans h2.symm)⟩

/-- Off the walk, the two sides of a dart are on the same side of `F`. -/
theorem extremalGFaceProve_mem_iff_alpha_of_not_walkKeep {M : CombMap.{v}} {F : Finset M.Face}
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d)
    {x : M.Dart} (hx : ¬ walkKeep M c x) :
    M.faceOf x ∈ F ↔ M.faceOf (M.alpha x) ∈ F := by
  constructor
  · intro h
    by_contra h'
    exact hx (Or.inl ((hc x).mpr ⟨h, h'⟩))
  · intro h
    by_contra h'
    refine hx (Or.inr ((hc (M.alpha x)).mpr ⟨h, ?_⟩))
    rwa [M.alpha_involutive x]

/-- **The colour is constant along the walk regions** when `F'` separates no dart off the walk. -/
theorem extremalGFaceProve_colour_step (M : CombMap.{v}) (F F' : Finset M.Face)
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d)
    (hU : ∀ x, ¬ walkKeep M c x → (M.faceOf x ∈ F' ↔ M.faceOf (M.alpha x) ∈ F')) :
    ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y →
      extremalGFaceProve_colour M F F' x = extremalGFaceProve_colour M F F' y := by
  intro x y hxy
  rcases (show y = M.facePerm x ∨ (¬ walkKeep M c x ∧ y = M.alpha x) from hxy) with
    rfl | ⟨hk, rfl⟩
  · exact congrArg (extremalGFaceProve_colourFace M F F')
      ((M.faceOf_eq_iff x (M.facePerm x)).mpr
        (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)))
  · exact extremalGFaceProve_colour_eq_of_iff M F F'
      (extremalGFaceProve_mem_iff_alpha_of_not_walkKeep hc hk) (hU x hk)

/-- **No side pair of a walk dart is coloured twice** when every boundary dart of `F'` is on the
walk. -/
theorem extremalGFaceProve_colour_indep {M : CombMap.{v}} {F F' : Finset M.Face}
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d)
    (hB : ∀ d, M.faceOf d ∈ F' → M.faceOf (M.alpha d) ∉ F' → d ∈ c) :
    ∀ d ∈ c, extremalGFaceProve_colour M F F' d = false ∨
      extremalGFaceProve_colour M F F' (M.alpha d) = false := by
  intro d hd
  obtain ⟨hin, hout⟩ := (hc d).mp hd
  by_cases h : M.faceOf d ∈ F'
  · exact Or.inl ((extremalGFaceProve_colour_eq_false_iff M F F' d).mpr (iff_of_true hin h))
  · refine Or.inr ((extremalGFaceProve_colour_eq_false_iff M F F' (M.alpha d)).mpr
      (iff_of_false hout fun h' => ?_))
    have hα : M.alpha d ∈ c := hB (M.alpha d) h' (by rwa [M.alpha_involutive d])
    obtain ⟨hin', -⟩ := (hc (M.alpha d)).mp hα
    exact hout hin'

/-- **Flipping `F` at the colour of `F'` gives `F'`.** -/
theorem extremalGFaceProve_flipFaces_colour {M : CombMap.{v}} {F F' : Finset M.Face}
    {keep : M.Dart → Prop}
    (hz : ∀ x y, CombMap.FaceClassStep M keep x y →
      extremalGFaceProve_colour M F F' x = extremalGFaceProve_colour M F F' y) :
    flipFaces M F (extremalGFaceProve_colour M F F') = F' := by
  refine Finset.ext fun f => ?_
  obtain ⟨x, rfl⟩ := Quotient.exists_rep f
  show M.faceOf x ∈ flipFaces M F (extremalGFaceProve_colour M F F') ↔ M.faceOf x ∈ F'
  rw [mem_flipFaces_iff hz x, extremalGFaceProve_colour_eq_false_iff M F F' x]
  tauto

/-- **The colour of a flipped face set is the flip colouring.** -/
theorem extremalGFaceProve_colour_flipFaces {M : CombMap.{v}} {F : Finset M.Face}
    {keep : M.Dart → Prop} {z : M.Dart → Bool}
    (hz : ∀ x y, CombMap.FaceClassStep M keep x y → z x = z y) :
    extremalGFaceProve_colour M F (flipFaces M F z) = z := by
  funext x
  apply extremalGFaceProve_bool_eq_of_false_iff
  rw [extremalGFaceProve_colour_eq_false_iff M F (flipFaces M F z) x, mem_flipFaces_iff hz x]
  tauto

/-- **A face set that holds one face and misses another has a boundary dart**, in a connected
map. -/
theorem extremalGFaceProve_exists_boundary {M : CombMap.{v}} (hM : M.IsConnected)
    {F' : Finset M.Face} {a b : M.Face} (ha : a ∈ F') (hb : b ∉ F') :
    ∃ d, M.faceOf d ∈ F' ∧ M.faceOf (M.alpha d) ∉ F' := by
  by_contra hno
  have hα : ∀ x, M.faceOf x ∈ F' → M.faceOf (M.alpha x) ∈ F' := fun x hx =>
    Classical.byContradiction fun h => hno ⟨x, hx, h⟩
  have hαiff : ∀ x, M.faceOf x ∈ F' ↔ M.faceOf (M.alpha x) ∈ F' := by
    intro x
    refine ⟨hα x, fun h => ?_⟩
    have h2 := hα (M.alpha x) h
    rwa [M.alpha_involutive x] at h2
  have hstep : ∀ x y, M.Adjacent x y → (M.faceOf x ∈ F' ↔ M.faceOf y ∈ F') := by
    intro x y hxy
    rcases (show M.alpha x = y ∨ M.sigma x = y from hxy) with rfl | rfl
    · exact hαiff x
    · have hs : M.sigma x = M.facePerm (M.alpha x) := by
        rw [CombMap.facePerm, Equiv.Perm.mul_apply, M.alpha_involutive x]
      have he : M.faceOf (M.sigma x) = M.faceOf (M.alpha x) := by
        rw [hs]
        exact ((M.faceOf_eq_iff (M.alpha x) (M.facePerm (M.alpha x))).mpr
          (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _))).symm
      rw [he]
      exact hαiff x
  have hall : ∀ x y, Relation.EqvGen M.Adjacent x y →
      (M.faceOf x ∈ F' ↔ M.faceOf y ∈ F') := by
    intro x y h
    induction h with
    | rel p q hpq => exact hstep p q hpq
    | refl _ => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  obtain ⟨x, rfl⟩ := Quotient.exists_rep a
  obtain ⟨y, rfl⟩ := Quotient.exists_rep b
  exact hb ((hall x y (hM x y)).mp ha)

/-- **The boundary darts of `F'` on the walk are not all missing.** -/
theorem extremalGFaceProve_filter_bd_ne_nil {M : CombMap.{v}} (hM : M.IsConnected)
    {F' : Finset M.Face} {c : List M.Dart}
    (hB : ∀ d, M.faceOf d ∈ F' → M.faceOf (M.alpha d) ∉ F' → d ∈ c) {a b : M.Face}
    (ha : a ∈ F') (hb : b ∉ F') :
    c.filter (extremalGFaceProve_bd M F') ≠ [] := by
  obtain ⟨d, h1, h2⟩ := extremalGFaceProve_exists_boundary hM ha hb
  exact List.ne_nil_of_mem (List.mem_filter.mpr
    ⟨hB d h1 h2, (extremalGFaceProve_bd_eq_true_iff M F' d).mpr ⟨h1, h2⟩⟩)

/-- **The colour of a new face set touches the walk**, in a connected map. -/
theorem extremalGFaceProve_touch {M : CombMap.{v}} (hM : M.IsConnected) {F F' : Finset M.Face}
    {c : List M.Dart} (hcne : c ≠ [])
    (hz : ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y →
      extremalGFaceProve_colour M F F' x = extremalGFaceProve_colour M F F' y)
    (hne : F' ≠ F) :
    ∃ y ∈ c, movePred M (extremalGFaceProve_colour M F F') y = false := by
  refine Classical.byContradiction fun hno => hne ?_
  have hall : ∀ y ∈ c, extremalGFaceProve_colour M F F' y = false ∧
      extremalGFaceProve_colour M F F' (M.alpha y) = false := by
    intro y hy
    cases h : movePred M (extremalGFaceProve_colour M F F') y
    · exact (hno ⟨y, hy, h⟩).elim
    · exact (movePred_eq_true_iff M _ y).mp h
  have hzero : ∀ x, extremalGFaceProve_colour M F F' x = false := by
    intro x
    obtain ⟨y, hy, hxy | hxy⟩ := P10RegionMove.exists_mem_eqvGen_of_connected hM hcne x
    · exact (eq_of_eqvGen hz hxy).trans (hall y hy).1
    · exact (eq_of_eqvGen hz hxy).trans (hall y hy).2
  refine Finset.ext fun f => ?_
  obtain ⟨x, rfl⟩ := Quotient.exists_rep f
  exact ((extremalGFaceProve_colour_eq_false_iff M F F' x).mp (hzero x)).symm

/-- **On the walk, the kept darts of the colour are the boundary darts of `F'`.** -/
theorem extremalGFaceProve_movePred_colour_of_mem {M : CombMap.{v}} {F F' : Finset M.Face}
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d)
    {d : M.Dart} (hd : d ∈ c) :
    movePred M (extremalGFaceProve_colour M F F') d = extremalGFaceProve_bd M F' d := by
  obtain ⟨hin, hout⟩ := (hc d).mp hd
  apply extremalGFaceProve_bool_eq_of_true_iff
  rw [movePred_eq_true_iff, extremalGFaceProve_colour_eq_false_iff M F F' d,
    extremalGFaceProve_colour_eq_false_iff M F F' (M.alpha d),
    extremalGFaceProve_bd_eq_true_iff M F' d]
  exact ⟨fun h => ⟨h.1.mp hin, fun h' => hout (h.2.mpr h')⟩,
    fun h => ⟨iff_of_true hin h.1, iff_of_false hout h.2⟩⟩

/-- **A flipped face set separates no dart off the walk.** -/
theorem extremalGFaceProve_flip_union {M : CombMap.{v}} {F : Finset M.Face} {c : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d) {z : M.Dart → Bool}
    (hz : ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y → z x = z y) (x : M.Dart)
    (hk : ¬ walkKeep M c x) :
    M.faceOf x ∈ flipFaces M F z ↔ M.faceOf (M.alpha x) ∈ flipFaces M F z := by
  rw [mem_flipFaces_iff hz x, mem_flipFaces_iff hz (M.alpha x),
    extremalGFaceProve_mem_iff_alpha_of_not_walkKeep hc hk,
    hz x (M.alpha x) (Or.inr ⟨hk, rfl⟩)]

/-- **The boundary darts of a flipped face set lie on the walk**, when no side pair of a walk
dart is flipped twice. -/
theorem extremalGFaceProve_flip_boundary {M : CombMap.{v}} {F : Finset M.Face}
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d)
    {z : M.Dart → Bool} (hz : ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y → z x = z y)
    (hind : ∀ d ∈ c, z d = false ∨ z (M.alpha d) = false) (d : M.Dart)
    (h1 : M.faceOf d ∈ flipFaces M F z) (h2 : M.faceOf (M.alpha d) ∉ flipFaces M F z) :
    d ∈ c := by
  by_cases hk : walkKeep M c d
  · rcases hk with hd | hd
    · exact hd
    · exfalso
      obtain ⟨hin, hout⟩ := (hc (M.alpha d)).mp hd
      rw [M.alpha_involutive d] at hout
      have e1 := (mem_flipFaces_iff hz d).mp h1
      have e2 : ¬(M.faceOf (M.alpha d) ∈ F ↔ z (M.alpha d) = false) :=
        fun h => h2 ((mem_flipFaces_iff hz (M.alpha d)).mpr h)
      rcases hind (M.alpha d) hd with h | h
      · exact e2 (iff_of_true hin h)
      · rw [M.alpha_involutive d] at h
        exact hout (e1.mpr h)
  · exact absurd ((extremalGFaceProve_flip_union hc hz d hk).mp h1) h2

/-- **A colouring touching the walk changes the face set.** -/
theorem extremalGFaceProve_flip_ne {M : CombMap.{v}} {F : Finset M.Face} {c : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d) {z : M.Dart → Bool}
    (hz : ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y → z x = z y) {y : M.Dart}
    (hy : y ∈ c) (hpy : movePred M z y = false) :
    flipFaces M F z ≠ F := by
  intro heq
  obtain ⟨hin, hout⟩ := (hc y).mp hy
  have h1 : M.faceOf y ∈ flipFaces M F z := by
    rw [heq]
    exact hin
  have h2 : M.faceOf (M.alpha y) ∉ flipFaces M F z := by
    rw [heq]
    exact hout
  have e1 : z y = false := ((mem_flipFaces_iff hz y).mp h1).mp hin
  have e2 : z (M.alpha y) = false := by
    by_contra hne
    exact h2 ((mem_flipFaces_iff hz (M.alpha y)).mpr (iff_of_false hout hne))
  have htrue := (movePred_eq_true_iff M z y).mpr ⟨e1, e2⟩
  exact absurd (hpy.symm.trans htrue) (by decide)

/-- **On the walk, the kept darts of a colouring are the boundary darts of its flip.** -/
theorem extremalGFaceProve_movePred_flip {M : CombMap.{v}} {F : Finset M.Face}
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M F d)
    {z : M.Dart → Bool} (hz : ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y → z x = z y)
    {d : M.Dart} (hd : d ∈ c) :
    movePred M z d = extremalGFaceProve_bd M (flipFaces M F z) d := by
  have e : movePred M z d = movePred M (extremalGFaceProve_colour M F (flipFaces M F z)) d := by
    rw [extremalGFaceProve_colour_flipFaces hz]
  exact e.trans (extremalGFaceProve_movePred_colour_of_mem hc hd)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_colourFace
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_colour
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_bd
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_colour_eq_false_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_bd_eq_true_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_bool_eq_of_false_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_bool_eq_of_true_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_colour_eq_of_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_mem_iff_alpha_of_not_walkKeep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_colour_step
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_colour_indep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_flipFaces_colour
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_colour_flipFaces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_exists_boundary
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_filter_bd_ne_nil
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_touch
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_movePred_colour_of_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_flip_union
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_flip_boundary
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_flip_ne
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFaceProve_movePred_flip
