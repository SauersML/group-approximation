import GroupApproximation.GGT.VanKampen.CombMap
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.List.Nodup
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 09: cutting a face set along a closed boundary

Step 3 of the proof in `GreendlingerLeaf/Piece09/Walk.lean`, as a statement over a combinatorial
map.  Let `Pf ⊇ Rx` be two face sets.  Suppose the boundary darts of `Pf` are those of
`A ++ Mid ++ B` without repetition, the boundary darts of `Rx` are those of `Mid ++ L`, and no dart of
`L` bounds `Pf`.  Then the boundary darts of `Pf \ Rx` are those of `A ++ L⁻¹ ++ B`, where
`L⁻¹ = L.reverse.map alpha`, without repetition.

* `faceOf_not_mem_of_mem_walk`: a boundary dart of `Pf` outside `Mid` does not start in `Rx`.
* `mem_cut_of_mem_inv`: a reversed dart of `L` bounds `Pf \ Rx`.
* `cut_mem_iff`: the boundary darts of `Pf \ Rx`.
* `cut_nodup`: `A ++ L⁻¹ ++ B` has no repetition.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09

universe u

section Cut

variable {M : CombMap.{u}} {Pf Rx : Finset M.Face} {A Mid B L : List M.Dart}

/-- A dart of `A` is not a dart of `Mid`. -/
theorem not_mem_mid_of_mem_left (h2 : (A ++ Mid ++ B).Nodup) {d : M.Dart} (hd : d ∈ A) :
    d ∉ Mid :=
  fun hM => (List.nodup_append.mp (List.nodup_append.mp h2).1).2.2 d hd d hM rfl

/-- A dart of `B` is not a dart of `Mid`. -/
theorem not_mem_mid_of_mem_right (h2 : (A ++ Mid ++ B).Nodup) {d : M.Dart} (hd : d ∈ B) :
    d ∉ Mid :=
  fun hM => (List.nodup_append.mp h2).2.2 d (List.mem_append_right A hM) d hd rfl

/-- **A boundary dart of `Pf` outside `Mid` does not start in `Rx`.** -/
theorem faceOf_not_mem_of_mem_walk
    (h1 : ∀ d, d ∈ A ++ Mid ++ B ↔ M.faceOf d ∈ Pf ∧ M.faceOf (M.alpha d) ∉ Pf)
    (h3 : ∀ d, d ∈ Mid ++ L ↔ M.faceOf d ∈ Rx ∧ M.faceOf (M.alpha d) ∉ Rx)
    (h4 : Rx ⊆ Pf) (h5 : ∀ l ∈ L, l ∉ A ++ Mid ++ B) {d : M.Dart}
    (hd : d ∈ A ++ Mid ++ B) (hmid : d ∉ Mid) : M.faceOf d ∉ Rx := by
  intro hR
  have hout : M.faceOf (M.alpha d) ∉ Rx := fun h => ((h1 d).mp hd).2 (h4 h)
  rcases List.mem_append.mp ((h3 d).mpr ⟨hR, hout⟩) with hM | hL
  · exact hmid hM
  · exact h5 d hL hd

/-- **A reversed dart of `L` bounds `Pf \ Rx`**: it starts in `Pf` outside `Rx` and ends in `Rx`. -/
theorem mem_cut_of_mem_inv
    (h1 : ∀ d, d ∈ A ++ Mid ++ B ↔ M.faceOf d ∈ Pf ∧ M.faceOf (M.alpha d) ∉ Pf)
    (h3 : ∀ d, d ∈ Mid ++ L ↔ M.faceOf d ∈ Rx ∧ M.faceOf (M.alpha d) ∉ Rx)
    (h4 : Rx ⊆ Pf) (h5 : ∀ l ∈ L, l ∉ A ++ Mid ++ B) {d : M.Dart}
    (hd : d ∈ L.reverse.map M.alpha) :
    (M.faceOf d ∈ Pf ∧ M.faceOf d ∉ Rx) ∧
      ¬ (M.faceOf (M.alpha d) ∈ Pf ∧ M.faceOf (M.alpha d) ∉ Rx) := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hd
  rw [List.mem_reverse] at hl
  have hlR := (h3 l).mp (List.mem_append_right Mid hl)
  rw [M.alpha_involutive l]
  refine ⟨⟨?_, hlR.2⟩, fun h => h.2 hlR.1⟩
  by_contra hP
  exact h5 l hl ((h1 l).mpr ⟨h4 hlR.1, hP⟩)

/-- A boundary dart of `Pf` outside `Mid` bounds `Pf \ Rx`. -/
theorem mem_cut_of_mem_walk
    (h1 : ∀ d, d ∈ A ++ Mid ++ B ↔ M.faceOf d ∈ Pf ∧ M.faceOf (M.alpha d) ∉ Pf)
    (h3 : ∀ d, d ∈ Mid ++ L ↔ M.faceOf d ∈ Rx ∧ M.faceOf (M.alpha d) ∉ Rx)
    (h4 : Rx ⊆ Pf) (h5 : ∀ l ∈ L, l ∉ A ++ Mid ++ B) {d : M.Dart}
    (hd : d ∈ A ++ Mid ++ B) (hmid : d ∉ Mid) :
    (M.faceOf d ∈ Pf ∧ M.faceOf d ∉ Rx) ∧
      ¬ (M.faceOf (M.alpha d) ∈ Pf ∧ M.faceOf (M.alpha d) ∉ Rx) :=
  ⟨⟨((h1 d).mp hd).1, faceOf_not_mem_of_mem_walk h1 h3 h4 h5 hd hmid⟩,
    fun h => ((h1 d).mp hd).2 h.1⟩

/-- A boundary dart of `Pf \ Rx` lies on `A ++ L⁻¹ ++ B`. -/
theorem mem_of_mem_cut
    (h1 : ∀ d, d ∈ A ++ Mid ++ B ↔ M.faceOf d ∈ Pf ∧ M.faceOf (M.alpha d) ∉ Pf)
    (h3 : ∀ d, d ∈ Mid ++ L ↔ M.faceOf d ∈ Rx ∧ M.faceOf (M.alpha d) ∉ Rx) {d : M.Dart}
    (hP : M.faceOf d ∈ Pf) (hR : M.faceOf d ∉ Rx)
    (hα : ¬ (M.faceOf (M.alpha d) ∈ Pf ∧ M.faceOf (M.alpha d) ∉ Rx)) :
    d ∈ A ++ L.reverse.map M.alpha ++ B := by
  by_cases hαP : M.faceOf (M.alpha d) ∈ Pf
  · have hαR : M.faceOf (M.alpha d) ∈ Rx := by
      by_contra hn
      exact hα ⟨hαP, hn⟩
    have hR' : M.faceOf (M.alpha (M.alpha d)) ∉ Rx := by
      rw [M.alpha_involutive d]
      exact hR
    rcases List.mem_append.mp ((h3 (M.alpha d)).mpr ⟨hαR, hR'⟩) with hM | hL
    · have hw := (h1 (M.alpha d)).mp (List.mem_append_left B (List.mem_append_right A hM))
      rw [M.alpha_involutive d] at hw
      exact absurd hP hw.2
    · refine List.mem_append_left B (List.mem_append_right A ?_)
      rw [List.mem_map]
      exact ⟨M.alpha d, List.mem_reverse.mpr hL, M.alpha_involutive d⟩
  · rcases List.mem_append.mp ((h1 d).mpr ⟨hP, hαP⟩) with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · exact List.mem_append_left B (List.mem_append_left _ hw)
      · exact absurd ((h3 d).mp (List.mem_append_left L hw)).1 hR
    · exact List.mem_append_right _ hw

/-- **The boundary darts of `Pf \ Rx`** are the darts of `A ++ L⁻¹ ++ B`. -/
theorem cut_mem_iff [DecidableEq M.Face]
    (h1 : ∀ d, d ∈ A ++ Mid ++ B ↔ M.faceOf d ∈ Pf ∧ M.faceOf (M.alpha d) ∉ Pf)
    (h2 : (A ++ Mid ++ B).Nodup)
    (h3 : ∀ d, d ∈ Mid ++ L ↔ M.faceOf d ∈ Rx ∧ M.faceOf (M.alpha d) ∉ Rx)
    (h4 : Rx ⊆ Pf) (h5 : ∀ l ∈ L, l ∉ A ++ Mid ++ B) (d : M.Dart) :
    d ∈ A ++ L.reverse.map M.alpha ++ B ↔
      M.faceOf d ∈ Pf \ Rx ∧ M.faceOf (M.alpha d) ∉ Pf \ Rx := by
  rw [Finset.mem_sdiff, Finset.mem_sdiff]
  constructor
  · intro hd
    rcases List.mem_append.mp hd with hd | hd
    · rcases List.mem_append.mp hd with hd | hd
      · exact mem_cut_of_mem_walk h1 h3 h4 h5
          (List.mem_append_left B (List.mem_append_left Mid hd)) (not_mem_mid_of_mem_left h2 hd)
      · exact mem_cut_of_mem_inv h1 h3 h4 h5 hd
    · exact mem_cut_of_mem_walk h1 h3 h4 h5 (List.mem_append_right (A ++ Mid) hd)
        (not_mem_mid_of_mem_right h2 hd)
  · rintro ⟨⟨hP, hR⟩, hα⟩
    exact mem_of_mem_cut h1 h3 hP hR hα

/-- **`A ++ L⁻¹ ++ B` has no repetition.** -/
theorem cut_nodup
    (h1 : ∀ d, d ∈ A ++ Mid ++ B ↔ M.faceOf d ∈ Pf ∧ M.faceOf (M.alpha d) ∉ Pf)
    (h2 : (A ++ Mid ++ B).Nodup) (hL : L.Nodup) (h3' : ∀ l ∈ L, M.faceOf l ∈ Rx)
    (h4 : Rx ⊆ Pf) : (A ++ L.reverse.map M.alpha ++ B).Nodup := by
  have hperm : (A ++ L.reverse.map M.alpha ++ B).Perm (A ++ B ++ L.reverse.map M.alpha) := by
    rw [List.append_assoc A (L.reverse.map M.alpha) B,
      List.append_assoc A B (L.reverse.map M.alpha)]
    exact List.Perm.append_left A List.perm_append_comm
  have hsub : A ++ B <+ A ++ Mid ++ B :=
    (List.sublist_append_left A Mid).append (List.Sublist.refl B)
  rw [hperm.nodup_iff, List.nodup_append]
  refine ⟨List.Nodup.sublist hsub h2, (List.nodup_reverse.mpr hL).map M.alpha.injective, ?_⟩
  intro a ha b hb hab
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hb
  subst hab
  have hw := (h1 (M.alpha l)).mp (hsub.subset ha)
  rw [M.alpha_involutive l] at hw
  exact hw.2 (h4 (h3' l (List.mem_reverse.mp hl)))

end Cut

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.not_mem_mid_of_mem_left
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.not_mem_mid_of_mem_right
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.faceOf_not_mem_of_mem_walk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.mem_cut_of_mem_inv
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.mem_cut_of_mem_walk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.mem_of_mem_cut
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.cut_mem_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.cut_nodup
