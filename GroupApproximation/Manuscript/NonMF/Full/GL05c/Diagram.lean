import GroupApproximation.Manuscript.NonMF.Full.GL05c.Map
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchedTwoGonModel
import GroupApproximation.GroupTheory.NormalClosureProduct
import GroupApproximation.Meta.AxiomGuard

/-!
# The labelled diagram of the counterexample to WO-GL05-2'

The map of `Full/GL05c/Map.lean` as a disc diagram over `G = Perm (Fin 3)`.

* Labels: the loop `p = {0,1}` reads the transposition `x = (0 1)` and the loop `e = {14,15}`
  reads `y = (1 2)`.  Every other dart reads `1`.
* Relator cells: the source cell `S = [9,14,11,13]` reads `1 y 1 1` and `P = [0]` reads `x`.
  The faces `R1`, `Q1`, `R2`, `Q2` read `1` and are `G`-faces.  The exterior `O` reads `x 1 1 1 y`.
* `leastArea`: both relators are odd and the boundary value `y x` is even and nontrivial.  So every
  relator product of it has at least two factors.
* `label_isLetter`: the base alphabet of `D` is all of `G`.

## Manuscript status

Infrastructure for `thm:hull` (`non_mf_groups_exist.tex`, tex 2121, Hull's small cancellation
theorem, through Osin's Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL05c.Model

open Equiv GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.OsinPocketPinchedTwoGonModel (G gx gy D)

/-- The loop `p` reads `x`, the loop `e` reads `y`, and every other dart reads `1`. -/
def label (d : Fin 16) : GGT.RelLetter G Empty :=
  .base ((![gx, gx, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, gy, gy] : Fin 16 → G) d)

/-- The word of the source cell `S`. -/
def sWord : List (GGT.RelLetter G Empty) := [.base 1, .base gy, .base 1, .base 1]

/-- The word of the cell `P`. -/
def pWord : List (GGT.RelLetter G Empty) := [.base gx]

/-- The relators `1 y 1 1` and `x`. -/
def W : Set (List (GGT.RelLetter G Empty)) := {sWord, pWord}

/-- The source cell `S`. -/
def sCell : RelatorCell M (face 6) W where
  face := face 5
  face_ne_outer := (face_eq_iff 5 6).not.mpr (by decide)
  word := sWord
  word_mem := Or.inl rfl
  conjugator := 1
  reversed := false

/-- The cell `P`. -/
def pCell : RelatorCell M (face 6) W where
  face := face 0
  face_ne_outer := (face_eq_iff 0 6).not.mpr (by decide)
  word := pWord
  word_mem := Or.inr rfl
  conjugator := 1
  reversed := false

/-- **The diagram of the counterexample**, with relator cells `S` and `P`. -/
noncomputable def diagram : DiscDiagram W where
  toCombMap := M
  planar := planar
  label := label
  label_alpha := by
    intro d
    fin_cases d <;> exact congrArg GGT.RelLetter.base (by decide)
  outerFace := face 6
  faceBoundary := boundary
  relatorCells := [sCell, pCell]
  relatorCell_faces_nodup := by
    change [face 5, face 0].Nodup
    refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    rw [List.mem_singleton]
    exact (face_eq_iff 5 0).not.mpr (by decide)
  relatorCell_word := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · change sWord = (boundary (face 5)).darts.map label
      rw [boundary_face_darts]
      rfl
    · obtain rfl := List.mem_singleton.mp hC
      change pWord = (boundary (face 0)).darts.map label
      rw [boundary_face_darts]
      rfl
  inner_face := by
    intro f hf
    obtain ⟨i, rfl⟩ : ∃ i, face i = f := ⟨faceEquiv f, faceEquiv.left_inv f⟩
    fin_cases i
    · exact Or.inl ⟨pCell, List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)), rfl⟩
    · refine Or.inr ?_
      change GGT.RelLetter.listVal ((boundary (face 1)).darts.map label) = 1
      rw [boundary_face_darts]
      decide
    · refine Or.inr ?_
      change GGT.RelLetter.listVal ((boundary (face 2)).darts.map label) = 1
      rw [boundary_face_darts]
      decide
    · refine Or.inr ?_
      change GGT.RelLetter.listVal ((boundary (face 3)).darts.map label) = 1
      rw [boundary_face_darts]
      decide
    · refine Or.inr ?_
      change GGT.RelLetter.listVal ((boundary (face 4)).darts.map label) = 1
      rw [boundary_face_darts]
      decide
    · exact Or.inl ⟨sCell, List.mem_cons.mpr (Or.inl rfl), rfl⟩
    · exact (hf rfl).elim
  boundary_product := by
    rw [boundary_face_darts]
    decide

instance diagram_ofNat (n : ℕ) : OfNat diagram.toCombMap.Dart n :=
  inferInstanceAs (OfNat (Fin 16) n)
instance diagram_decidableEq : DecidableEq diagram.toCombMap.Dart :=
  inferInstanceAs (DecidableEq (Fin 16))

/-- The index of the source cell `S`. -/
noncomputable def sIndex : Fin diagram.rCellCount := ⟨0, by decide⟩

/-- The index of the cell `P`. -/
noncomputable def pIndex : Fin diagram.rCellCount := ⟨1, by decide⟩

/-! ## Least area -/

/-- **A relator product of odd relators has the parity of its count.** -/
theorem sign_of_isRelatorProduct {R : Set G} (hR : ∀ r ∈ R, Perm.sign r = -1) {n : ℕ} {w : G}
    (h : RelatorDefectBudget.IsRelatorProduct R n w) :
    Perm.sign w = if n % 2 = 0 then 1 else -1 := by
  induction h with
  | one => simp
  | base hr => simp [hR _ hr]
  | inv _ ih => rw [Perm.sign_inv, ih]
  | conj c _ ih =>
      rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, ih, mul_right_comm, Int.units_mul_self,
        one_mul]
  | @mul m k a b _ _ iha ihb =>
      rw [Perm.sign_mul, iha, ihb, Nat.add_mod]
      rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
        rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;> simp [hm, hk]

theorem sign_gx : Perm.sign gx = -1 := Perm.sign_swap (by decide)

theorem sign_gy : Perm.sign gy = -1 := Perm.sign_swap (by decide)

theorem sign_boundary : Perm.sign (gy * gx) = 1 := by
  rw [Perm.sign_mul, sign_gy, sign_gx]
  decide

theorem relator_signs : ∀ r ∈ GGT.RelLetter.listVal '' W, Perm.sign r = -1 := by
  rintro r ⟨word, hword, rfl⟩
  simp only [W, Set.mem_insert_iff, Set.mem_singleton_iff] at hword
  rcases hword with rfl | rfl
  · rw [show GGT.RelLetter.listVal sWord = gy by decide]
    exact sign_gy
  · rw [show GGT.RelLetter.listVal pWord = gx by decide]
    exact sign_gx

theorem boundaryValue_eq : diagram.boundaryValue = gy * gx := by
  change GGT.RelLetter.listVal
    (HullSC.RelWord.revInv ((boundary (face 6)).darts.map label)) = gy * gx
  rw [boundary_face_darts]
  decide

/-- **The diagram has least area.** -/
theorem leastArea : diagram.LeastArea := by
  intro m hm
  rw [boundaryValue_eq] at hm
  have hsign := sign_of_isRelatorProduct relator_signs hm
  rw [sign_boundary] at hsign
  change 2 ≤ m
  rcases m with _ | _ | m
  · exact absurd hm.eq_one_of_index_zero (by decide)
  · exact absurd hsign (by decide)
  · omega

/-- **The labels are letters** of the symmetrized alphabet. -/
theorem label_isLetter (d : diagram.toCombMap.Dart) :
    (symmetricLabelAlphabet D).IsLetter (diagram.label d) :=
  Or.inl (Set.mem_univ _)

/-! ## The source cell, the exterior and the sides -/

theorem cellDarts_sIndex : Embedded.cellDarts diagram sIndex = [9, 14, 11, 13] := by
  change (boundary (face 5)).darts = _
  rw [boundary_face_darts]
  rfl

theorem outerDarts_eq : Embedded.outerDarts diagram = [14, 2, 6, 4, 0] := by
  change (boundary (face 6)).darts.reverse.map M.alpha = _
  rw [boundary_face_darts]
  rfl

theorem empty_side_norm :
    WordMetric.wordNorm D.alphabet.carrier (GGT.RelLetter.listVal
      (Embedded.dartWord diagram ([] : List diagram.toCombMap.Dart))) ≤ 1 :=
  (Nat.le_of_eq (WordMetric.wordNorm_one _)).trans (Nat.zero_le _)

theorem one_side_norm :
    WordMetric.wordNorm D.alphabet.carrier (GGT.RelLetter.listVal
      (Embedded.dartWord diagram ([0] : List diagram.toCombMap.Dart))) ≤ 1 :=
  WordMetric.wordNorm_le_one_of_mem (Or.inl (Set.mem_univ _))

end GroupApproximation.Full.GL05c.Model

#audit_axioms GroupApproximation.Full.GL05c.Model.diagram
#audit_axioms GroupApproximation.Full.GL05c.Model.leastArea
#audit_axioms GroupApproximation.Full.GL05c.Model.label_isLetter
#audit_axioms GroupApproximation.Full.GL05c.Model.cellDarts_sIndex
#audit_axioms GroupApproximation.Full.GL05c.Model.outerDarts_eq
