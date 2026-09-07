import GroupApproximation.GGT.VanKampen.Estimating.ContiguityGeometry
import GroupApproximation.GGT.VanKampen.CactusBoundary
import GroupApproximation.GGT.VanKampen.FaceShelling
import GroupApproximation.GGT.VanKampen.Estimating.PieceCore

/-!
# A positive-length geometric self-contiguity

The six-dart planar map has a relator triangle, a G-cell digon and an outer
monogon. Both sides of the digon meet different darts of the same relator
cell. This is a nonvacuity model of contiguity geometry, not a claim that the
example satisfies the small-cancellation hypotheses of Osin's loop argument.
-/

namespace GroupApproximation.GGT.VanKampen.SelfContiguityModel

open Equiv GroupApproximation.HullSC GroupApproximation.WordMetric

def alpha : Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by decide
  right_inv := by decide

def facePerm : Perm (Fin 6) where
  toFun := ![1, 2, 0, 4, 3, 5]
  invFun := ![2, 0, 1, 4, 3, 5]
  left_inv := by decide
  right_inv := by decide

def M : CombMap where
  Dart := Fin 6
  dartFintype := inferInstance
  alpha := alpha
  sigma := facePerm * alpha
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 6))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 6) n)

def faceClass : Fin 6 → Fin 3 := ![0, 0, 0, 1, 1, 2]
def faceRep : Fin 3 → Fin 6 := ![0, 3, 5]

noncomputable def faceEquiv : M.Face ≃ Fin 3 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep
    (by decide) (by decide) (by decide)

def face (i : Fin 3) : M.Face := M.faceOf (faceRep i)

@[simp] theorem faceEquiv_face (i : Fin 3) : faceEquiv (face i) = i := by
  change faceClass (faceRep i) = i
  fin_cases i <;> rfl

theorem faceOf_eq_face (d : Fin 6) (i : Fin 3) :
    M.faceOf d = face i ↔ faceClass d = i := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face]
  rfl

theorem face_eq_iff (i j : Fin 3) : face i = face j ↔ i = j := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face, faceEquiv_face]

noncomputable def vertexEquiv : M.Vertex ≃ Fin 2 :=
  OrbitClassifier.orbitEquiv M.sigma (![0, 1, 0, 1, 0, 0] : Fin 6 → Fin 2)
    (![0, 1] : Fin 2 → Fin 6) (by decide) (by decide) (by decide)

theorem planar : M.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 6, Relation.EqvGen M.Adjacent 0 d := by
      have trans {d e f : M.Dart}
          (hde : Relation.EqvGen M.Adjacent d e)
          (hef : Relation.EqvGen M.Adjacent e f) :
          Relation.EqvGen M.Adjacent d f := .trans _ _ _ hde hef
      have h03 : Relation.EqvGen M.Adjacent 0 3 := .rel _ _ (Or.inl rfl)
      have h31 : Relation.EqvGen M.Adjacent 3 1 := .rel _ _ (Or.inr rfl)
      have h04 : Relation.EqvGen M.Adjacent 0 4 := .rel _ _ (Or.inr rfl)
      have h42 : Relation.EqvGen M.Adjacent 4 2 := .rel _ _ (Or.inr rfl)
      have h25 : Relation.EqvGen M.Adjacent 2 5 := .rel _ _ (Or.inl rfl)
      intro d
      fin_cases d
      · exact .refl _
      · exact trans h03 h31
      · exact trans h04 h42
      · exact h03
      · exact h04
      · exact trans (trans h04 h42) h25
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 2 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 3 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 6 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 3 := by omega
    rw [heq]
    norm_num

def faceDarts : Fin 3 → List (Fin 6) := ![[0, 1, 2], [3, 4], [5]]

noncomputable def indexedBoundary (i : Fin 3) : FaceBoundary M (face i) where
  darts := faceDarts i
  nonempty := by change faceDarts i ≠ ([] : List (Fin 6)); fin_cases i <;> decide
  nodup := by fin_cases i <;> decide
  mem_iff := by
    intro d
    rw [faceOf_eq_face]
    fin_cases i <;> fin_cases d <;> decide
  chain := by fin_cases i <;> decide
  closes := by fin_cases i <;> decide
  length_eq_degree := by
    have h := closedOrbitList.length_eq_orbitDegree M.facePerm (faceRep i)
    have hd : closedOrbitList M.facePerm (faceRep i) = faceDarts i := by
      fin_cases i <;> decide
    rw [hd] at h
    exact h

noncomputable def boundary (f : M.Face) : FaceBoundary M f :=
  (faceEquiv.left_inv f) ▸ indexedBoundary (faceEquiv f)

@[simp] theorem boundary_face_darts (i : Fin 3) :
    (boundary (face i)).darts = faceDarts i := by
  have htransport {f g : M.Face} (h : f = g) (B : FaceBoundary M f) :
      (h ▸ B).darts = B.darts := by cases h; rfl
  unfold boundary
  rw [htransport]
  exact congrArg faceDarts (faceEquiv_face i)

abbrev G := Perm (Fin 1)

def D : RelGenSet G Empty where
  base := Set.univ
  fam := Empty.elim
  symmetricGenerating := by
    rw [Set.univ_union]
    exact ⟨fun _ _ => Set.mem_univ _, Subgroup.closure_univ⟩

def label (_ : Fin 6) : RelLetter G Empty := .base 1

def relator : List (RelLetter G Empty) := [.base 1, .base 1, .base 1]
def W : Set (List (RelLetter G Empty)) := {relator}

def relatorCell : RelatorCell M (face 2) W where
  face := face 0
  face_ne_outer := (face_eq_iff 0 2).not.mpr (by decide)
  word := relator
  word_mem := rfl
  conjugator := 1
  reversed := false

noncomputable def diagram : DiscDiagram W where
  toCombMap := M
  planar := planar
  label := label
  label_alpha := by intro d; simp [label, RelWord.inv]
  outerFace := face 2
  faceBoundary := boundary
  relatorCells := [relatorCell]
  relatorCell_faces_nodup := by simp
  relatorCell_word := by
    intro C hC
    have h : C = relatorCell := List.mem_singleton.mp hC
    subst C
    change relator = (boundary (face 0)).darts.map label
    rw [boundary_face_darts]
    rfl
  inner_face := by
    intro f hf
    obtain ⟨i, rfl⟩ : ∃ i, face i = f := ⟨faceEquiv f, faceEquiv.left_inv f⟩
    fin_cases i
    · exact Or.inl ⟨relatorCell, List.mem_singleton_self _, rfl⟩
    · right
      rw [boundary_face_darts]
      change (1 : G) * (1 * 1) = 1
      simp
    · exact (hf rfl).elim
  boundary_product := by
    rw [boundary_face_darts]
    change (1 : G) * (1 * (1 * (1 * 1))) * 1⁻¹ * 1 = 1⁻¹ * 1
    simp

instance : NeZero diagram.rCellCount := ⟨by decide⟩
instance (n : ℕ) : OfNat diagram.toCombMap.Dart n := inferInstanceAs (OfNat (Fin 6) n)
instance : DecidableEq diagram.toCombMap.Dart := inferInstanceAs (DecidableEq (Fin 6))

@[simp] theorem diagram_cellDarts : Embedded.cellDarts diagram 0 = [0, 1, 2] := by
  change (boundary (face 0)).darts = _
  rw [boundary_face_darts]
  rfl

def faces : Finset diagram.toCombMap.Face := {face 1}

theorem isBoundaryDart_iff (d : Fin 6) :
    Embedded.IsBoundaryDart diagram faces d ↔ d = 3 ∨ d = 4 := by
  change (M.faceOf d ∈ ({face 1} : Finset M.Face) ∧
    M.faceOf (M.alpha d) ∉ ({face 1} : Finset M.Face)) ↔ _
  simp only [Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

theorem step34 : Embedded.BoundaryStep diagram faces 3 4 :=
  ⟨(isBoundaryDart_iff 3).mpr (Or.inl rfl),
    (isBoundaryDart_iff 4).mpr (Or.inr rfl), .refl⟩

theorem step43 : Embedded.BoundaryStep diagram faces 4 3 :=
  ⟨(isBoundaryDart_iff 4).mpr (Or.inr rfl),
    (isBoundaryDart_iff 3).mpr (Or.inl rfl), .refl⟩

noncomputable def regionBoundary : Embedded.FaceSetBoundary diagram faces where
  faces_nonempty := Finset.singleton_nonempty _
  all_gCells := by
    intro f hf
    have h : f = face 1 := Finset.mem_singleton.mp hf
    subst f
    refine ⟨(face_eq_iff 1 2).not.mpr (by decide), ?_⟩
    change RelLetter.listVal ((boundary (face 1)).darts.map label) = 1
    rw [boundary_face_darts]
    change (1 : G) * (1 * 1) = 1
    simp
  cycle := [3, 4]
  cycle_nonempty := List.cons_ne_nil _ _
  cycle_nodup := by decide
  cycle_mem_iff := by
    intro d
    rw [isBoundaryDart_iff]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rfl
  cycle_chain := by
    simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using step34
  cycle_closes := step43

def sourceArc : Embedded.CyclicArc (Embedded.cellDarts diagram 0) where
  start := ⟨0, Nat.zero_lt_succ _⟩
  length := 1
  length_le := by rw [diagram_cellDarts]; decide

def targetArc : Embedded.CyclicArc (Embedded.targetDarts diagram (some 0)) where
  start := ⟨1, by
    change 1 < (Embedded.cellDarts diagram 0).length + 1
    rw [diagram_cellDarts]
    decide⟩
  length := 1
  length_le := by
    change 1 ≤ (Embedded.cellDarts diagram 0).length
    rw [diagram_cellDarts]
    decide

noncomputable def region : Embedded.ContiguityGeometry D 0 diagram faces where
  boundary := regionBoundary
  source := 0
  target := some 0
  sourceArc := sourceArc
  targetArc := targetArc
  rightSide := []
  leftSide := []
  boundary_decomposition := by
    change [3, 4] = sourceArc.reverseDarts ++ [] ++ targetArc.reverseDarts ++ []
    simp only [Embedded.CyclicArc.reverseDarts, Embedded.CyclicArc.darts,
      Embedded.CyclicArc.rotated, sourceArc, targetArc, Embedded.targetDarts, diagram_cellDarts]
    rfl
  rightSide_length_le := le_rfl
  leftSide_length_le := le_rfl
  rightSide_norm_le := by change wordNorm D.alphabet.carrier 1 ≤ 0; rw [wordNorm_one]
  leftSide_norm_le := by change wordNorm D.alphabet.carrier 1 ≤ 0; rw [wordNorm_one]
  pasting := by
    refine ⟨[face 1], ?_⟩
    have h := Embedded.shelling_oneFace (Delta := diagram) (faces := faces)
      (face := face 1) (Finset.mem_singleton_self _) 0
    rw [List.rotate_zero] at h
    change Embedded.FaceShelling diagram faces [face 1] ((boundary (face 1)).darts) at h
    rw [boundary_face_darts] at h
    exact h

/-- A genuine positive-length self-contiguity on an actual reduced planar
diagram. No small-cancellation hypothesis is asserted for this example. -/
theorem positive_self_contiguity :
    diagram.Reduced ∧ region.target = some region.source ∧
      region.sourceArc.length = 1 ∧ region.targetArc.length = 1 := by
  exact ⟨reduced_of_rCellCount_le_one diagram (by decide), rfl, rfl, rfl⟩

/-- The old projection omits this concrete geometric witness. -/
theorem region_not_in_historical_image :
    ¬ ∃ H : Embedded.Contiguity D 0 diagram faces, H.toGeometry = region := by
  rintro ⟨H, h⟩
  have hs : H.source = 0 := congrArg (fun J => J.source) h
  have ht : H.target = some 0 := congrArg (fun J => J.target) h
  exact H.target_ne_source 0 ht hs

end GroupApproximation.GGT.VanKampen.SelfContiguityModel

#audit_closed_axioms GroupApproximation.GGT.VanKampen.SelfContiguityModel.positive_self_contiguity
#audit_closed_axioms GroupApproximation.GGT.VanKampen.SelfContiguityModel.region_not_in_historical_image
