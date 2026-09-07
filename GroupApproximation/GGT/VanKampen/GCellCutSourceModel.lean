import GroupApproximation.GGT.VanKampen.CellShellingWithGCellsModel

/-!
# A reduced two-relator source for the repaired region cut

This extends the six-dart shelling obstruction by a second relator monogon
at the exterior vertex. The two based relator values are distinct
transpositions, so the source is reduced. Cutting off that monogon retains
the bridged relator and its adjacent G-cell digon.
-/

namespace GroupApproximation.GGT.VanKampen.GCellCutSourceModel

open Equiv GroupApproximation.HullSC
open ExteriorArcCounterexample (G a b D)

def alpha : Perm (Fin 8) where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6]
  left_inv := by decide
  right_inv := by decide

def facePerm : Perm (Fin 8) where
  toFun := ![2, 0, 1, 4, 3, 7, 6, 5]
  invFun := ![1, 2, 0, 4, 3, 7, 6, 5]
  left_inv := by decide
  right_inv := by decide

def M : CombMap where
  Dart := Fin 8
  dartFintype := inferInstance
  alpha := alpha
  sigma := facePerm * alpha
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 8))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 8) n)

def faceClass : Fin 8 → Fin 4 := ![0, 0, 0, 1, 1, 3, 2, 3]
def faceRep : Fin 4 → Fin 8 := ![0, 3, 6, 5]

noncomputable def faceEquiv : M.Face ≃ Fin 4 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep
    (by decide) (by decide) (by decide)

def face (i : Fin 4) : M.Face := M.faceOf (faceRep i)

@[simp] theorem faceEquiv_face (i : Fin 4) : faceEquiv (face i) = i := by
  change faceClass (faceRep i) = i
  fin_cases i <;> rfl

theorem faceOf_eq_face (d : Fin 8) (i : Fin 4) :
    M.faceOf d = face i ↔ faceClass d = i := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face]
  rfl

theorem face_eq_iff (i j : Fin 4) : face i = face j ↔ i = j := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face, faceEquiv_face]

noncomputable def vertexEquiv : M.Vertex ≃ Fin 2 :=
  OrbitClassifier.orbitEquiv M.sigma (![0, 1, 1, 1, 1, 1, 1, 1] : Fin 8 → Fin 2)
    (![0, 1] : Fin 2 → Fin 8) (by decide) (by decide) (by decide)

theorem planar : M.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 8, Relation.EqvGen M.Adjacent 0 d := by
      have trans {d e f : M.Dart}
          (hde : Relation.EqvGen M.Adjacent d e)
          (hef : Relation.EqvGen M.Adjacent e f) :
          Relation.EqvGen M.Adjacent d f := .trans _ _ _ hde hef
      have h01 : Relation.EqvGen M.Adjacent 0 1 :=
        .rel _ _ (Or.inl rfl)
      have h12 : Relation.EqvGen M.Adjacent 1 2 :=
        .rel _ _ (Or.inr rfl)
      have h24 : Relation.EqvGen M.Adjacent 2 4 :=
        .rel _ _ (Or.inr rfl)
      have h47 : Relation.EqvGen M.Adjacent 4 7 := .rel _ _ (Or.inr rfl)
      have h76 : Relation.EqvGen M.Adjacent 7 6 := .rel _ _ (Or.inl rfl)
      have h65 : Relation.EqvGen M.Adjacent 6 5 := .rel _ _ (Or.inr rfl)
      have h53 : Relation.EqvGen M.Adjacent 5 3 := .rel _ _ (Or.inr rfl)
      have h04 := trans (trans h01 h12) h24
      have h07 := trans h04 h47
      have h06 := trans h07 h76
      have h05 := trans h06 h65
      intro d
      fin_cases d
      · exact .refl _
      · exact h01
      · exact trans h01 h12
      · exact trans h05 h53
      · exact h04
      · exact h05
      · exact h06
      · exact h07
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 2 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 4 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 8 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 4 := by omega
    rw [heq]
    norm_num

def faceDarts : Fin 4 → List (Fin 8) := ![[0, 2, 1], [3, 4], [6], [5, 7]]

noncomputable def indexedBoundary (i : Fin 4) : FaceBoundary M (face i) where
  darts := faceDarts i
  nonempty := by change faceDarts i ≠ ([] : List (Fin 8)); fin_cases i <;> decide
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

@[simp] theorem boundary_face_darts (i : Fin 4) :
    (boundary (face i)).darts = faceDarts i := by
  have htransport {f g : M.Face} (h : f = g) (B : FaceBoundary M f) :
      (h ▸ B).darts = B.darts := by cases h; rfl
  unfold boundary
  rw [htransport]
  exact congrArg faceDarts (faceEquiv_face i)

def label (d : Fin 8) : RelLetter G Empty :=
  .base ((![b, b⁻¹, a, a⁻¹, a, a⁻¹, b, b⁻¹] : Fin 8 → G) d)

def relator : List (RelLetter G Empty) := [.base b, .base a, .base b⁻¹]
def W : Set (List (RelLetter G Empty)) := {relator, [.base b]}

def relatorCell : RelatorCell M (face 3) W where
  face := face 0
  face_ne_outer := (face_eq_iff 0 3).not.mpr (by decide)
  word := relator
  word_mem := Or.inl rfl
  conjugator := b⁻¹
  reversed := false

def removedCell : RelatorCell M (face 3) W where
  face := face 2
  face_ne_outer := (face_eq_iff 2 3).not.mpr (by decide)
  word := [.base b]
  word_mem := Or.inr rfl
  conjugator := 1
  reversed := false

noncomputable def diagram : DiscDiagram W where
  toCombMap := M
  planar := planar
  label := label
  label_alpha := by
    intro d
    fin_cases d <;> exact congrArg RelLetter.base (by decide)
  outerFace := face 3
  faceBoundary := boundary
  relatorCells := [removedCell, relatorCell]
  relatorCell_faces_nodup := by
    change ([face 2, face 0] : List M.Face).Nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.nodup_nil, not_false_eq_true, and_true]
    exact (face_eq_iff 2 0).not.mpr (by decide)
  relatorCell_word := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · change [.base b] = (boundary (face 2)).darts.map label
      rw [boundary_face_darts]
      rfl
    · have h : C = relatorCell := List.mem_singleton.mp hC
      subst C
      change relator = (boundary (face 0)).darts.map label
      rw [boundary_face_darts]
      rfl
  inner_face := by
    intro f hf
    obtain ⟨i, rfl⟩ : ∃ i, face i = f := ⟨faceEquiv f, faceEquiv.left_inv f⟩
    fin_cases i
    · exact Or.inl ⟨relatorCell, List.mem_cons.mpr (Or.inr (List.mem_singleton_self _)), rfl⟩
    · right
      rw [boundary_face_darts]
      change a⁻¹ * (a * 1) = 1
      simp
    · exact Or.inl ⟨removedCell, List.mem_cons_self, rfl⟩
    · exact (hf rfl).elim
  boundary_product := by
    rw [boundary_face_darts]
    change (1 * (b * 1) * 1⁻¹) *
      ((b⁻¹ * (b * (a * (b⁻¹ * 1))) * (b⁻¹)⁻¹) * 1) =
      (b⁻¹)⁻¹ * ((a⁻¹)⁻¹ * 1)
    group

instance : DecidableEq diagram.toCombMap.Dart := inferInstanceAs (DecidableEq (Fin 8))
instance (n : ℕ) : OfNat diagram.toCombMap.Dart n := inferInstanceAs (OfNat (Fin 8) n)

/-- The two based values are not inverse to one another. -/
theorem cell_values_ne_one : removedCell.value * relatorCell.value ≠ 1 := by
  have h1 : removedCell.value = b := by
    change 1 * (b * 1) * 1⁻¹ = b
    group
  have h2 : relatorCell.value = a := by
    change b⁻¹ * (b * (a * (b⁻¹ * 1))) * (b⁻¹)⁻¹ = a
    group
  rw [h1, h2]
  decide

end GroupApproximation.GGT.VanKampen.GCellCutSourceModel

namespace GroupApproximation.GGT.VanKampen.DiscDiagram

universe u w v

/-- For exactly two listed relators, reducedness is their non-cancellation. -/
theorem reduced_of_two_cells {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (Delta : DiscDiagram.{u, w, v} W)
    (A B : RelatorCell Delta.toCombMap Delta.outerFace W)
    (hcells : Delta.relatorCells = [A, B]) (hne : A.value * B.value ≠ 1) :
    Delta.Reduced := by
  intro pre between suf C₁ C₂ hsplit
  rw [hcells] at hsplit
  have hlen := congrArg List.length hsplit
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  have hp : pre = [] := List.length_eq_zero_iff.mp (by omega)
  have hb : between = [] := List.length_eq_zero_iff.mp (by omega)
  have hs : suf = [] := List.length_eq_zero_iff.mp (by omega)
  subst pre between suf
  simp only [List.nil_append, List.cons.injEq] at hsplit
  obtain ⟨rfl, rfl, _⟩ := hsplit
  simpa using hne

end GroupApproximation.GGT.VanKampen.DiscDiagram

namespace GroupApproximation.GGT.VanKampen.GCellCutSourceModel

theorem diagram_reduced : diagram.Reduced :=
  diagram.reduced_of_two_cells removedCell relatorCell rfl cell_values_ne_one

end GroupApproximation.GGT.VanKampen.GCellCutSourceModel

#audit_closed_axioms GroupApproximation.GGT.VanKampen.GCellCutSourceModel.diagram_reduced
