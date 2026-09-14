import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWholeSectionWrapModel
import GroupApproximation.Meta.AxiomGuard

/-!
# Two exterior regions at a whole section: the least-area diagram

The map and the labelled least-area diagram of the model test for the inner-pocket route of the
whole-section two-arc face set producer (`SectionPocketFaceSetWholeSectionTwoArcInput`,
`Estimating/OsinPocketTwoArcSection.lean`).  The regions and the two pockets are in
`Estimating/OsinPocketInnerWalkModel.lean`.

The map has fourteen darts, the edges `{0,1}`, …, `{12,13}`, and three vertices: the base vertex
`v₀ = {0,8,13,5,6,7}`, `v₁ = {1,2,10,9}` and `v₂ = {3,4,12,11}`.  An outer triangle `v₀ v₁ v₂` and an
inner triangle on the same vertices are joined by three digons, and a loop at `v₀` holds a monogon
inside the inner triangle.  Its faces are:
* the relator cell `Π = [0,2,4,6]`, the inner triangle with the loop, reading `1 · a · 1 · 1`;
* the `G`-face `R_x = [1,8]`, the digon on `v₀ v₁`, reading `1 · 1`;
* the relator cell `K = [3,10]`, the digon on `v₁ v₂`, reading `a⁻¹ c`;
* the `G`-face `R_y = [5,12]`, the digon on `v₂ v₀`, reading `1 · 1`;
* the `G`-face `F = [7]`, the monogon in the loop, reading `1`;
* the exterior `O = [13,11,9]`, based at `13`, so the oriented outer darts are `[8,10,12]`: the arc of
  `R_x` at position `0`, the arc of `K` at `1`, and the arc of `R_y` ending at `|∂Δ| = 3`.

Over `Perm (Fin 3)` with `a` a transposition and `c` a 3-cycle both relator values are odd, and the
diagram reads `c`, which is even and not `1`, so the diagram has least area (`leastArea`).

## Manuscript status

Model test for infrastructure of `thm:hull` (Hull's small cancellation theorem, through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketInnerWalkModel

open Equiv GroupApproximation.HullSC
open OsinPocketPinchedTwoGonModel (D)
open OsinPocketFullArcLakeModel (ga gc sign_ga sign_gc sign_of_isRelatorProduct)

def mapAlpha : Perm (Fin 14) where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12]
  left_inv := by decide
  right_inv := by decide

def mapSigma : Perm (Fin 14) where
  toFun := ![8, 2, 10, 4, 12, 6, 7, 0, 13, 1, 9, 3, 11, 5]
  invFun := ![7, 9, 1, 11, 3, 13, 5, 6, 0, 10, 2, 12, 4, 8]
  left_inv := by decide
  right_inv := by decide

/-- The map: two triangles on three vertices joined by three digons, with a loop at the base vertex. -/
def M : CombMap where
  Dart := Fin 14
  dartFintype := inferInstance
  alpha := mapAlpha
  sigma := mapSigma
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 14))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 14) n)

def faceClass : Fin 14 → Fin 6 := ![0, 1, 0, 2, 0, 3, 0, 4, 1, 5, 2, 5, 3, 5]
def faceRep : Fin 6 → Fin 14 := ![0, 1, 3, 5, 7, 13]

noncomputable def faceEquiv : M.Face ≃ Fin 6 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep (by decide) (by decide) (by decide)

def face (i : Fin 6) : M.Face := M.faceOf (faceRep i)

@[simp] theorem faceEquiv_face (i : Fin 6) : faceEquiv (face i) = i := by
  change faceClass (faceRep i) = i
  fin_cases i <;> rfl

theorem faceOf_eq_face (d : Fin 14) (i : Fin 6) :
    M.faceOf d = face i ↔ faceClass d = i := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face]
  rfl

theorem face_eq_iff (i j : Fin 6) : face i = face j ↔ i = j := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face, faceEquiv_face]

def vertexClass : Fin 14 → Fin 3 := ![0, 1, 1, 2, 2, 0, 0, 0, 0, 1, 1, 2, 2, 0]
def vertexRep : Fin 3 → Fin 14 := ![0, 1, 3]

noncomputable def vertexEquiv : M.Vertex ≃ Fin 3 :=
  OrbitClassifier.orbitEquiv M.sigma vertexClass vertexRep (by decide) (by decide) (by decide)

theorem vertexEquiv_vertexOf (d : Fin 14) : vertexEquiv (M.vertexOf d) = vertexClass d :=
  rfl

theorem vertexOf_eq_iff (d e : Fin 14) : M.vertexOf d = M.vertexOf e ↔ vertexClass d = vertexClass e := by
  rw [← vertexEquiv.injective.eq_iff]
  rfl

theorem planar : M.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 14, Relation.EqvGen M.Adjacent 0 d := by
      have h0_1 : Relation.EqvGen M.Adjacent 0 1 := .rel _ _ (Or.inl rfl)
      have h0_8 : Relation.EqvGen M.Adjacent 0 8 := .rel _ _ (Or.inr rfl)
      have h8_13 : Relation.EqvGen M.Adjacent 8 13 := .rel _ _ (Or.inr rfl)
      have h13_5 : Relation.EqvGen M.Adjacent 13 5 := .rel _ _ (Or.inr rfl)
      have h5_6 : Relation.EqvGen M.Adjacent 5 6 := .rel _ _ (Or.inr rfl)
      have h6_7 : Relation.EqvGen M.Adjacent 6 7 := .rel _ _ (Or.inr rfl)
      have h1_2 : Relation.EqvGen M.Adjacent 1 2 := .rel _ _ (Or.inr rfl)
      have h2_10 : Relation.EqvGen M.Adjacent 2 10 := .rel _ _ (Or.inr rfl)
      have h10_9 : Relation.EqvGen M.Adjacent 10 9 := .rel _ _ (Or.inr rfl)
      have h2_3 : Relation.EqvGen M.Adjacent 2 3 := .rel _ _ (Or.inl rfl)
      have h3_4 : Relation.EqvGen M.Adjacent 3 4 := .rel _ _ (Or.inr rfl)
      have h4_12 : Relation.EqvGen M.Adjacent 4 12 := .rel _ _ (Or.inr rfl)
      have h12_11 : Relation.EqvGen M.Adjacent 12 11 := .rel _ _ (Or.inr rfl)
      have h0_13 := Relation.EqvGen.trans _ _ _ h0_8 h8_13
      have h0_5 := Relation.EqvGen.trans _ _ _ h0_13 h13_5
      have h0_6 := Relation.EqvGen.trans _ _ _ h0_5 h5_6
      have h0_7 := Relation.EqvGen.trans _ _ _ h0_6 h6_7
      have h0_2 := Relation.EqvGen.trans _ _ _ h0_1 h1_2
      have h0_10 := Relation.EqvGen.trans _ _ _ h0_2 h2_10
      have h0_9 := Relation.EqvGen.trans _ _ _ h0_10 h10_9
      have h0_3 := Relation.EqvGen.trans _ _ _ h0_2 h2_3
      have h0_4 := Relation.EqvGen.trans _ _ _ h0_3 h3_4
      have h0_12 := Relation.EqvGen.trans _ _ _ h0_4 h4_12
      have h0_11 := Relation.EqvGen.trans _ _ _ h0_12 h12_11
      intro d
      fin_cases d
      · exact .refl _
      · exact h0_1
      · exact h0_2
      · exact h0_3
      · exact h0_4
      · exact h0_5
      · exact h0_6
      · exact h0_7
      · exact h0_8
      · exact h0_9
      · exact h0_10
      · exact h0_11
      · exact h0_12
      · exact h0_13
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 3 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 6 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 14 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 7 := by omega
    rw [heq]
    norm_num

def faceDarts : Fin 6 → List (Fin 14) :=
  ![[0, 2, 4, 6], [1, 8], [3, 10], [5, 12], [7], [13, 11, 9]]

noncomputable def indexedBoundary (i : Fin 6) : FaceBoundary M (face i) where
  darts := faceDarts i
  nonempty := by change faceDarts i ≠ ([] : List (Fin 14)); fin_cases i <;> decide
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

@[simp] theorem boundary_face_darts (i : Fin 6) :
    (boundary (face i)).darts = faceDarts i := by
  have htransport {f g : M.Face} (h : f = g) (B : FaceBoundary M f) :
      (h ▸ B).darts = B.darts := by cases h; rfl
  unfold boundary
  rw [htransport]
  exact congrArg faceDarts (faceEquiv_face i)

/-! ## Labels and relator cells -/

abbrev G := Perm (Fin 3)

/-- `Π` reads `1 · a · 1 · 1`, `K` reads `a⁻¹ c`, the digons of the regions and the monogon read `1`, and
the exterior reads `1 · c⁻¹ · 1`. -/
def label (d : Fin 14) : RelLetter G Empty :=
  .base ((![1, 1, ga, ga⁻¹, 1, 1, 1, 1, 1, 1, gc, gc⁻¹, 1, 1] : Fin 14 → G) d)

def W : Set (List (RelLetter G Empty)) :=
  {[.base 1, .base ga, .base 1, .base 1], [.base ga⁻¹, .base gc]}

def cellP : RelatorCell M (face 5) W where
  face := face 0
  face_ne_outer := (face_eq_iff 0 5).not.mpr (by decide)
  word := [.base 1, .base ga, .base 1, .base 1]
  word_mem := Or.inl rfl
  conjugator := 1
  reversed := false

def cellK : RelatorCell M (face 5) W where
  face := face 2
  face_ne_outer := (face_eq_iff 2 5).not.mpr (by decide)
  word := [.base ga⁻¹, .base gc]
  word_mem := Or.inr rfl
  conjugator := 1
  reversed := false

/-- **The model as a disc diagram**, with the relator cells `Π` and `K`. -/
noncomputable def diagram : DiscDiagram W where
  toCombMap := M
  planar := planar
  label := label
  label_alpha := by
    intro d
    fin_cases d <;> exact congrArg RelLetter.base (by decide)
  outerFace := face 5
  faceBoundary := boundary
  relatorCells := [cellP, cellK]
  relatorCell_faces_nodup := by
    change [face 0, face 2].Nodup
    refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    rw [List.mem_singleton]
    exact (face_eq_iff 0 2).not.mpr (by decide)
  relatorCell_word := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · change [RelLetter.base (1 : G), RelLetter.base ga, RelLetter.base 1, RelLetter.base 1] =
        (boundary (face 0)).darts.map label
      rw [boundary_face_darts]
      rfl
    · obtain rfl := List.mem_singleton.mp hC
      change [RelLetter.base ga⁻¹, RelLetter.base gc] = (boundary (face 2)).darts.map label
      rw [boundary_face_darts]
      rfl
  inner_face := by
    intro f hf
    obtain ⟨i, rfl⟩ : ∃ i, face i = f := ⟨faceEquiv f, faceEquiv.left_inv f⟩
    fin_cases i
    · exact Or.inl ⟨cellP, by simp, rfl⟩
    · right
      rw [boundary_face_darts]
      decide
    · exact Or.inl ⟨cellK, by simp, rfl⟩
    · right
      rw [boundary_face_darts]
      decide
    · right
      rw [boundary_face_darts]
      decide
    · exact (hf rfl).elim
  boundary_product := by
    rw [boundary_face_darts]
    decide

instance : NeZero diagram.rCellCount := ⟨by decide⟩
instance (n : ℕ) : OfNat diagram.toCombMap.Dart n := inferInstanceAs (OfNat (Fin 14) n)
instance : DecidableEq diagram.toCombMap.Dart := inferInstanceAs (DecidableEq (Fin 14))

/-- The source cell `Π`. -/
def iP : Fin diagram.rCellCount := ⟨0, by decide⟩

/-- The kept cell `K`. -/
def iK : Fin diagram.rCellCount := ⟨1, by decide⟩

theorem letters : ∀ d, (symmetricLabelAlphabet D).IsLetter (diagram.label d) := fun _ =>
  Or.inl (Set.mem_univ _)

/-! ## Least area -/

theorem relator_signs : ∀ r ∈ RelLetter.listVal '' W, Perm.sign r = -1 := by
  rintro r ⟨word, hword, rfl⟩
  simp only [W, Set.mem_insert_iff, Set.mem_singleton_iff] at hword
  rcases hword with rfl | rfl
  · rw [show RelLetter.listVal ([.base 1, .base ga, .base 1, .base 1] : List (RelLetter G Empty)) =
        ga by decide]
    exact sign_ga
  · rw [show RelLetter.listVal ([.base ga⁻¹, .base gc] : List (RelLetter G Empty)) = ga⁻¹ * gc by
        decide, Perm.sign_mul, Perm.sign_inv, sign_ga, sign_gc, mul_one]

theorem boundaryValue_eq : diagram.boundaryValue = gc := by
  change RelLetter.listVal (RelWord.revInv ((boundary (face 5)).darts.map label)) = gc
  rw [boundary_face_darts]
  decide

/-- **The model has least area.** -/
theorem leastArea : diagram.LeastArea := by
  intro m hm
  rw [boundaryValue_eq] at hm
  have hsign := sign_of_isRelatorProduct relator_signs hm
  rw [sign_gc] at hsign
  change 2 ≤ m
  rcases m with _ | _ | m
  · exact absurd hm.eq_one_of_index_zero (by decide)
  · exact absurd hsign (by decide)
  · omega

/-! ## Arcs of `Π` and of the exterior -/

theorem cellDarts_iP : Embedded.cellDarts diagram iP = [0, 2, 4, 6] := by
  change (boundary (face 0)).darts = _
  rw [boundary_face_darts]
  rfl

theorem outerDarts_eq : Embedded.outerDarts diagram = [8, 10, 12] := by
  change ((boundary (face 5)).darts.reverse.map M.alpha) = _
  rw [boundary_face_darts]
  rfl

theorem boundaryWord_length : diagram.boundaryWord.length = 3 := by
  rw [← Embedded.dartWord_outerDarts, Embedded.dartWord, List.length_map, outerDarts_eq]
  rfl

end GroupApproximation.GGT.VanKampen.OsinPocketInnerWalkModel

#audit_closed_axioms GroupApproximation.GGT.VanKampen.OsinPocketInnerWalkModel.leastArea
#audit_closed_axioms GroupApproximation.GGT.VanKampen.OsinPocketInnerWalkModel.boundaryWord_length
