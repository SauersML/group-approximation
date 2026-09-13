import GroupApproximation.GGT.VanKampen.CactusBoundary
import GroupApproximation.GGT.VanKampen.FaceShelling
import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.Meta.AxiomGuard

/-!
# Two exterior regions pinched at one vertex

A model test for the zero-cell merge of Osin, arXiv:math/0411039v3, proof of Lemma 9.7(a):
"Finally inside every 2-gon `ef` of `Φ'_M` there is a vertex of `Φ_M` since otherwise one can
include the ε-contiguity subdiagrams corresponding to the edges `e` and `f` of `Φ'_M` into a
single ε-contiguity subdiagram in the obvious way, contrary to the definition of `M`."

The map has ten darts.  Its faces are a relator cell `Π = [0,1,2]`, two `G`-cell digons
`a = [3,4]` and `b = [5,6]`, and the exterior face `[7,9,8]`.  The digon `a` joins the first
letter of `Π` to the first boundary letter, and `b` joins the second letter to the second.  The
two digons meet only at the vertex `{1,3,6,8}`, so the pocket between them has no face.

The face set `{a, b}` has four boundary darts and no internal dart.  So a boundary step is one
turn of `facePerm`, which swaps the darts of each digon, and no duplicate-free cycle through all
four darts closes up (`no_faceSetBoundary`).  An `Embedded.FaceSetBoundary` of the merged face set
does not exist, hence no `Embedded.Contiguity` on it (`no_contiguity`): a producer of the merge
through the face-set boundary of `a ∪ b` fails at a pinch, and the merged region has to be built
in another O-equivalent diagram.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)); certifies
no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketPinchedTwoGonModel

open Equiv GroupApproximation.HullSC GroupApproximation.WordMetric

def alpha : Perm (Fin 10) where
  toFun := ![3, 5, 7, 0, 8, 1, 9, 2, 4, 6]
  invFun := ![3, 5, 7, 0, 8, 1, 9, 2, 4, 6]
  left_inv := by decide
  right_inv := by decide

def facePerm : Perm (Fin 10) where
  toFun := ![1, 2, 0, 4, 3, 6, 5, 9, 7, 8]
  invFun := ![2, 0, 1, 4, 3, 6, 5, 8, 9, 7]
  left_inv := by decide
  right_inv := by decide

def M : CombMap where
  Dart := Fin 10
  dartFintype := inferInstance
  alpha := alpha
  sigma := facePerm * alpha
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 10))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 10) n)

def faceClass : Fin 10 → Fin 4 := ![0, 0, 0, 1, 1, 2, 2, 3, 3, 3]
def faceRep : Fin 4 → Fin 10 := ![0, 3, 5, 7]

noncomputable def faceEquiv : M.Face ≃ Fin 4 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep
    (by decide) (by decide) (by decide)

def face (i : Fin 4) : M.Face := M.faceOf (faceRep i)

@[simp] theorem faceEquiv_face (i : Fin 4) : faceEquiv (face i) = i := by
  change faceClass (faceRep i) = i
  fin_cases i <;> rfl

theorem faceOf_eq_face (d : Fin 10) (i : Fin 4) :
    M.faceOf d = face i ↔ faceClass d = i := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face]
  rfl

theorem face_eq_iff (i j : Fin 4) : face i = face j ↔ i = j := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face, faceEquiv_face]

noncomputable def vertexEquiv : M.Vertex ≃ Fin 3 :=
  OrbitClassifier.orbitEquiv M.sigma (![0, 1, 2, 1, 0, 2, 1, 0, 1, 2] : Fin 10 → Fin 3)
    (![0, 1, 2] : Fin 3 → Fin 10) (by decide) (by decide) (by decide)

theorem planar : M.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 10, Relation.EqvGen M.Adjacent 0 d := by
      have trans {d e f : M.Dart}
          (hde : Relation.EqvGen M.Adjacent d e)
          (hef : Relation.EqvGen M.Adjacent e f) :
          Relation.EqvGen M.Adjacent d f := .trans _ _ _ hde hef
      have h03 : Relation.EqvGen M.Adjacent 0 3 := .rel _ _ (Or.inl rfl)
      have h04 : Relation.EqvGen M.Adjacent 0 4 := .rel _ _ (Or.inr rfl)
      have h47 : Relation.EqvGen M.Adjacent 4 7 := .rel _ _ (Or.inr rfl)
      have h31 : Relation.EqvGen M.Adjacent 3 1 := .rel _ _ (Or.inr rfl)
      have h15 : Relation.EqvGen M.Adjacent 1 5 := .rel _ _ (Or.inl rfl)
      have h52 : Relation.EqvGen M.Adjacent 5 2 := .rel _ _ (Or.inr rfl)
      have h16 : Relation.EqvGen M.Adjacent 1 6 := .rel _ _ (Or.inr rfl)
      have h68 : Relation.EqvGen M.Adjacent 6 8 := .rel _ _ (Or.inr rfl)
      have h29 : Relation.EqvGen M.Adjacent 2 9 := .rel _ _ (Or.inr rfl)
      intro d
      fin_cases d
      · exact .refl _
      · exact trans h03 h31
      · exact trans (trans (trans h03 h31) h15) h52
      · exact h03
      · exact h04
      · exact trans (trans h03 h31) h15
      · exact trans (trans h03 h31) h16
      · exact trans h04 h47
      · exact trans (trans (trans h03 h31) h16) h68
      · exact trans (trans (trans (trans h03 h31) h15) h52) h29
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 3 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 4 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 10 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 5 := by omega
    rw [heq]
    norm_num

def faceDarts : Fin 4 → List (Fin 10) := ![[0, 1, 2], [3, 4], [5, 6], [7, 9, 8]]

noncomputable def indexedBoundary (i : Fin 4) : FaceBoundary M (face i) where
  darts := faceDarts i
  nonempty := by change faceDarts i ≠ ([] : List (Fin 10)); fin_cases i <;> decide
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

abbrev G := Perm (Fin 3)

def gx : G := Equiv.swap 0 1
def gy : G := Equiv.swap 1 2
def gz : G := Equiv.swap 0 2

def D : RelGenSet G Empty where
  base := Set.univ
  fam := Empty.elim
  symmetricGenerating := by
    rw [Set.univ_union]
    exact ⟨fun _ _ => Set.mem_univ _, Subgroup.closure_univ⟩

/-- The darts of `Π` read `x y z`; each digon reads a letter and its inverse. -/
def label (d : Fin 10) : RelLetter G Empty :=
  .base ((![gx, gy, gz, gx⁻¹, gx, gy⁻¹, gy, gz⁻¹, gx⁻¹, gy⁻¹] : Fin 10 → G) d)

def relator : List (RelLetter G Empty) := [.base gx, .base gy, .base gz]
def W : Set (List (RelLetter G Empty)) := {relator}

def relatorCell : RelatorCell M (face 3) W where
  face := face 0
  face_ne_outer := (face_eq_iff 0 3).not.mpr (by decide)
  word := relator
  word_mem := rfl
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
      first
        | decide
        | (change gx⁻¹ * (gx * 1) = 1; simp)
    · right
      rw [boundary_face_darts]
      first
        | decide
        | (change gy⁻¹ * (gy * 1) = 1; simp)
    · exact (hf rfl).elim
  boundary_product := by
    rw [boundary_face_darts]
    first
      | decide
      | (change (1 : G) * (gx * (gy * (gz * 1))) * (1 : G)⁻¹ * 1 =
            (gx⁻¹)⁻¹ * ((gy⁻¹)⁻¹ * ((gz⁻¹)⁻¹ * 1)); group)

instance : NeZero diagram.rCellCount := ⟨by decide⟩
instance (n : ℕ) : OfNat diagram.toCombMap.Dart n := inferInstanceAs (OfNat (Fin 10) n)
instance : DecidableEq diagram.toCombMap.Dart := inferInstanceAs (DecidableEq (Fin 10))

@[simp] theorem diagram_cellDarts : Embedded.cellDarts diagram 0 = [0, 1, 2] := by
  change (boundary (face 0)).darts = _
  rw [boundary_face_darts]
  rfl

@[simp] theorem diagram_outerDarts : Embedded.outerDarts diagram = [4, 6, 2] := by
  change ((boundary (face 3)).darts.reverse.map M.alpha) = _
  rw [boundary_face_darts]
  rfl

/-- The merged face set of the two digons. -/
def pinchFaces : Finset diagram.toCombMap.Face :=
  Finset.cons (face 1) {face 2} (by
    rw [Finset.mem_singleton, face_eq_iff]
    decide)

theorem isBoundaryDart_iff (d : Fin 10) :
    Embedded.IsBoundaryDart diagram pinchFaces d ↔ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 := by
  change (M.faceOf d ∈ Finset.cons (face 1) {face 2} _ ∧
    M.faceOf (M.alpha d) ∉ Finset.cons (face 1) {face 2} _) ↔ _
  simp only [Finset.mem_cons, Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

/-- No edge of the merged face set is internal. -/
theorem not_internalBoundaryMove (d e : Fin 10) :
    ¬ Embedded.InternalBoundaryMove diagram pinchFaces d e := by
  rintro ⟨hd, hα, -⟩
  change M.faceOf d ∈ Finset.cons (face 1) {face 2} _ at hd
  change M.faceOf (M.alpha d) ∈ Finset.cons (face 1) {face 2} _ at hα
  simp only [Finset.mem_cons, Finset.mem_singleton, faceOf_eq_face] at hd hα
  revert hd hα
  fin_cases d <;> decide

/-- A boundary step of the merged face set is one turn of `facePerm`. -/
theorem boundaryStep_eq {d e : Fin 10}
    (h : Embedded.BoundaryStep diagram pinchFaces d e) : e = M.facePerm d := by
  obtain ⟨-, -, hrt⟩ := h
  cases hrt with
  | refl => rfl
  | tail _ hmove => exact (not_internalBoundaryMove _ _ hmove).elim

/-- Two turns of `facePerm` return to a boundary dart: each digon has two darts. -/
theorem facePerm_facePerm_of_isBoundaryDart (d : Fin 10)
    (hd : Embedded.IsBoundaryDart diagram pinchFaces d) : M.facePerm (M.facePerm d) = d := by
  rw [isBoundaryDart_iff] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> decide

/-- A duplicate-free chain of boundary steps has at most two darts. -/
theorem length_le_two_of_isChain (l : List diagram.toCombMap.Dart) (hnodup : l.Nodup)
    (hchain : l.IsChain (Embedded.BoundaryStep diagram pinchFaces)) : l.length ≤ 2 := by
  rcases l with _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, rest⟩⟩⟩
  · simp
  · simp
  · simp
  · rw [List.isChain_cons_cons, List.isChain_cons_cons] at hchain
    obtain ⟨h01, h12, -⟩ := hchain
    have e1 := boundaryStep_eq h01
    have e2 := boundaryStep_eq h12
    have h20 : d2 = d0 := by
      rw [e2, e1]
      exact facePerm_facePerm_of_isBoundaryDart d0 h01.1
    subst h20
    exact ((List.nodup_cons.mp hnodup).1 (by simp)).elim

/-- **The merged face set of a pinched pair has no face-set boundary.** -/
theorem no_faceSetBoundary : IsEmpty (Embedded.FaceSetBoundary diagram pinchFaces) := by
  refine ⟨fun B => ?_⟩
  have hsub : ([3, 4, 5, 6] : List diagram.toCombMap.Dart) ⊆ B.cycle := by
    intro d hd
    exact (B.cycle_mem_iff d).mpr ((isBoundaryDart_iff d).mpr (by simpa using hd))
  have hlen : 4 ≤ B.cycle.length :=
    (List.Nodup.subperm (by decide) hsub).length_le
  have hle := length_le_two_of_isChain B.cycle B.cycle_nodup B.cycle_chain
  exact absurd (hlen.trans hle) (by decide)

/-- **No contiguity region on the merged face set.** -/
theorem no_contiguity (D' : RelGenSet G Empty) (eps : ℕ) :
    IsEmpty (Embedded.Contiguity D' eps diagram pinchFaces) :=
  ⟨fun C => no_faceSetBoundary.false C.boundary⟩

#audit_closed_axioms no_faceSetBoundary
#audit_closed_axioms no_contiguity

end GroupApproximation.GGT.VanKampen.OsinPocketPinchedTwoGonModel
