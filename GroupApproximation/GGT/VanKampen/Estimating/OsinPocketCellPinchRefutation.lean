import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellPinchModel
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWrapRose
import GroupApproximation.Meta.AxiomGuard

/-!
# The cell pinch fails at `ε = 1`: a rose with four petals

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining the cells `Π_i` and `Π_j`.

`CellPocketWrap.not_simple_of_monogon_cells` (`Estimating/OsinPocketCellPinchModel.lean`) shows that
a cell pocket face set at `ε = 0` on monogon cells is never simple.  The argument needs only the
first cell, and no side bound.  Both arcs are nonempty.  So when the first cell `Π_i` has one dart
`x`, the arc `t_1` is `[x]` and the cycle is `s_1 ++ alpha x :: e :: rest`, where `e` starts
`s_2 t_2`.  The dart `x` is a loop, so `alpha x` starts where `x` starts, and walk order makes that
the start of `e`.  The cycle then passes that vertex twice.

* `CellPocketWrap.not_simple_of_monogon_first`: a cell pocket face set whose first cell has one dart
  is not simple, at every `ε`.
* `CellPocketWrap.no_simple_of_oEquivalent_monogons_pos`: no O-equivalent copy of a diagram on
  one-letter relator words has a simple cell pocket face set, at every `ε`.
* `CellPocketWrap.not_cellPocketPinchPosStatement_of_monogon_cells`: a cell pocket face set in walk
  order, at `0 < ε`, of a diagram on one-letter relator words with letter labels, refutes
  `CellPocketPinchPosStatement`.

The map is a rose with four petals.  It has eight darts, the edges `{0,1}`, `{2,3}`, `{4,5}` and
`{6,7}`, and one vertex with rotation `0 ↦ 1 ↦ ⋯ ↦ 7 ↦ 0`.  Its faces are a `G`-cell
`κ = [0,2,4,6]`, the relator cells `Π_i = [1]`, `Π_j = [3]` and `R = [5]`, and the exterior face
`[7]`.  The group is `Perm (Fin 3)` and every element is a letter.

* `roseK`: the face set `{κ, R}` is a cell pocket face set at `ε = 1` between `Π_i` and `Π_j`, with
  kept cell `R`, first side empty, second side the exterior-facing dart `6`, and both arcs whole
  boundaries.  Its cycle `[0,6,2]` is in walk order (`roseK_closedWalk`): the rose has one vertex.
* `cellPocketPinchRoseRefutation`: `CellPocketPinchPosStatement` fails at the universes `0, 0, 0`.

The section form `CellPocketPinchSectionStatement` (`Estimating/OsinPocketCellPinchSection.lean`)
asks for proper arcs, which no monogon cell has, so this diagram does not touch it.

## Manuscript status

Model test for infrastructure of `thm:hull` (Hull's small cancellation theorem, through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

namespace CellPocketWrap

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {X : DiscDiagram.{u, w, v} W}

/-- **A cell pocket face set whose first cell has one dart is not simple**, at every side bound. -/
theorem not_simple_of_monogon_first {eps : ℕ} {i j : Fin X.rCellCount}
    (K : CellPocketFaceSet D eps X i j) (hi : (cellDarts X i).length = 1) : ¬ K.Simple := by
  intro hK
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hi
  have h1l : K.firstArc.darts.length ≤ 1 :=
    K.firstArc.darts_length.trans_le (K.firstArc.length_le.trans_eq hi)
  have h1m : ∀ d ∈ K.firstArc.darts, d = x := fun d hd => by
    have h := K.firstArc.mem_cycle_of_mem_darts hd
    rw [hx, List.mem_singleton] at h
    exact h
  have ht1 : K.firstArc.darts = [x] := by
    rcases PocketWrap.eq_nil_or_eq_singleton h1l h1m with h | h
    · have hpos := K.firstArc_pos
      rw [← K.firstArc.darts_length, h] at hpos
      exact absurd hpos (by simp)
    · exact h
  have ht2 : K.secondArc.darts ≠ [] := by
    intro h
    have hpos := K.secondArc_pos
    rw [← K.secondArc.darts_length, h] at hpos
    exact absurd hpos (by simp)
  have hne : K.secondSide ++ invDarts X K.secondArc.darts ≠ [] := by
    intro h
    apply ht2
    simpa [invDarts] using (List.append_eq_nil_iff.mp h).2
  obtain ⟨b, rest, hb⟩ := List.exists_cons_of_ne_nil hne
  have hc : K.boundary.cycle = (K.firstSide ++ invDarts X [x]) ++ b :: rest := by
    rw [K.decomposition, ht1,
      List.append_assoc (K.firstSide ++ invDarts X [x]) K.secondSide
        (invDarts X K.secondArc.darts), hb]
  have hc2 : K.boundary.cycle = K.firstSide ++ X.toCombMap.alpha x :: b :: rest := by
    rw [hc]
    simp [invDarts]
  have hS : IsSimpleClosedWalk X.toCombMap K.boundary.cycle := hK
  have hch := hS.chain
  rw [hc2] at hch
  obtain ⟨-, hxb, -⟩ := List.isChain_append_cons_cons.mp hch
  rw [X.toCombMap.alpha_involutive x] at hxb
  have hfx : X.toCombMap.sigma (X.toCombMap.alpha x) = x :=
    PocketWrap.facePerm_eq_self_of_darts_eq (X.faceBoundary (cell X i).face) hx
  have hvx : X.toCombMap.vertexOf (X.toCombMap.alpha x) = X.toCombMap.vertexOf x :=
    (X.toCombMap.vertexOf_sigma (X.toCombMap.alpha x)).symm.trans
      (congrArg X.toCombMap.vertexOf hfx)
  have hnd := hS.vertex_nodup
  rw [hc, List.map_append, List.nodup_append] at hnd
  exact hnd.2.2 _ (List.mem_map_of_mem (by simp [invDarts])) _ (List.mem_map_of_mem (by simp))
    (hvx.trans hxb)

/-- **No O-equivalent copy of a diagram on one-letter relator words has a simple cell pocket face
set**, at every side bound. -/
theorem no_simple_of_oEquivalent_monogons_pos {X' : DiscDiagram.{u, w, v} W}
    (e : OEquivalentDiscDiagram X X') (hcells : ∀ k, (cell X k).word.length = 1) {eps : ℕ}
    {i' j' : Fin X'.rCellCount} (K' : CellPocketFaceSet D eps X' i' j') : ¬ K'.Simple := by
  have h := e.cellWord_eq (e.cellIndex.symm i')
  rw [Equiv.apply_symm_apply] at h
  refine not_simple_of_monogon_first K' ?_
  rw [PocketWrap.cellDarts_length_eq_word_length, h]
  exact hcells _

/-- **The cell pinch fails on one-letter relator words.**  A cell pocket face set in walk order, at
`0 < ε`, of a diagram with letter labels whose relator words have one letter, refutes
`CellPocketPinchPosStatement`. -/
theorem not_cellPocketPinchPosStatement_of_monogon_cells {eps : ℕ} (heps : 0 < eps)
    (hcells : ∀ k, (cell X k).word.length = 1)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) {i j : Fin X.rCellCount}
    (K : CellPocketFaceSet D eps X i j) (hK : K.ClosedWalk) :
    ¬ CellPocketPinchPosStatement.{u, w, v} := by
  intro h
  obtain ⟨X', i', j', K', ⟨e⟩, -, hsimple⟩ := h D eps heps W X i j hlabel K hK
  exact no_simple_of_oEquivalent_monogons_pos e hcells K' hsimple

end CellPocketWrap

namespace OsinPocketCellPinchRose

open Equiv
open OsinPocketPinchedTwoGonModel (G gx gy D)
open Surgery.MapCollapse (IsBoundaryDart BoundaryCycle)

def roseAlpha : Perm (Fin 8) where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6]
  left_inv := by decide
  right_inv := by decide

def roseSigma : Perm (Fin 8) where
  toFun := ![1, 2, 3, 4, 5, 6, 7, 0]
  invFun := ![7, 0, 1, 2, 3, 4, 5, 6]
  left_inv := by decide
  right_inv := by decide

/-- The rose with four petals. -/
def M : CombMap where
  Dart := Fin 8
  dartFintype := inferInstance
  alpha := roseAlpha
  sigma := roseSigma
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 8))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 8) n)

/-- The faces `κ`, `Π_i`, `Π_j`, `R` and the exterior are the classes `0, 1, 2, 3, 4`. -/
def faceClass : Fin 8 → Fin 5 := ![0, 1, 0, 2, 0, 3, 0, 4]
def faceRep : Fin 5 → Fin 8 := ![0, 1, 3, 5, 7]

noncomputable def faceEquiv : M.Face ≃ Fin 5 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep (by decide) (by decide) (by decide)

def face (i : Fin 5) : M.Face := M.faceOf (faceRep i)

@[simp] theorem faceEquiv_face (i : Fin 5) : faceEquiv (face i) = i := by
  change faceClass (faceRep i) = i
  fin_cases i <;> rfl

theorem faceOf_eq_face (d : Fin 8) (i : Fin 5) :
    M.faceOf d = face i ↔ faceClass d = i := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face]
  rfl

theorem face_eq_iff (i j : Fin 5) : face i = face j ↔ i = j := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face, faceEquiv_face]

noncomputable def vertexEquiv : M.Vertex ≃ Fin 1 :=
  OrbitClassifier.orbitEquiv M.sigma (![0, 0, 0, 0, 0, 0, 0, 0] : Fin 8 → Fin 1)
    (![0] : Fin 1 → Fin 8) (by decide) (by decide) (by decide)

/-- Every dart of the rose starts at its one vertex. -/
theorem vertexOf_eq (d e : M.Dart) : M.vertexOf d = M.vertexOf e :=
  vertexEquiv.injective (Subsingleton.elim _ _)

theorem planar : M.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 8, Relation.EqvGen M.Adjacent 0 d := by
      have h01 : Relation.EqvGen M.Adjacent 0 1 := .rel _ _ (Or.inr rfl)
      have h12 : Relation.EqvGen M.Adjacent 1 2 := .rel _ _ (Or.inr rfl)
      have h23 : Relation.EqvGen M.Adjacent 2 3 := .rel _ _ (Or.inr rfl)
      have h34 : Relation.EqvGen M.Adjacent 3 4 := .rel _ _ (Or.inr rfl)
      have h45 : Relation.EqvGen M.Adjacent 4 5 := .rel _ _ (Or.inr rfl)
      have h56 : Relation.EqvGen M.Adjacent 5 6 := .rel _ _ (Or.inr rfl)
      have h67 : Relation.EqvGen M.Adjacent 6 7 := .rel _ _ (Or.inr rfl)
      have h02 := Relation.EqvGen.trans _ _ _ h01 h12
      have h03 := Relation.EqvGen.trans _ _ _ h02 h23
      have h04 := Relation.EqvGen.trans _ _ _ h03 h34
      have h05 := Relation.EqvGen.trans _ _ _ h04 h45
      have h06 := Relation.EqvGen.trans _ _ _ h05 h56
      have h07 := Relation.EqvGen.trans _ _ _ h06 h67
      intro d
      fin_cases d
      · exact .refl _
      · exact h01
      · exact h02
      · exact h03
      · exact h04
      · exact h05
      · exact h06
      · exact h07
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 1 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 5 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 8 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 4 := by omega
    rw [heq]
    norm_num

def faceDarts : Fin 5 → List (Fin 8) := ![[0, 2, 4, 6], [1], [3], [5], [7]]

noncomputable def indexedBoundary (i : Fin 5) : FaceBoundary M (face i) where
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

@[simp] theorem boundary_face_darts (i : Fin 5) :
    (boundary (face i)).darts = faceDarts i := by
  have htransport {f g : M.Face} (h : f = g) (B : FaceBoundary M f) :
      (h ▸ B).darts = B.darts := by cases h; rfl
  unfold boundary
  rw [htransport]
  exact congrArg faceDarts (faceEquiv_face i)

/-- The darts of `κ` read `x⁻¹`, `y⁻¹`, `x⁻¹` and `x y x`; `Π_i` and `R` read `x`, `Π_j` reads
`y`, and the exterior reads `(x y x)⁻¹`. -/
def label (d : Fin 8) : RelLetter G Empty :=
  .base ((![gx⁻¹, gx, gy⁻¹, gy, gx⁻¹, gx, gx * gy * gx, (gx * gy * gx)⁻¹] : Fin 8 → G) d)

def xWord : List (RelLetter G Empty) := [.base gx]
def yWord : List (RelLetter G Empty) := [.base gy]

/-- The relators `x` and `y`. -/
def roseW : Set (List (RelLetter G Empty)) := {xWord, yWord}

def piCell : RelatorCell M (face 4) roseW where
  face := face 1
  face_ne_outer := (face_eq_iff 1 4).not.mpr (by decide)
  word := xWord
  word_mem := Set.mem_insert _ _
  conjugator := 1
  reversed := false

def pjCell : RelatorCell M (face 4) roseW where
  face := face 2
  face_ne_outer := (face_eq_iff 2 4).not.mpr (by decide)
  word := yWord
  word_mem := Set.mem_insert_of_mem _ rfl
  conjugator := 1
  reversed := false

def rCell : RelatorCell M (face 4) roseW where
  face := face 3
  face_ne_outer := (face_eq_iff 3 4).not.mpr (by decide)
  word := xWord
  word_mem := Set.mem_insert _ _
  conjugator := 1
  reversed := false

/-- **The rose as a disc diagram**, with the relator cells `Π_i`, `Π_j` and `R`. -/
noncomputable def roseDiagram : DiscDiagram roseW where
  toCombMap := M
  planar := planar
  label := label
  label_alpha := by
    intro d
    fin_cases d <;> exact congrArg RelLetter.base (by decide)
  outerFace := face 4
  faceBoundary := boundary
  relatorCells := [piCell, pjCell, rCell]
  relatorCell_faces_nodup := by
    change [face 1, face 2, face 3].Nodup
    exact List.Nodup.map (fun a b h => (face_eq_iff a b).mp h)
      (by decide : ([1, 2, 3] : List (Fin 5)).Nodup)
  relatorCell_word := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · change xWord = (boundary (face 1)).darts.map label
      rw [boundary_face_darts]
      rfl
    · rcases List.mem_cons.mp hC with rfl | hC
      · change yWord = (boundary (face 2)).darts.map label
        rw [boundary_face_darts]
        rfl
      · rcases List.mem_singleton.mp hC with rfl
        change xWord = (boundary (face 3)).darts.map label
        rw [boundary_face_darts]
        rfl
  inner_face := by
    intro f hf
    obtain ⟨i, rfl⟩ : ∃ i, face i = f := ⟨faceEquiv f, faceEquiv.left_inv f⟩
    fin_cases i
    · right
      rw [boundary_face_darts]
      decide
    · exact Or.inl ⟨piCell, List.mem_cons.mpr (Or.inl rfl), rfl⟩
    · exact Or.inl ⟨pjCell, List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))), rfl⟩
    · exact Or.inl ⟨rCell, List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
        (Or.inr (List.mem_singleton_self _)))), rfl⟩
    · exact (hf rfl).elim
  boundary_product := by
    rw [boundary_face_darts]
    decide

instance roseDiagram_neZero : NeZero roseDiagram.rCellCount := ⟨by decide⟩
instance roseDiagram_ofNat (n : ℕ) : OfNat roseDiagram.toCombMap.Dart n :=
  inferInstanceAs (OfNat (Fin 8) n)
instance roseDiagram_decidableEq : DecidableEq roseDiagram.toCombMap.Dart :=
  inferInstanceAs (DecidableEq (Fin 8))

theorem roseDiagram_cellDarts_zero : Embedded.cellDarts roseDiagram 0 = [1] := by
  change (boundary (face 1)).darts = _
  rw [boundary_face_darts]
  rfl

theorem roseDiagram_cellDarts_one : Embedded.cellDarts roseDiagram 1 = [3] := by
  change (boundary (face 2)).darts = _
  rw [boundary_face_darts]
  rfl

/-- The relator words have one letter. -/
theorem roseDiagram_cellWord_length (k : Fin roseDiagram.rCellCount) :
    (Embedded.cell roseDiagram k).word.length = 1 := by
  rcases Set.mem_insert_iff.mp (Embedded.cell roseDiagram k).word_mem with h | h
  · exact (congrArg List.length h).trans rfl
  · exact (congrArg List.length (Set.mem_singleton_iff.mp h)).trans rfl

/-- The labels of the rose are letters of the symmetrized alphabet. -/
theorem roseDiagram_letters :
    ∀ d, (symmetricLabelAlphabet D).IsLetter (roseDiagram.label d) := fun _ =>
  Or.inl (Set.mem_univ _)

/-! ## The cell pocket face set `{κ, R}` -/

/-- The face set `{κ, R}`. -/
def roseFaces : Finset roseDiagram.toCombMap.Face :=
  Finset.cons (face 0) {face 3} fun h =>
    absurd ((face_eq_iff 0 3).mp (Finset.mem_singleton.mp h)) (by decide)

theorem face_mem_roseFaces_iff (i : Fin 5) : face i ∈ roseFaces ↔ i = 0 ∨ i = 3 :=
  Finset.mem_cons.trans (or_congr (face_eq_iff i 0) (Finset.mem_singleton.trans (face_eq_iff i 3)))

theorem roseBoundaryDart_iff (d : Fin 8) :
    IsBoundaryDart roseDiagram.toCombMap roseFaces d ↔ d ∈ ([0, 6, 2] : List (Fin 8)) := by
  change (M.faceOf d ∈ Finset.cons (face 0) {face 3} _ ∧
    M.faceOf (M.alpha d) ∉ Finset.cons (face 0) {face 3} _) ↔ _
  simp only [Finset.mem_cons, Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

/-- The three boundary darts of `{κ, R}`: across `Π_i`, across the exterior, across `Π_j`. -/
def roseCycle : BoundaryCycle roseDiagram.toCombMap roseFaces where
  cycle := ([0, 6, 2] : List (Fin 8))
  cycle_nonempty := List.cons_ne_nil _ _
  cycle_nodup := (by decide : ([0, 6, 2] : List (Fin 8)).Nodup)
  cycle_mem_iff := fun d => (roseBoundaryDart_iff d).symm

/-- The arc `[1]` of `Π_i`, all of it. -/
def roseFirstArc : Embedded.CyclicArc (Embedded.cellDarts roseDiagram 0) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 1
  length_le := by
    rw [roseDiagram_cellDarts_zero]
    decide

theorem roseFirstArc_darts : roseFirstArc.darts = [1] := by
  change ((Embedded.cellDarts roseDiagram 0).drop 0 ++
    (Embedded.cellDarts roseDiagram 0).take 0).take 1 = _
  rw [roseDiagram_cellDarts_zero]
  rfl

/-- The arc `[3]` of `Π_j`, all of it. -/
def roseSecondArc : Embedded.CyclicArc (Embedded.cellDarts roseDiagram 1) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 1
  length_le := by
    rw [roseDiagram_cellDarts_one]
    decide

theorem roseSecondArc_darts : roseSecondArc.darts = [3] := by
  change ((Embedded.cellDarts roseDiagram 1).drop 0 ++
    (Embedded.cellDarts roseDiagram 1).take 0).take 1 = _
  rw [roseDiagram_cellDarts_one]
  rfl

/-- The cycle of `{κ, R}` is the reversed arc of `Π_i`, the dart `6`, and the reversed arc of
`Π_j`. -/
theorem rose_decomposition :
    (roseCycle : BoundaryCycle roseDiagram.toCombMap roseFaces).cycle =
      [] ++ Embedded.invDarts roseDiagram roseFirstArc.darts ++ [6] ++
        Embedded.invDarts roseDiagram roseSecondArc.darts := by
  rw [roseFirstArc_darts, roseSecondArc_darts]
  decide

theorem rose_empty_side_norm :
    WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal
      (Embedded.dartWord roseDiagram ([] : List roseDiagram.toCombMap.Dart))) ≤ 1 :=
  (Nat.le_of_eq (WordMetric.wordNorm_one _)).trans (Nat.zero_le _)

theorem rose_side_norm :
    WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal
      (Embedded.dartWord roseDiagram ([6] : List roseDiagram.toCombMap.Dart))) ≤ 1 :=
  WordMetric.wordNorm_le_one_of_mem (Or.inl (Set.mem_univ _))

/-- **The cell pocket face set `{κ, R}`** at `ε = 1`, between `Π_i` and `Π_j`, with kept cell `R`. -/
noncomputable def roseK : CellPocketFaceSet D 1 roseDiagram 0 1 where
  faces := roseFaces
  outerFace_not_mem := fun h => absurd ((face_mem_roseFaces_iff 4).mp h) (by decide)
  first_not_mem := fun h => absurd ((face_mem_roseFaces_iff 1).mp h) (by decide)
  second_not_mem := fun h => absurd ((face_mem_roseFaces_iff 2).mp h) (by decide)
  kept := ⟨2, by decide⟩
  kept_mem := (face_mem_roseFaces_iff 3).mpr (Or.inr rfl)
  firstArc := roseFirstArc
  secondArc := roseSecondArc
  firstSide := []
  secondSide := [6]
  boundary := roseCycle
  decomposition := rose_decomposition
  firstArc_pos := Nat.one_pos
  secondArc_pos := Nat.one_pos
  firstSide_length_le := Nat.zero_le _
  secondSide_length_le := Nat.le_refl 1
  firstSide_norm_le := rose_empty_side_norm
  secondSide_norm_le := rose_side_norm

/-- The cycle `[0,6,2]` is a closed walk: the rose has one vertex. -/
theorem roseK_closedWalk : roseK.ClosedWalk :=
  And.intro
    (List.isChain_cons_cons.mpr ⟨vertexOf_eq _ _, List.isChain_pair.mpr (vertexOf_eq _ _)⟩)
    (vertexOf_eq _ _)

/-- The face set `{κ, R}` is not simple, through the general theorem. -/
theorem roseK_not_simple : ¬ roseK.Simple :=
  CellPocketWrap.not_simple_of_monogon_first roseK
    (by rw [roseDiagram_cellDarts_zero, List.length_singleton])

/-! ## The endpoint -/

/-- **The cell pinch fails at the universes `0, 0, 0`**, witnessed by `roseK` at `ε = 1`. -/
def CellPocketPinchRoseRefutation : Prop :=
  ¬ CellPocketPinchPosStatement.{0, 0, 0}

theorem cellPocketPinchRoseRefutation : CellPocketPinchRoseRefutation :=
  CellPocketWrap.not_cellPocketPinchPosStatement_of_monogon_cells Nat.one_pos
    roseDiagram_cellWord_length roseDiagram_letters roseK roseK_closedWalk

#audit_axioms roseDiagram
#audit_axioms roseK
#audit_closed_axioms roseK_closedWalk
#audit_closed_axioms roseK_not_simple
#audit_closed_axioms cellPocketPinchRoseRefutation

end OsinPocketCellPinchRose

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWrap.not_simple_of_monogon_first
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWrap.no_simple_of_oEquivalent_monogons_pos
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWrap.not_cellPocketPinchPosStatement_of_monogon_cells
