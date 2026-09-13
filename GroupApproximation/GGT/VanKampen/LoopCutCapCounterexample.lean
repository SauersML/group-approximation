import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionInduction
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellArcs
import GroupApproximation.GGT.VanKampen.Estimating.RegionWeightBound
import GroupApproximation.GGT.VanKampen.Estimating.ContiguityGeometry
import GroupApproximation.GGT.VanKampen.GRegionBoundaryValue
import GroupApproximation.GGT.VanKampen.CactusBoundary
import GroupApproximation.GGT.VanKampen.FaceShelling
import GroupApproximation.GGT.VanKampen.Estimating.PieceCore
import GroupApproximation.Meta.AxiomGuard

/-!
# A least-area cap refutes `LoopCutInput` as stated

`LoopCutInput` (`Estimating/OsinAppendixSectionInduction.lean`) asks that every selected region
of a globally distinguished section family whose target is its own source cell encloses an
`OsinLoopCut`: an enclosed least-area diagram with at least one relator cell and fewer relator
cells than `Delta`.  When `Delta` has one relator cell no such cut exists, so the statement says
that no loop is ever selected there.  This file gives a least-area diagram with one relator cell
whose distinguished family is one loop.

The group is `S₃`, and every element is a letter.  The map has ten darts and four faces: the
relator cell `Π = [0,1,2]` reading `y y y` for the transposition `y = (0 1)`, a G-cell digon
`[5,6]` reading `y y`, a G-cell `[3,4,8,7]` reading `γ g γ y` for `γ = (1 2)` and `g = (0 2)`,
and the outer face `[9]` reading `g`.  The cell carries the conjugator `γ`, so its value is
`γ y γ⁻¹ = g`, the boundary value.

* `leastArea`: the boundary value `g⁻¹` is not `1`, so a relator product of it has index at
  least `1`.
* `capFamily`: the digon is a contiguity region from `Π` to `Π` with arcs of length `1`, and the
  family `{cap}` is globally distinguished.  In every O-equivalent diagram a nondegenerate region
  has the cell as its target, because `y⁻ᵏ g⁻¹ ≠ 1` for `k = 1, 2, 3`; its arcs then have total
  length `2`, because `y⁻ᵏ ≠ 1` for `k = 3`; and two such regions need four darts of a cell with
  three.  So every family has weight at most `2`.
* `not_loopCutInput`: `LoopCutInput D λ c 0 W` is false for `λ ≤ 1` and `0 ≤ c`.

The relator family `{y y y}` does not satisfy `OsinCCondition` at `ε = 0`, so this does not
refute a consumer that assumes that condition.  It shows that `RegionCandidate`,
`nondegenerate`, `respects` and `LabelLegal` do not exclude a cap, so `LoopCutInput` as stated is
false; loops have to be excluded at the level of the candidates or derived from the
small-cancellation condition.  Once `RespectsSections` requires `target ≠ some source`,
`capSectionFamily` no longer exists and this file has to be retired.

## Manuscript status

Infrastructure/audit; certifies no printed sentence.
-/

namespace GroupApproximation.GGT.VanKampen.LoopCutCapCounterexample

open Equiv GroupApproximation.HullSC GroupApproximation.WordMetric

/-! ## The map -/

def alpha : Perm (Fin 10) where
  toFun := ![5, 6, 7, 8, 9, 0, 1, 2, 3, 4]
  invFun := ![5, 6, 7, 8, 9, 0, 1, 2, 3, 4]
  left_inv := by decide
  right_inv := by decide

def facePerm : Perm (Fin 10) where
  toFun := ![1, 2, 0, 4, 8, 6, 5, 3, 7, 9]
  invFun := ![2, 0, 1, 7, 3, 6, 5, 8, 4, 9]
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

def faceClass : Fin 10 → Fin 4 := ![0, 0, 0, 2, 2, 1, 1, 2, 2, 3]
def faceRep : Fin 4 → Fin 10 := ![0, 5, 3, 9]

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
  OrbitClassifier.orbitEquiv M.sigma (![0, 1, 0, 0, 2, 1, 0, 0, 2, 2] : Fin 10 → Fin 3)
    (![0, 1, 4] : Fin 3 → Fin 10) (by decide) (by decide) (by decide)

theorem planar : M.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 10, Relation.EqvGen M.Adjacent 0 d := by
      have trans {d e f : M.Dart}
          (hde : Relation.EqvGen M.Adjacent d e)
          (hef : Relation.EqvGen M.Adjacent e f) :
          Relation.EqvGen M.Adjacent d f := .trans _ _ _ hde hef
      have h05 : Relation.EqvGen M.Adjacent 0 5 := .rel _ _ (Or.inl rfl)
      have h51 : Relation.EqvGen M.Adjacent 5 1 := .rel _ _ (Or.inr rfl)
      have h06 : Relation.EqvGen M.Adjacent 0 6 := .rel _ _ (Or.inr rfl)
      have h62 : Relation.EqvGen M.Adjacent 6 2 := .rel _ _ (Or.inr rfl)
      have h23 : Relation.EqvGen M.Adjacent 2 3 := .rel _ _ (Or.inr rfl)
      have h37 : Relation.EqvGen M.Adjacent 3 7 := .rel _ _ (Or.inr rfl)
      have h38 : Relation.EqvGen M.Adjacent 3 8 := .rel _ _ (Or.inl rfl)
      have h84 : Relation.EqvGen M.Adjacent 8 4 := .rel _ _ (Or.inr rfl)
      have h49 : Relation.EqvGen M.Adjacent 4 9 := .rel _ _ (Or.inr rfl)
      have h02 := trans h06 h62
      have h03 := trans h02 h23
      have h08 := trans h03 h38
      have h04 := trans h08 h84
      intro d
      fin_cases d
      · exact .refl _
      · exact trans h05 h51
      · exact h02
      · exact h03
      · exact h04
      · exact h05
      · exact h06
      · exact trans h03 h37
      · exact h08
      · exact trans h04 h49
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

def faceDarts : Fin 4 → List (Fin 10) := ![[0, 1, 2], [5, 6], [3, 4, 8, 7], [9]]

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

/-! ## The diagram -/

abbrev G := Perm (Fin 3)

/-- The transposition `(0 1)`, the letter of the relator. -/
def y : G := Equiv.swap 0 1
/-- The transposition `(1 2)`, the conjugator of the cell. -/
def gam : G := Equiv.swap 1 2
/-- The transposition `(0 2) = γ y γ⁻¹`, the boundary letter. -/
def g : G := Equiv.swap 0 2

def D : RelGenSet G Empty where
  base := Set.univ
  fam := Empty.elim
  symmetricGenerating := by
    rw [Set.univ_union]
    exact ⟨fun _ _ => Set.mem_univ _, Subgroup.closure_univ⟩

/-- Every letter is admissible. -/
theorem letter_admissible (a : RelLetter G Empty) : D.IsLetter a := by
  cases a with
  | base x => exact Set.mem_univ x
  | comp i _ => exact i.elim

/-- `Π` reads `y y y`, the digon `y y`, the G-cell `γ g γ y` and the outer face `g`. -/
def label (d : Fin 10) : RelLetter G Empty :=
  .base ((![y, y, y, gam, g, y, y, y, gam, g] : Fin 10 → G) d)

def relator : List (RelLetter G Empty) := [.base y, .base y, .base y]
def W : Set (List (RelLetter G Empty)) := {relator}

def relatorCell : RelatorCell M (face 3) W where
  face := face 0
  face_ne_outer := (face_eq_iff 0 3).not.mpr (by decide)
  word := relator
  word_mem := rfl
  conjugator := gam
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
      decide
    · right
      rw [boundary_face_darts]
      decide
    · exact (hf rfl).elim
  boundary_product := by
    rw [boundary_face_darts]
    decide

instance : NeZero diagram.rCellCount := ⟨by decide⟩
instance (n : ℕ) : OfNat diagram.toCombMap.Dart n := inferInstanceAs (OfNat (Fin 10) n)
instance : DecidableEq diagram.toCombMap.Dart := inferInstanceAs (DecidableEq (Fin 10))

@[simp] theorem diagram_cellDarts : Embedded.cellDarts diagram 0 = [0, 1, 2] := by
  change (boundary (face 0)).darts = _
  rw [boundary_face_darts]
  rfl

theorem diagram_boundaryWord : diagram.boundaryWord = [RelLetter.base g⁻¹] := by
  change RelWord.revInv ((boundary (face 3)).darts.map label) = _
  rw [boundary_face_darts]
  rfl

theorem boundaryValue_ne_one : diagram.boundaryValue ≠ 1 := by
  change RelLetter.listVal diagram.boundaryWord ≠ 1
  rw [diagram_boundaryWord]
  decide

/-- **The diagram has least area**: its boundary value is not `1`. -/
theorem leastArea : diagram.LeastArea := by
  intro m hm
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · exact absurd hm.eq_one_of_index_zero boundaryValue_ne_one
  · change 1 ≤ m
    omega

/-- The boundary word `g⁻¹` is `(λ, c)`-quasi-geodesic for `λ ≤ 1` and `0 ≤ c`. -/
theorem boundary_quasiGeodesic (lambda c : ℝ) (hlam : lambda ≤ 1) (hc : 0 ≤ c) :
    IsLambdaCQuasiGeodesicWord D lambda c diagram.boundaryWord := by
  rw [diagram_boundaryWord]
  refine ⟨fun a _ => letter_admissible a, fun i j _hij hj => ?_⟩
  have hj1 : j ≤ 1 := hj
  rcases (show j - i = 0 ∨ (i = 0 ∧ j = 1) by omega) with h | ⟨rfl, rfl⟩
  · have hnonneg : (0 : ℝ) ≤ ((wordDist D.alphabet.carrier
        (OsinComponents.vertex 1 [(RelLetter.base g⁻¹ : RelLetter G Empty)] i)
        (OsinComponents.vertex 1 [(RelLetter.base g⁻¹ : RelLetter G Empty)] j) : ℕ) : ℝ) := by
      positivity
    rw [h, Nat.cast_zero, mul_zero]
    linarith
  · have hdist : 1 ≤ wordDist D.alphabet.carrier
        (OsinComponents.vertex 1 [(RelLetter.base g⁻¹ : RelLetter G Empty)] 0)
        (OsinComponents.vertex 1 [(RelLetter.base g⁻¹ : RelLetter G Empty)] 1) := by
      change 1 ≤ wordDist D.alphabet.carrier 1 (1 * g⁻¹)
      rw [wordDist_one_left]
      exact one_le_wordNorm D.alphabet.symmetricGenerating (by decide)
    have hdistReal : (1 : ℝ) ≤ ((wordDist D.alphabet.carrier
        (OsinComponents.vertex 1 [(RelLetter.base g⁻¹ : RelLetter G Empty)] 0)
        (OsinComponents.vertex 1 [(RelLetter.base g⁻¹ : RelLetter G Empty)] 1) : ℕ) : ℝ) := by
      exact_mod_cast hdist
    simp only [Nat.sub_zero, Nat.cast_one, mul_one]
    linarith

/-- One section, the whole boundary word. -/
noncomputable def cuts (lambda c : ℝ) (hlam : lambda ≤ 1) (hc : 0 ≤ c) :
    SectionCuts D lambda c diagram.boundaryWord :=
  SectionCuts.whole (boundary_quasiGeodesic lambda c hlam hc)

/-! ## The cap -/

/-- The digon `[5,6]`, whose two sides lie on `Π`. -/
def faces : Finset diagram.toCombMap.Face := {face 1}

theorem isBoundaryDart_iff (d : Fin 10) :
    Embedded.IsBoundaryDart diagram faces d ↔ d = 5 ∨ d = 6 := by
  change (M.faceOf d ∈ ({face 1} : Finset M.Face) ∧
    M.faceOf (M.alpha d) ∉ ({face 1} : Finset M.Face)) ↔ _
  simp only [Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

theorem step56 : Embedded.BoundaryStep diagram faces 5 6 :=
  ⟨(isBoundaryDart_iff 5).mpr (Or.inl rfl),
    (isBoundaryDart_iff 6).mpr (Or.inr rfl), .refl⟩

theorem step65 : Embedded.BoundaryStep diagram faces 6 5 :=
  ⟨(isBoundaryDart_iff 6).mpr (Or.inr rfl),
    (isBoundaryDart_iff 5).mpr (Or.inl rfl), .refl⟩

noncomputable def capBoundary : Embedded.FaceSetBoundary diagram faces where
  faces_nonempty := Finset.singleton_nonempty _
  all_gCells := by
    intro f hf
    have h : f = face 1 := Finset.mem_singleton.mp hf
    subst f
    refine ⟨(face_eq_iff 1 3).not.mpr (by decide), ?_⟩
    change RelLetter.listVal ((boundary (face 1)).darts.map label) = 1
    rw [boundary_face_darts]
    decide
  cycle := [5, 6]
  cycle_nonempty := List.cons_ne_nil _ _
  cycle_nodup := by decide
  cycle_mem_iff := by
    intro d
    rw [isBoundaryDart_iff]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rfl
  cycle_chain := by
    simpa only [List.isChain_cons_cons, List.isChain_singleton, and_true] using step56
  cycle_closes := step65

def capSourceArc : Embedded.CyclicArc (Embedded.cellDarts diagram 0) where
  start := ⟨0, Nat.zero_lt_succ _⟩
  length := 1
  length_le := by rw [diagram_cellDarts]; decide

def capTargetArc : Embedded.CyclicArc (Embedded.targetDarts diagram (some 0)) where
  start := ⟨1, by
    change 1 < (Embedded.cellDarts diagram 0).length + 1
    rw [diagram_cellDarts]
    decide⟩
  length := 1
  length_le := by
    change 1 ≤ (Embedded.cellDarts diagram 0).length
    rw [diagram_cellDarts]
    decide

/-- The cap: a contiguity region from `Π` to `Π` with arcs `[0]` and `[1]` and empty sides. -/
noncomputable def capRegion : Embedded.ContiguityGeometry D 0 diagram faces where
  boundary := capBoundary
  source := 0
  target := some 0
  sourceArc := capSourceArc
  targetArc := capTargetArc
  rightSide := []
  leftSide := []
  boundary_decomposition := by
    change [5, 6] = capSourceArc.reverseDarts ++ [] ++ capTargetArc.reverseDarts ++ []
    simp only [Embedded.CyclicArc.reverseDarts, Embedded.CyclicArc.darts,
      Embedded.CyclicArc.rotated, capSourceArc, capTargetArc, Embedded.targetDarts,
      diagram_cellDarts]
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

noncomputable def capCandidate : Embedded.RegionCandidate D 0 diagram := ⟨faces, capRegion⟩

/-- The one-region family `{cap}`.  Its only target is a cell, so `respects` is vacuous. -/
noncomputable def capSectionFamily (lambda c : ℝ) (hlam : lambda ≤ 1) (hc : 0 ≤ c) :
    RealizedSectionFamily D lambda c 0 diagram (cuts lambda c hlam hc) where
  diagram := diagram
  equiv := OEquivalentDiscDiagram.refl diagram
  reduced := reduced_of_rCellCount_le_one diagram (by decide)
  family := {capCandidate}
  pairwise := by
    intro a ha b hb hab
    rw [Finset.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  respects := by
    intro a ha hnone
    rw [Finset.mem_singleton] at ha
    subst a
    exact absurd hnone (Option.some_ne_none _)
  nondegenerate := by
    intro a ha
    rw [Finset.mem_singleton] at ha
    subst a
    exact ⟨Nat.one_pos, Nat.one_pos⟩

theorem capSectionFamily_weight (lambda c : ℝ) (hlam : lambda ≤ 1) (hc : 0 ≤ c) :
    (capSectionFamily lambda c hlam hc).weight = 2 := by
  change EstimatingSelection.familyWeight Embedded.RegionCandidate.weight {capCandidate} = 2
  rw [EstimatingSelection.familyWeight, Finset.sum_singleton]
  rfl

/-! ## Every O-equivalent family has weight at most `2` -/

section Other

variable {Y : DiscDiagram.{0, 0, 0} W}

theorem cell_word (i : Fin Y.rCellCount) : (Embedded.cell Y i).word = relator :=
  (Embedded.cell Y i).word_mem

theorem cellDarts_length (i : Fin Y.rCellCount) : (Embedded.cellDarts Y i).length = 3 := by
  rw [Embedded.CellBoundaryPartition.cellDarts_length_eq_word_length, cell_word]
  rfl

theorem relator_eq_replicate : relator = List.replicate 3 (RelLetter.base y) := rfl

/-- An arc of a relator cell, read backwards, is a power of `y⁻¹`. -/
theorem arcWord (i : Fin Y.rCellCount) (arc : Embedded.CyclicArc (Embedded.cellDarts Y i)) :
    Embedded.dartWord Y arc.reverseDarts =
      RelWord.revInv (List.replicate arc.length (RelLetter.base y)) := by
  have hle : arc.length ≤ 3 := by
    have h := arc.length_le
    rwa [cellDarts_length] at h
  change Embedded.dartWord Y (Embedded.invDarts Y arc.darts) = _
  rw [Embedded.CyclicArc.dartWord_invDarts_darts_cellDarts,
    cell_word, relator_eq_replicate, List.rotate_replicate, List.take_replicate,
    Nat.min_eq_left hle]

/-- A nonempty arc of the outer boundary reads `g⁻¹`. -/
theorem targetWord_none (E : OEquivalentDiscDiagram diagram Y)
    (arc : Embedded.CyclicArc (Embedded.targetDarts Y none)) (hpos : 0 < arc.length) :
    Embedded.dartWord Y arc.darts = [RelLetter.base g⁻¹] := by
  have hword : List.map Y.label (Embedded.outerDarts Y) = [RelLetter.base g⁻¹] := by
    have h := Embedded.dartWord_outerDarts Y
    rw [E.boundaryWord_eq, diagram_boundaryWord] at h
    exact h
  have hlen : (Embedded.outerDarts Y).length = 1 := by
    simpa only [List.length_map, List.length_singleton] using congrArg List.length hword
  have harc : arc.length = 1 := by
    have h := arc.length_le
    change arc.length ≤ (Embedded.outerDarts Y).length at h
    omega
  rw [Embedded.CyclicArc.darts, Embedded.CyclicArc.rotated_eq_rotate, harc]
  change List.map Y.label (((Embedded.outerDarts Y).rotate arc.start.1).take 1) = _
  rw [List.map_take, List.map_rotate, hword, List.rotate_singleton]
  rfl

theorem none_value_ne (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    RelLetter.listVal (RelWord.revInv (List.replicate k (RelLetter.base y : RelLetter G Empty)) ++
      [RelLetter.base g⁻¹]) ≠ 1 := by
  interval_cases k <;> decide

theorem some_value_eq (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) (hkl : k + l ≤ 3)
    (h : RelLetter.listVal
      (RelWord.revInv (List.replicate k (RelLetter.base y : RelLetter G Empty)) ++
        RelWord.revInv (List.replicate l (RelLetter.base y : RelLetter G Empty))) = 1) :
    k + l = 2 := by
  have hk2 : k ≤ 2 := by omega
  have hl2 : l ≤ 2 := by omega
  interval_cases k <;> interval_cases l <;> first | rfl | omega | exact absurd h (by decide)

/-- The two arcs of a loop are disjoint sets of darts of a cell with three darts. -/
theorem arcs_le (a : Embedded.RegionCandidate D 0 Y) (j : Fin Y.rCellCount)
    (hsource : a.2.source = j) (htarget : a.2.target = some j) :
    a.2.sourceArc.length + a.2.targetArc.length ≤ 3 := by
  classical
  have h := (Finset.card_le_card (Embedded.RegionCandidate.cellArcDarts_subset a j)).trans
    (List.toFinset_card_le (l := Embedded.cellDarts Y j))
  simp only [Embedded.RegionCandidate.card_cellArcDarts, if_pos hsource, if_pos htarget,
    cellDarts_length] at h
  exact h

/-- **Every nondegenerate region is a loop whose arcs have total length `2`.** -/
theorem region_facts (E : OEquivalentDiscDiagram diagram Y) (a : Embedded.RegionCandidate D 0 Y)
    (hpos : 0 < a.2.sourceArc.length ∧ 0 < a.2.targetArc.length) :
    a.2.target = some a.2.source ∧ a.2.sourceArc.length + a.2.targetArc.length = 2 := by
  have hcount : Y.rCellCount = 1 := E.rCellCount_eq
  have harcs : a.2.target = some a.2.source →
      a.2.sourceArc.length + a.2.targetArc.length ≤ 3 :=
    arcs_le a a.2.source rfl
  revert harcs
  revert hpos
  obtain ⟨_, H⟩ := a
  obtain ⟨boundary, source, target, sourceArc, targetArc, rightSide, leftSide, hdecomp, hright,
    hleft, -, -, ⟨_, hl⟩⟩ := H
  intro hpos harcs
  obtain ⟨hl1, hl2⟩ := hpos
  have hval := Embedded.cycle_value_eq_one_of_shelling boundary hl
  obtain rfl : rightSide = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hright)
  obtain rfl : leftSide = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hleft)
  simp only [List.append_nil] at hdecomp
  have hsource : Embedded.dartWord Y sourceArc.reverseDarts =
      RelWord.revInv (List.replicate sourceArc.length (RelLetter.base y)) :=
    arcWord source sourceArc
  have hle1 : sourceArc.length ≤ 3 := by
    have h := sourceArc.length_le
    rwa [cellDarts_length] at h
  cases target with
  | none =>
    have htarget : Embedded.dartWord Y (Embedded.targetBoundaryDarts Y none targetArc) =
        [RelLetter.base g⁻¹] :=
      targetWord_none E targetArc hl2
    rw [hdecomp, Embedded.dartWord_append, hsource, htarget] at hval
    exact absurd hval (none_value_ne sourceArc.length hl1 hle1)
  | some j =>
    have htarget : Embedded.dartWord Y (Embedded.targetBoundaryDarts Y (some j) targetArc) =
        RelWord.revInv (List.replicate targetArc.length (RelLetter.base y)) :=
      arcWord j targetArc
    rw [hdecomp, Embedded.dartWord_append, hsource, htarget] at hval
    have hj : j = source := Fin.ext (by have hj := j.isLt; have hs := source.isLt; omega)
    have hsum : sourceArc.length + targetArc.length ≤ 3 := harcs (congrArg some hj)
    exact ⟨congrArg some hj,
      some_value_eq sourceArc.length targetArc.length hl1 hl2 hsum hval⟩

/-- **Every realized section family over an O-equivalent diagram has weight at most `2`.** -/
theorem other_weight_le {lambda c : ℝ} {cuts : SectionCuts D lambda c diagram.boundaryWord}
    (other : RealizedSectionFamily D lambda c 0 diagram cuts) : other.weight ≤ 2 := by
  have hcount : other.diagram.rCellCount = 1 := other.equiv.rCellCount_eq
  have h0 : 0 < other.diagram.rCellCount := by omega
  have hfacts : ∀ a ∈ other.family, a.2.target = some a.2.source ∧
      a.2.sourceArc.length + a.2.targetArc.length = 2 :=
    fun a ha => region_facts other.equiv a (other.nondegenerate a ha)
  have hcard : ∀ a ∈ other.family, (a.cellArcDarts ⟨0, h0⟩).card = 2 := by
    intro a ha
    obtain ⟨htarget, hweight⟩ := hfacts a ha
    have hsource : a.2.source = ⟨0, h0⟩ :=
      Fin.ext (by have hs := a.2.source.isLt; change a.2.source.1 = 0; omega)
    simp only [Embedded.RegionCandidate.card_cellArcDarts, if_pos hsource,
      if_pos (htarget.trans (congrArg some hsource))]
    exact hweight
  have hsum := Embedded.RegionCandidate.sum_cellArcDarts_card_le other.family other.pairwise
    ⟨0, h0⟩
  rw [Finset.sum_const_nat hcard, cell_word] at hsum
  change other.family.card * 2 ≤ 3 at hsum
  have hweight : ∀ a ∈ other.family, Embedded.RegionCandidate.weight a = 2 :=
    fun a ha => (hfacts a ha).2
  change EstimatingSelection.familyWeight Embedded.RegionCandidate.weight other.family ≤ 2
  rw [EstimatingSelection.familyWeight, Finset.sum_const_nat hweight]
  omega

end Other

/-- **The one-loop family is globally distinguished.** -/
noncomputable def capFamily (lambda c : ℝ) (hlam : lambda ≤ 1) (hc : 0 ≤ c) :
    GloballyDistinguishedSectionFamily D lambda c 0 diagram (cuts lambda c hlam hc) where
  toRealizedSectionFamily := capSectionFamily lambda c hlam hc
  label_admissible := fun _ => symmetricLabelAlphabet.isLetter D (letter_admissible _)
  weight_maximal := fun other _ =>
    (other_weight_le other).trans (capSectionFamily_weight lambda c hlam hc).ge
  card_minimal := by
    intro other _ hw
    have hw2 : EstimatingSelection.familyWeight Embedded.RegionCandidate.weight
        other.family = 2 :=
      hw.trans (capSectionFamily_weight lambda c hlam hc)
    change ({capCandidate} : Finset (Embedded.RegionCandidate D 0 diagram)).card ≤
      other.family.card
    rw [Finset.card_singleton]
    refine Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr fun hempty => ?_)
    rw [hempty, EstimatingSelection.familyWeight, Finset.sum_empty] at hw2
    exact absurd hw2 (by decide)

/-- **`LoopCutInput` is false** on the least-area one-cell diagram, whose distinguished family
is one loop: a loop cut would enclose a diagram with at least one and fewer than one relator
cell. -/
theorem not_loopCutInput (lambda c : ℝ) (hlam : lambda ≤ 1) (hc : 0 ≤ c) :
    ¬ LoopCutInput.{0, 0, 0} D lambda c 0 W := by
  intro h
  obtain ⟨L⟩ := h diagram (cuts lambda c hlam hc) leastArea (capFamily lambda c hlam hc)
    capCandidate (Finset.mem_singleton_self _) rfl
  have h1 := L.rCellCount_pos
  have h2 : L.enclosed.rCellCount < 1 := L.rCellCount_lt
  omega

/-- **The cap counterexample** as a closed proposition: for `λ ≤ 1` and `0 ≤ c`, `LoopCutInput`
fails over `S₃` with `ε = 0`. -/
def LoopCutCapCounterexampleStatement : Prop :=
  ∀ lambda c : ℝ, lambda ≤ 1 → 0 ≤ c → ¬ LoopCutInput.{0, 0, 0} D lambda c 0 W

theorem loopCutCapCounterexample : LoopCutCapCounterexampleStatement :=
  not_loopCutInput

end GroupApproximation.GGT.VanKampen.LoopCutCapCounterexample

#audit_axioms GroupApproximation.GGT.VanKampen.LoopCutCapCounterexample.not_loopCutInput
#audit_closed_axioms GroupApproximation.GGT.VanKampen.LoopCutCapCounterexample.loopCutCapCounterexample
