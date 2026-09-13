import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWrapMonogon
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchedTwoGonModel
import GroupApproximation.Meta.AxiomGuard

/-!
# The wrap case of the pinch: a rose with three petals

A model test for the wrap case of `PocketPinchPinchedStatement`
(`Estimating/OsinPocketPinchUnpinched.lean`): the cycle of the pocket face set follows the boundary
and is pinched, and the arc `t_1` is all of `∂Π` or the arc `t_2` is all of `∂X`.

The map is a rose with three petals.  It has six darts, the edges `{0,1}`, `{2,3}` and `{4,5}`,
and one vertex with rotation `0 ↦ 1 ↦ 2 ↦ 3 ↦ 4 ↦ 5 ↦ 0`.  Its faces are a `G`-cell
`κ = [0,2,4]`, the relator cell `Π = [1]` reading `x`, the exterior face `[3]`, and the relator
cell `R = [5]` reading `y`.  The group is `Perm (Fin 3)` and every element is a letter, so the
boundary word is the one letter `x y`.

* `wrapK`: the face set `{κ, R}` is a pocket face set at `ε = 0` between the positions `0` and
  `1`, with source `Π`, kept cell `R`, empty sides, the arc `[1]` of `Π` read backwards and the
  arc `[2]` of the exterior.  Both arcs are whole boundaries (`wrapK_sourceArc_length`,
  `wrapK_targetArc_length`).
* Its cycle `[0,2]` is in walk order (`wrapK_closedWalk`) and follows the boundary
  (`wrapK_followsBoundary`): `0 ↦ 2` is a face step, and `2 ↦ 4 ↦ 5 ↦ 0` crosses the internal
  edge `{4,5}`.  The darts `0` and `2` start at the one vertex (`wrapK_not_unpinched`).
* The relator words and the boundary word have one letter, so no O-equivalent copy has a simple
  pocket face set at `ε = 0` (`PocketWrap.no_simple_of_oEquivalent_monogons`).

So `PocketPinchStatement`, `PocketPinchPinchedStatement`, `PocketPinchLabelledStatement` and
`PocketPinchStepStatement` fail at the universes `0, 0, 0` (`pocketPinchWrapRefutation`).

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 1903,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketWrapRose

open Equiv
open OsinPocketPinchedTwoGonModel (G gx gy D)
open Surgery.MapCollapse (IsBoundaryDart InternalDart BoundaryCycle BoundaryWalk Unpinched)

def roseAlpha : Perm (Fin 6) where
  toFun := ![1, 0, 3, 2, 5, 4]
  invFun := ![1, 0, 3, 2, 5, 4]
  left_inv := by decide
  right_inv := by decide

def roseSigma : Perm (Fin 6) where
  toFun := ![1, 2, 3, 4, 5, 0]
  invFun := ![5, 0, 1, 2, 3, 4]
  left_inv := by decide
  right_inv := by decide

/-- The rose with three petals. -/
def M : CombMap where
  Dart := Fin 6
  dartFintype := inferInstance
  alpha := roseAlpha
  sigma := roseSigma
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 6))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 6) n)

def faceClass : Fin 6 → Fin 4 := ![0, 1, 0, 2, 0, 3]
def faceRep : Fin 4 → Fin 6 := ![0, 1, 3, 5]

noncomputable def faceEquiv : M.Face ≃ Fin 4 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep (by decide) (by decide) (by decide)

def face (i : Fin 4) : M.Face := M.faceOf (faceRep i)

@[simp] theorem faceEquiv_face (i : Fin 4) : faceEquiv (face i) = i := by
  change faceClass (faceRep i) = i
  fin_cases i <;> rfl

theorem faceOf_eq_face (d : Fin 6) (i : Fin 4) :
    M.faceOf d = face i ↔ faceClass d = i := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face]
  rfl

theorem face_eq_iff (i j : Fin 4) : face i = face j ↔ i = j := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face, faceEquiv_face]

noncomputable def vertexEquiv : M.Vertex ≃ Fin 1 :=
  OrbitClassifier.orbitEquiv M.sigma (![0, 0, 0, 0, 0, 0] : Fin 6 → Fin 1)
    (![0] : Fin 1 → Fin 6) (by decide) (by decide) (by decide)

/-- Every dart of the rose starts at its one vertex. -/
theorem vertexOf_eq (d e : M.Dart) : M.vertexOf d = M.vertexOf e :=
  vertexEquiv.injective (Subsingleton.elim _ _)

theorem planar : M.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 6, Relation.EqvGen M.Adjacent 0 d := by
      have h01 : Relation.EqvGen M.Adjacent 0 1 := .rel _ _ (Or.inr rfl)
      have h12 : Relation.EqvGen M.Adjacent 1 2 := .rel _ _ (Or.inr rfl)
      have h23 : Relation.EqvGen M.Adjacent 2 3 := .rel _ _ (Or.inr rfl)
      have h34 : Relation.EqvGen M.Adjacent 3 4 := .rel _ _ (Or.inr rfl)
      have h45 : Relation.EqvGen M.Adjacent 4 5 := .rel _ _ (Or.inr rfl)
      have h02 := Relation.EqvGen.trans _ _ _ h01 h12
      have h03 := Relation.EqvGen.trans _ _ _ h02 h23
      have h04 := Relation.EqvGen.trans _ _ _ h03 h34
      have h05 := Relation.EqvGen.trans _ _ _ h04 h45
      intro d
      fin_cases d
      · exact .refl _
      · exact h01
      · exact h02
      · exact h03
      · exact h04
      · exact h05
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 1 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 4 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 6 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 3 := by omega
    rw [heq]
    norm_num

def faceDarts : Fin 4 → List (Fin 6) := ![[0, 2, 4], [1], [3], [5]]

noncomputable def indexedBoundary (i : Fin 4) : FaceBoundary M (face i) where
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

@[simp] theorem boundary_face_darts (i : Fin 4) :
    (boundary (face i)).darts = faceDarts i := by
  have htransport {f g : M.Face} (h : f = g) (B : FaceBoundary M f) :
      (h ▸ B).darts = B.darts := by cases h; rfl
  unfold boundary
  rw [htransport]
  exact congrArg faceDarts (faceEquiv_face i)

/-- The darts of `κ` read `x⁻¹`, `x y` and `y⁻¹`; `Π` reads `x`, `R` reads `y`, and the exterior
reads `(x y)⁻¹`. -/
def label (d : Fin 6) : RelLetter G Empty :=
  .base ((![gx⁻¹, gx, gx * gy, (gx * gy)⁻¹, gy⁻¹, gy] : Fin 6 → G) d)

def piWord : List (RelLetter G Empty) := [.base gx]
def rWord : List (RelLetter G Empty) := [.base gy]

/-- The relators `x` and `y`. -/
def wrapW : Set (List (RelLetter G Empty)) := {piWord, rWord}

def piCell : RelatorCell M (face 2) wrapW where
  face := face 1
  face_ne_outer := (face_eq_iff 1 2).not.mpr (by decide)
  word := piWord
  word_mem := Set.mem_insert _ _
  conjugator := 1
  reversed := false

def rCell : RelatorCell M (face 2) wrapW where
  face := face 3
  face_ne_outer := (face_eq_iff 3 2).not.mpr (by decide)
  word := rWord
  word_mem := Set.mem_insert_of_mem _ rfl
  conjugator := 1
  reversed := false

/-- **The rose as a disc diagram**, with the relator cells `Π` and `R`. -/
noncomputable def wrapDiagram : DiscDiagram wrapW where
  toCombMap := M
  planar := planar
  label := label
  label_alpha := by
    intro d
    fin_cases d <;> exact congrArg RelLetter.base (by decide)
  outerFace := face 2
  faceBoundary := boundary
  relatorCells := [piCell, rCell]
  relatorCell_faces_nodup := by
    change [face 1, face 3].Nodup
    exact List.nodup_cons.mpr
      ⟨fun h => absurd ((face_eq_iff 1 3).mp (List.mem_singleton.mp h)) (by decide),
        List.nodup_singleton _⟩
  relatorCell_word := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · change piWord = (boundary (face 1)).darts.map label
      rw [boundary_face_darts]
      rfl
    · rcases List.mem_singleton.mp hC with rfl
      change rWord = (boundary (face 3)).darts.map label
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
    · exact (hf rfl).elim
    · exact Or.inl ⟨rCell, List.mem_cons.mpr (Or.inr (List.mem_singleton_self _)), rfl⟩
  boundary_product := by
    rw [boundary_face_darts]
    decide

instance wrapDiagram_neZero : NeZero wrapDiagram.rCellCount := ⟨by decide⟩
instance wrapDiagram_ofNat (n : ℕ) : OfNat wrapDiagram.toCombMap.Dart n :=
  inferInstanceAs (OfNat (Fin 6) n)
instance wrapDiagram_decidableEq : DecidableEq wrapDiagram.toCombMap.Dart :=
  inferInstanceAs (DecidableEq (Fin 6))

theorem wrapDiagram_cellDarts : Embedded.cellDarts wrapDiagram 0 = [1] := by
  change (boundary (face 1)).darts = _
  rw [boundary_face_darts]
  rfl

theorem wrapDiagram_outerDarts : Embedded.outerDarts wrapDiagram = [2] := by
  change ((boundary (face 2)).darts.reverse.map M.alpha) = _
  rw [boundary_face_darts]
  rfl

/-- Both relator words have one letter. -/
theorem wrapDiagram_cellWord_length (i : Fin wrapDiagram.rCellCount) :
    (Embedded.cell wrapDiagram i).word.length = 1 := by
  rcases Set.mem_insert_iff.mp (Embedded.cell wrapDiagram i).word_mem with h | h
  · exact (congrArg List.length h).trans rfl
  · exact (congrArg List.length (Set.mem_singleton_iff.mp h)).trans rfl

/-- The boundary word has one letter. -/
theorem wrapDiagram_boundaryWord_length : wrapDiagram.boundaryWord.length = 1 := by
  rw [← PocketWrap.outerBoundary_darts_length]
  change (boundary (face 2)).darts.length = 1
  rw [boundary_face_darts]
  rfl

/-- The labels of the rose are letters of the symmetrized alphabet. -/
theorem wrapDiagram_letters :
    ∀ d, (symmetricLabelAlphabet D).IsLetter (wrapDiagram.label d) := fun _ =>
  Or.inl (Set.mem_univ _)

theorem wrap_empty_side_norm :
    WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal
      (Embedded.dartWord wrapDiagram ([] : List wrapDiagram.toCombMap.Dart))) ≤ 0 :=
  Nat.le_of_eq (WordMetric.wordNorm_one _)

/-! ## The pocket face set `{κ, R}` -/

/-- The face set `{κ, R}`. -/
def wrapFaces : Finset wrapDiagram.toCombMap.Face :=
  Finset.cons (face 0) {face 3} fun h =>
    absurd ((face_eq_iff 0 3).mp (Finset.mem_singleton.mp h)) (by decide)

theorem face_mem_wrapFaces_iff (i : Fin 4) : face i ∈ wrapFaces ↔ i = 0 ∨ i = 3 :=
  Finset.mem_cons.trans (or_congr (face_eq_iff i 0) (Finset.mem_singleton.trans (face_eq_iff i 3)))

theorem wrapBoundaryDart_iff (d : Fin 6) :
    IsBoundaryDart wrapDiagram.toCombMap wrapFaces d ↔ d ∈ ([0, 2] : List (Fin 6)) := by
  change (M.faceOf d ∈ Finset.cons (face 0) {face 3} _ ∧
    M.faceOf (M.alpha d) ∉ Finset.cons (face 0) {face 3} _) ↔ _
  simp only [Finset.mem_cons, Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

theorem wrapInternalDart_iff (d : Fin 6) :
    InternalDart wrapDiagram.toCombMap wrapFaces d ↔ d ∈ ([4, 5] : List (Fin 6)) := by
  change (M.faceOf d ∈ Finset.cons (face 0) {face 3} _ ∧
    M.faceOf (M.alpha d) ∈ Finset.cons (face 0) {face 3} _) ↔ _
  simp only [Finset.mem_cons, Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

/-- The two boundary darts of `{κ, R}`. -/
def wrapCycle : BoundaryCycle wrapDiagram.toCombMap wrapFaces where
  cycle := ([0, 2] : List (Fin 6))
  cycle_nonempty := List.cons_ne_nil _ _
  cycle_nodup := (by decide : ([0, 2] : List (Fin 6)).Nodup)
  cycle_mem_iff := fun d => (wrapBoundaryDart_iff d).symm

/-- The arc `[1]` of `Π`, all of it. -/
def wrapSourceArc : Embedded.CyclicArc (Embedded.cellDarts wrapDiagram 0) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 1
  length_le := by
    rw [wrapDiagram_cellDarts]
    decide

theorem wrapSourceArc_darts : wrapSourceArc.darts = [1] := by
  change ((Embedded.cellDarts wrapDiagram 0).drop 0 ++
    (Embedded.cellDarts wrapDiagram 0).take 0).take 1 = _
  rw [wrapDiagram_cellDarts]
  rfl

/-- The arc `[2]` of the exterior boundary, all of it. -/
def wrapTargetArc : Embedded.CyclicArc (Embedded.outerDarts wrapDiagram) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 1
  length_le := by
    rw [wrapDiagram_outerDarts]
    decide

theorem wrapTargetArc_darts : wrapTargetArc.darts = [2] := by
  change ((Embedded.outerDarts wrapDiagram).drop 0 ++
    (Embedded.outerDarts wrapDiagram).take 0).take 1 = _
  rw [wrapDiagram_outerDarts]
  rfl

/-- The cycle of `{κ, R}` is the reversed arc `[1]` of `Π` and the arc `[2]` of the exterior, with
empty sides. -/
theorem wrap_decomposition :
    (wrapCycle : BoundaryCycle wrapDiagram.toCombMap wrapFaces).cycle =
      [] ++ Embedded.invDarts wrapDiagram wrapSourceArc.darts ++ [] ++ wrapTargetArc.darts := by
  rw [wrapSourceArc_darts, wrapTargetArc_darts]
  decide

/-- **The pocket face set `{κ, R}`**, with source `Π` and kept cell `R`. -/
noncomputable def wrapK : PocketFaceSet D 0 wrapDiagram 0 1 where
  faces := wrapFaces
  outerFace_not_mem := fun h => absurd ((face_mem_wrapFaces_iff 2).mp h) (by decide)
  source := 0
  source_not_mem := fun h => absurd ((face_mem_wrapFaces_iff 1).mp h) (by decide)
  kept := ⟨1, by decide⟩
  kept_mem := (face_mem_wrapFaces_iff 3).mpr (Or.inr rfl)
  sourceArc := wrapSourceArc
  targetArc := wrapTargetArc
  firstSide := []
  secondSide := []
  boundary := wrapCycle
  decomposition := wrap_decomposition
  firstSide_length_le := Nat.le_refl 0
  secondSide_length_le := Nat.le_refl 0
  firstSide_norm_le := wrap_empty_side_norm
  secondSide_norm_le := wrap_empty_side_norm
  lo_le := Nat.zero_le _
  le_hi := by decide

/-- The cycle `[0,2]` is a closed walk: the rose has one vertex. -/
theorem wrapK_closedWalk : wrapK.ClosedWalk :=
  And.intro (List.isChain_pair.mpr (vertexOf_eq _ _)) (vertexOf_eq _ _)

/-- The face step from `0` is `2`. -/
theorem wrapWalk_zero_two : BoundaryWalk wrapDiagram.toCombMap wrapFaces 0 2 := by
  change Relation.ReflTransGen _ (M.facePerm 0) 2
  exact (show M.facePerm 0 = 2 by decide) ▸ Relation.ReflTransGen.refl

/-- The face step from `2` is `4`, and the internal edge `{4,5}` leads back to `0`. -/
theorem wrapWalk_two_zero : BoundaryWalk wrapDiagram.toCombMap wrapFaces 2 0 := by
  have h4 : InternalDart wrapDiagram.toCombMap wrapFaces 4 :=
    (wrapInternalDart_iff 4).mpr (by decide)
  have h5 : InternalDart wrapDiagram.toCombMap wrapFaces 5 :=
    (wrapInternalDart_iff 5).mpr (by decide)
  change Relation.ReflTransGen _ (M.facePerm 2) 0
  rw [show M.facePerm 2 = 4 by decide]
  exact .head ⟨h4, show M.sigma 4 = 5 by decide⟩
    (.head ⟨h5, show M.sigma 5 = 0 by decide⟩ .refl)

theorem wrapCycle_followsBoundary : wrapCycle.FollowsBoundary :=
  wrapCycle.followsBoundary_of_chain (List.isChain_pair.mpr wrapWalk_zero_two) wrapWalk_two_zero

/-- **The cycle of `{κ, R}` follows the boundary.** -/
theorem wrapK_followsBoundary : wrapK.boundary.FollowsBoundary :=
  wrapCycle_followsBoundary

/-- **The face set `{κ, R}` is pinched**: the darts `0` and `2` start at the one vertex. -/
theorem wrapK_not_unpinched : ¬ Unpinched wrapDiagram.toCombMap wrapK.faces := fun h =>
  absurd (h 0 2 ((wrapBoundaryDart_iff 0).mpr (by decide))
    ((wrapBoundaryDart_iff 2).mpr (by decide)) (vertexOf_eq _ _)) (by decide)

/-- The arc `t_1` is all of `∂Π`. -/
theorem wrapK_sourceArc_length :
    wrapK.sourceArc.length = (Embedded.cellDarts wrapDiagram wrapK.source).length := by
  change 1 = (Embedded.cellDarts wrapDiagram 0).length
  rw [wrapDiagram_cellDarts, List.length_singleton]

/-- The arc `t_2` is all of `∂X`. -/
theorem wrapK_targetArc_length :
    wrapK.targetArc.length = (Embedded.outerDarts wrapDiagram).length := by
  change 1 = (Embedded.outerDarts wrapDiagram).length
  rw [wrapDiagram_outerDarts, List.length_singleton]

/-! ## The endpoints -/

/-- **The wrap case of the pinch at `ε = 0`** (model test).  There is a disc diagram whose labels
are letters, with a pocket face set at `ε = 0` in walk order whose cycle follows the boundary and
is pinched, whose arc `t_1` is all of `∂Π`, and whose arc `t_2` is all of `∂X`.  No O-equivalent
copy of the diagram has a simple pocket face set at `ε = 0`, in any positions. -/
def PocketPinchWrapModel : Prop :=
  ∃ (X : DiscDiagram.{0, 0, 0} wrapW) (K : PocketFaceSet D 0 X 0 1),
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) ∧ K.ClosedWalk ∧
      K.boundary.FollowsBoundary ∧ ¬ Unpinched X.toCombMap K.faces ∧
      K.sourceArc.length = (Embedded.cellDarts X K.source).length ∧
      K.targetArc.length = (Embedded.outerDarts X).length ∧
      ∀ X' : DiscDiagram.{0, 0, 0} wrapW, Nonempty (OEquivalentDiscDiagram X X') →
        ∀ (lo' hi' : ℕ) (K' : PocketFaceSet D 0 X' lo' hi'), ¬ K'.Simple

theorem pocketPinchWrapModel : PocketPinchWrapModel :=
  ⟨wrapDiagram, wrapK, wrapDiagram_letters, wrapK_closedWalk, wrapK_followsBoundary,
    wrapK_not_unpinched, wrapK_sourceArc_length, wrapK_targetArc_length,
    fun _ ⟨e⟩ _ _ K' => PocketWrap.no_simple_of_oEquivalent_monogons e
      wrapDiagram_cellWord_length wrapDiagram_boundaryWord_length K'⟩

/-- **The pinch Props fail at the universes `0, 0, 0`**, witnessed by `wrapK`. -/
def PocketPinchWrapRefutation : Prop :=
  ¬ PocketPinchStatement.{0, 0, 0} ∧ ¬ PocketPinchPinchedStatement.{0, 0, 0} ∧
    ¬ PocketPinchLabelledStatement.{0, 0, 0} ∧ ¬ PocketPinchStepStatement.{0, 0, 0}

theorem pocketPinchWrapRefutation : PocketPinchWrapRefutation :=
  ⟨PocketWrap.not_pocketPinchStatement_of_monogons wrapDiagram_cellWord_length
      wrapDiagram_boundaryWord_length wrapK,
    PocketWrap.not_pocketPinchPinchedStatement_of_monogons wrapDiagram_cellWord_length
      wrapDiagram_boundaryWord_length wrapK,
    PocketWrap.not_pocketPinchLabelledStatement_of_monogons wrapDiagram_cellWord_length
      wrapDiagram_boundaryWord_length wrapDiagram_letters wrapK wrapK_closedWalk,
    PocketWrap.not_pocketPinchStepStatement_of_monogons wrapDiagram_cellWord_length
      wrapDiagram_boundaryWord_length wrapDiagram_letters wrapK wrapK_closedWalk⟩

#audit_axioms wrapDiagram
#audit_axioms wrapK
#audit_closed_axioms wrapK_closedWalk
#audit_axioms wrapK_followsBoundary
#audit_axioms wrapK_not_unpinched
#audit_closed_axioms pocketPinchWrapModel
#audit_closed_axioms pocketPinchWrapRefutation

end GroupApproximation.GGT.VanKampen.OsinPocketWrapRose
