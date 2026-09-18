import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickClsMap
import GroupApproximation.Meta.AxiomGuard

/-!
# The diagram and pocket of the counterexample to `ExtremalJordanStatement`

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-40.

The map `ExtremalJordanPickClsModel.M` becomes a disc diagram over `Perm (Fin 3)`.

* The exterior is the face `[15,13,11,9]`.
* The relator cells are `S = [7,5,3,14,1]`, reading `1 1 1 c a⁻¹`, and `K₀ = [0]`, reading `a`.
  Here `a` is a transposition and `c` a 3-cycle.
* The other four faces are G-faces reading `1`.
* The boundary reads `c`.  Both relator values are odd and `c` is even and not `1`.  So the diagram
  has least area (`leastArea`).

The pocket face set `pK` has faces `[0]`, `[2,6]`, `[4]`, `[8,12]` and `[10]`, source `S` and kept
cell `K₀`.  Its boundary cycle is `[0,2,4,6,8,10,12]`.
* first side `[0]`;
* source arc `[7,5,3]` of `S`, read backwards as `[2,4,6]`;
* empty second side;
* target arc `[8,10,12]` of the exterior boundary `[8,10,12,14]`.

## Manuscript status

Counterexample model for infrastructure of `thm:hull`.  It certifies no printed sentence on its
own.
-/

namespace GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel

open Equiv GroupApproximation.HullSC
open OsinPocketPinchedTwoGonModel (D)
open OsinPocketFullArcLakeModel (ga gc sign_ga sign_gc sign_of_isRelatorProduct)
open Surgery.MapCollapse (IsBoundaryDart BoundaryCycle)

abbrev G := Perm (Fin 3)

/-- The dart `0` reads `a`, the dart `14` reads `c`, and the darts `2, …, 13` read `1`. -/
def label (d : Fin 16) : RelLetter G Empty :=
  .base ((![ga, ga⁻¹, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, gc, gc⁻¹] : Fin 16 → G) d)

def W : Set (List (RelLetter G Empty)) :=
  {[.base 1, .base 1, .base 1, .base gc, .base ga⁻¹], [.base ga]}

def cellS : RelatorCell M (face 5) W where
  face := face 1
  face_ne_outer := (face_eq_iff 1 5).not.mpr (by decide)
  word := [.base 1, .base 1, .base 1, .base gc, .base ga⁻¹]
  word_mem := Or.inl rfl
  conjugator := 1
  reversed := false

def cellK0 : RelatorCell M (face 5) W where
  face := face 0
  face_ne_outer := (face_eq_iff 0 5).not.mpr (by decide)
  word := [.base ga]
  word_mem := Or.inr rfl
  conjugator := 1
  reversed := false

/-- **The map as a disc diagram**, with the relator cells `S` and `K₀`. -/
noncomputable def diagram : DiscDiagram W where
  toCombMap := M
  planar := planar
  label := label
  label_alpha := by
    intro d
    fin_cases d <;> exact congrArg RelLetter.base (by decide)
  outerFace := face 5
  faceBoundary := boundary
  relatorCells := [cellS, cellK0]
  relatorCell_faces_nodup := by
    change [face 1, face 0].Nodup
    refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    rw [List.mem_singleton]
    exact (face_eq_iff 1 0).not.mpr (by decide)
  relatorCell_word := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · change [RelLetter.base (1 : G), RelLetter.base 1, RelLetter.base 1, RelLetter.base gc,
        RelLetter.base ga⁻¹] = (boundary (face 1)).darts.map label
      rw [boundary_face_darts]
      rfl
    · obtain rfl := List.mem_singleton.mp hC
      change [RelLetter.base ga] = (boundary (face 0)).darts.map label
      rw [boundary_face_darts]
      rfl
  inner_face := by
    intro f hf
    obtain ⟨i, rfl⟩ : ∃ i, face i = f := ⟨faceEquiv f, faceEquiv.left_inv f⟩
    fin_cases i
    · exact Or.inl ⟨cellK0, by simp, rfl⟩
    · exact Or.inl ⟨cellS, by simp, rfl⟩
    · right
      rw [boundary_face_darts]
      decide
    · right
      rw [boundary_face_darts]
      decide
    · right
      rw [boundary_face_darts]
      decide
    · exact (hf rfl).elim
    · right
      rw [boundary_face_darts]
      decide
  boundary_product := by
    rw [boundary_face_darts]
    decide

instance instNeZeroCells : NeZero diagram.rCellCount := ⟨by decide⟩
instance instOfNatDiagramDart (n : ℕ) : OfNat diagram.toCombMap.Dart n :=
  inferInstanceAs (OfNat (Fin 16) n)
instance instDecEqDiagramDart : DecidableEq diagram.toCombMap.Dart :=
  inferInstanceAs (DecidableEq (Fin 16))

/-- The source cell `S`. -/
def iS : Fin diagram.rCellCount := ⟨0, by decide⟩

/-- The kept cell `K₀`. -/
def iK0 : Fin diagram.rCellCount := ⟨1, by decide⟩

theorem letters : ∀ d, (symmetricLabelAlphabet D).IsLetter (diagram.label d) := fun _ =>
  Or.inl (Set.mem_univ _)

/-! ## Least area -/

theorem relator_signs : ∀ r ∈ RelLetter.listVal '' W, Perm.sign r = -1 := by
  rintro r ⟨word, hword, rfl⟩
  simp only [W, Set.mem_insert_iff, Set.mem_singleton_iff] at hword
  rcases hword with rfl | rfl
  · rw [show RelLetter.listVal ([.base 1, .base 1, .base 1, .base gc, .base ga⁻¹] :
        List (RelLetter G Empty)) = gc * ga⁻¹ by decide, Perm.sign_mul, Perm.sign_inv, sign_gc,
      sign_ga, one_mul]
  · rw [show RelLetter.listVal ([.base ga] : List (RelLetter G Empty)) = ga by decide]
    exact sign_ga

theorem boundaryValue_eq : diagram.boundaryValue = gc := by
  change RelLetter.listVal (RelWord.revInv ((boundary (face 5)).darts.map label)) = gc
  rw [boundary_face_darts]
  decide

/-- **The diagram has least area.** -/
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

/-! ## The pocket face set -/

theorem cellDarts_iS : Embedded.cellDarts diagram iS = [7, 5, 3, 14, 1] := by
  change (boundary (face 1)).darts = _
  rw [boundary_face_darts]
  rfl

theorem outerDarts_eq : Embedded.outerDarts diagram = [8, 10, 12, 14] := by
  change ((boundary (face 5)).darts.reverse.map M.alpha) = _
  rw [boundary_face_darts]
  rfl

/-- The arc `[7,5,3]` of `S`. -/
def sArc : Embedded.CyclicArc (Embedded.cellDarts diagram iS) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 3
  length_le := by
    rw [cellDarts_iS]
    decide

theorem sArc_darts : sArc.darts = [7, 5, 3] := by
  change ((Embedded.cellDarts diagram iS).drop 0 ++
    (Embedded.cellDarts diagram iS).take 0).take 3 = _
  rw [cellDarts_iS]
  rfl

/-- The arc `[8,10,12]` of the exterior boundary `[8,10,12,14]`. -/
def tArc : Embedded.CyclicArc (Embedded.outerDarts diagram) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 3
  length_le := by
    rw [outerDarts_eq]
    decide

theorem tArc_darts : tArc.darts = [8, 10, 12] := by
  change ((Embedded.outerDarts diagram).drop 0 ++
    (Embedded.outerDarts diagram).take 0).take 3 = _
  rw [outerDarts_eq]
  rfl

/-- Membership of the faces `0, …, 6` in the pocket face set. -/
def faceIn : Fin 7 → Bool := ![true, false, true, true, true, false, true]

/-- The faces `[0]`, `[2,6]`, `[4]`, `[8,12]` and `[10]`. -/
noncomputable def pFaces : Finset M.Face :=
  ({0, 2, 3, 4, 6} : Finset (Fin 7)).map faceEquiv.symm.toEmbedding

theorem face_mem_iff (i : Fin 7) : face i ∈ pFaces ↔ faceIn i = true := by
  unfold pFaces
  rw [Finset.mem_map_equiv, Equiv.symm_symm, faceEquiv_face]
  revert i
  decide

def cyc : List (Fin 16) := [0, 2, 4, 6, 8, 10, 12]

theorem bd_iff (d : Fin 16) : IsBoundaryDart diagram.toCombMap pFaces d ↔ d ∈ cyc := by
  change M.faceOf d ∈ pFaces ∧ M.faceOf (M.alpha d) ∉ pFaces ↔ _
  rw [faceOf_eq_face', faceOf_eq_face', face_mem_iff, face_mem_iff]
  revert d
  decide

/-- The boundary darts of the pocket face set, in walk order. -/
def pCycle : BoundaryCycle diagram.toCombMap pFaces where
  cycle := cyc
  cycle_nonempty := List.cons_ne_nil _ _
  cycle_nodup := (by decide : cyc.Nodup)
  cycle_mem_iff := fun d => (bd_iff d).symm

theorem decomp : pCycle.cycle = ([0] : List diagram.toCombMap.Dart) ++
    Embedded.invDarts diagram sArc.darts ++ ([] : List diagram.toCombMap.Dart) ++
      tArc.darts := by
  rw [sArc_darts, tArc_darts]
  decide

theorem side_norm : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal
    (Embedded.dartWord diagram ([0] : List diagram.toCombMap.Dart))) ≤ 1 := by
  have hmem : RelLetter.listVal (Embedded.dartWord diagram ([0] : List diagram.toCombMap.Dart))
      ∈ D.alphabet.carrier := Or.inl (Set.mem_univ _)
  exact WordMetric.wordNorm_le_one_of_mem hmem

theorem empty_norm : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal
    (Embedded.dartWord diagram ([] : List diagram.toCombMap.Dart))) ≤ 1 :=
  (Nat.le_of_eq (WordMetric.wordNorm_one _)).trans (Nat.zero_le 1)

/-- **The pocket face set** at `ε = 1` between the positions `0` and `4`. -/
noncomputable def pK : PocketFaceSet D 1 diagram 0 4 where
  faces := pFaces
  outerFace_not_mem := fun h => absurd ((face_mem_iff 5).mp h) (by decide)
  source := iS
  source_not_mem := fun h => absurd ((face_mem_iff 1).mp h) (by decide)
  kept := iK0
  kept_mem := (face_mem_iff 0).mpr rfl
  sourceArc := sArc
  targetArc := tArc
  firstSide := [0]
  secondSide := []
  boundary := pCycle
  decomposition := decomp
  firstSide_length_le := le_refl 1
  secondSide_length_le := Nat.zero_le _
  firstSide_norm_le := side_norm
  secondSide_norm_le := empty_norm
  lo_le := Nat.zero_le _
  le_hi := by decide

theorem pK_target : pK.targetArc.darts = ([8, 10, 12] : List diagram.toCombMap.Dart) :=
  tArc_darts

theorem pK_invSrc :
    Embedded.invDarts diagram pK.sourceArc.darts = ([2, 4, 6] : List diagram.toCombMap.Dart) := by
  change Embedded.invDarts diagram sArc.darts = _
  rw [sArc_darts]
  rfl

end GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel

#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.G
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.label
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.W
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.cellS
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.cellK0
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.diagram
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.instNeZeroCells
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.instOfNatDiagramDart
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.instDecEqDiagramDart
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.iS
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.iK0
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.letters
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.relator_signs
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.boundaryValue_eq
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.leastArea
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.cellDarts_iS
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.outerDarts_eq
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.sArc
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.sArc_darts
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.tArc
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.tArc_darts
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.faceIn
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.pFaces
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.face_mem_iff
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.cyc
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.bd_iff
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.pCycle
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.decomp
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.side_norm
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.empty_norm
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.pK
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.pK_target
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.pK_invSrc
