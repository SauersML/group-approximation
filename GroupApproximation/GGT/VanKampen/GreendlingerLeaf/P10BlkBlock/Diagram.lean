import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10BlkBlock.Map
import GroupApproximation.Meta.AxiomGuard

/-!
# The diagram and pocket of the counterexample to `roseLobeBlk_BlockStatement`

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-88.

The map `P10BlkBlockModel.M` becomes a disc diagram over `Perm (Fin 3)`.

* The exterior is the face `[1,14]`, reading `c⁻¹ 1`.
* The relator cells are `K₀ = [0,15,4]`, reading `c 1 a`, and `S = [3]`, reading `a`.
  Here `a` is a transposition and `c` a 3-cycle.  They are stored in the order `[K₀, S]`, so
  the product of the cell values is `(c a) a = c`.
* The other four faces `[2,6,10,11]`, `[5,9]`, `[7,12]` and `[8,13]` read `a a a a` or `a a`,
  so they are G-faces.
* The boundary reads `c`.  Both relator values are odd and `c` is even and not `1`.  So the diagram
  has least area (`leastArea`).

The pocket face set `pK` has faces `[0,15,4]`, `[2,6,10,11]` and `[8,13]`, source `S` and kept
cell `K₀`.  Its boundary cycle is `[0,15,2,8,6,4,13]`.
* empty first side;
* empty source arc of `S = [3]`;
* second side the whole cycle, of length `7 = ε` and norm at most `1`;
* empty target arc of the exterior boundary `[15,0]`, at the positions `lo = hi = 0`.

## Manuscript status

Counterexample model for infrastructure of `thm:hull`.  It certifies no printed sentence on its
own.
-/

namespace GroupApproximation.GGT.VanKampen.P10BlkBlockModel

open Equiv GroupApproximation.HullSC
open OsinPocketPinchedTwoGonModel (D)
open OsinPocketFullArcLakeModel (ga gc sign_ga sign_gc sign_of_isRelatorProduct)
open Surgery.MapCollapse (IsBoundaryDart BoundaryCycle)

abbrev G := Perm (Fin 3)

/-- The dart `0` reads `c`, the darts `2, …, 13` read `a`, and the darts `14, 15` read `1`. -/
def label (d : Fin 16) : RelLetter G Empty :=
  .base ((![gc, gc⁻¹, ga, ga, ga, ga, ga, ga, ga, ga, ga, ga, ga, ga, 1, 1] : Fin 16 → G) d)

def W : Set (List (RelLetter G Empty)) :=
  {[.base gc, .base 1, .base ga], [.base ga]}

def cellK0 : RelatorCell M (face 1) W where
  face := face 0
  face_ne_outer := (face_eq_iff 0 1).not.mpr (by decide)
  word := [.base gc, .base 1, .base ga]
  word_mem := Or.inl rfl
  conjugator := 1
  reversed := false

def cellS : RelatorCell M (face 1) W where
  face := face 3
  face_ne_outer := (face_eq_iff 3 1).not.mpr (by decide)
  word := [.base ga]
  word_mem := Or.inr rfl
  conjugator := 1
  reversed := false

/-- **The map as a disc diagram**, with the relator cells `K₀` and `S`. -/
noncomputable def diagram : DiscDiagram W where
  toCombMap := M
  planar := planar
  label := label
  label_alpha := by
    intro d
    fin_cases d <;> exact congrArg RelLetter.base (by decide)
  outerFace := face 1
  faceBoundary := boundary
  relatorCells := [cellK0, cellS]
  relatorCell_faces_nodup := by
    change [face 0, face 3].Nodup
    refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    rw [List.mem_singleton]
    exact (face_eq_iff 0 3).not.mpr (by decide)
  relatorCell_word := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · change [RelLetter.base gc, RelLetter.base (1 : G), RelLetter.base ga] =
        (boundary (face 0)).darts.map label
      rw [boundary_face_darts]
      rfl
    · obtain rfl := List.mem_singleton.mp hC
      change [RelLetter.base ga] = (boundary (face 3)).darts.map label
      rw [boundary_face_darts]
      rfl
  inner_face := by
    intro f hf
    obtain ⟨i, rfl⟩ : ∃ i, face i = f := ⟨faceEquiv f, faceEquiv.left_inv f⟩
    fin_cases i
    · exact Or.inl ⟨cellK0, by simp, rfl⟩
    · exact (hf rfl).elim
    · right
      rw [boundary_face_darts]
      decide
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
  boundary_product := by
    rw [boundary_face_darts]
    decide

instance instNeZeroCells : NeZero diagram.rCellCount := ⟨by decide⟩
instance instOfNatDiagramDart (n : ℕ) : OfNat diagram.toCombMap.Dart n :=
  inferInstanceAs (OfNat (Fin 16) n)
instance instDecEqDiagramDart : DecidableEq diagram.toCombMap.Dart :=
  inferInstanceAs (DecidableEq (Fin 16))

/-- The kept cell `K₀`. -/
def iK0 : Fin diagram.rCellCount := ⟨0, by decide⟩

/-- The source cell `S`. -/
def iS : Fin diagram.rCellCount := ⟨1, by decide⟩

theorem letters : ∀ d, (symmetricLabelAlphabet D).IsLetter (diagram.label d) := fun _ =>
  Or.inl (Set.mem_univ _)

/-! ## Least area -/

theorem relator_signs : ∀ r ∈ RelLetter.listVal '' W, Perm.sign r = -1 := by
  rintro r ⟨word, hword, rfl⟩
  simp only [W, Set.mem_insert_iff, Set.mem_singleton_iff] at hword
  rcases hword with rfl | rfl
  · rw [show RelLetter.listVal ([.base gc, .base 1, .base ga] : List (RelLetter G Empty)) =
        gc * ga by decide, Perm.sign_mul, sign_gc, sign_ga, one_mul]
  · rw [show RelLetter.listVal ([.base ga] : List (RelLetter G Empty)) = ga by decide]
    exact sign_ga

theorem boundaryValue_eq : diagram.boundaryValue = gc := by
  change RelLetter.listVal (RelWord.revInv ((boundary (face 1)).darts.map label)) = gc
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

theorem cellDarts_iS : Embedded.cellDarts diagram iS = [3] := by
  change (boundary (face 3)).darts = _
  rw [boundary_face_darts]
  rfl

theorem outerDarts_eq : Embedded.outerDarts diagram = [15, 0] := by
  change ((boundary (face 1)).darts.reverse.map M.alpha) = _
  rw [boundary_face_darts]
  rfl

/-- The empty arc of `S`. -/
def sArc : Embedded.CyclicArc (Embedded.cellDarts diagram iS) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 0
  length_le := Nat.zero_le _

theorem sArc_darts : sArc.darts = [] := List.take_zero

/-- The empty arc of the exterior boundary `[15,0]`, at the position `0`. -/
def tArc : Embedded.CyclicArc (Embedded.outerDarts diagram) where
  start := ⟨0, Nat.succ_pos _⟩
  length := 0
  length_le := Nat.zero_le _

theorem tArc_darts : tArc.darts = [] := List.take_zero

/-- Membership of the faces `0, …, 6` in the pocket face set. -/
def faceIn : Fin 7 → Bool := ![true, false, true, false, false, false, true]

/-- The faces `[0,15,4]`, `[2,6,10,11]` and `[8,13]`. -/
noncomputable def pFaces : Finset M.Face :=
  ({0, 2, 6} : Finset (Fin 7)).map faceEquiv.symm.toEmbedding

theorem face_mem_iff (i : Fin 7) : face i ∈ pFaces ↔ faceIn i = true := by
  unfold pFaces
  rw [Finset.mem_map_equiv, Equiv.symm_symm, faceEquiv_face]
  revert i
  decide

def cyc : List (Fin 16) := [0, 15, 2, 8, 6, 4, 13]

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

theorem decomp : pCycle.cycle = ([] : List diagram.toCombMap.Dart) ++
    Embedded.invDarts diagram sArc.darts ++ (cyc : List diagram.toCombMap.Dart) ++
      tArc.darts := by
  rw [sArc_darts, tArc_darts]
  decide

theorem side_norm : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal
    (Embedded.dartWord diagram (cyc : List diagram.toCombMap.Dart))) ≤ 7 := by
  have hmem : RelLetter.listVal (Embedded.dartWord diagram (cyc : List diagram.toCombMap.Dart))
      ∈ D.alphabet.carrier := Or.inl (Set.mem_univ _)
  exact (WordMetric.wordNorm_le_one_of_mem hmem).trans (by decide)

theorem empty_norm : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal
    (Embedded.dartWord diagram ([] : List diagram.toCombMap.Dart))) ≤ 7 :=
  (Nat.le_of_eq (WordMetric.wordNorm_one _)).trans (Nat.zero_le 7)

/-- **The pocket face set** at `ε = 7` between the positions `0` and `0`. -/
noncomputable def pK : PocketFaceSet D 7 diagram 0 0 where
  faces := pFaces
  outerFace_not_mem := fun h => absurd ((face_mem_iff 1).mp h) (by decide)
  source := iS
  source_not_mem := fun h => absurd ((face_mem_iff 3).mp h) (by decide)
  kept := iK0
  kept_mem := (face_mem_iff 0).mpr rfl
  sourceArc := sArc
  targetArc := tArc
  firstSide := []
  secondSide := cyc
  boundary := pCycle
  decomposition := decomp
  firstSide_length_le := Nat.zero_le _
  secondSide_length_le := by decide
  firstSide_norm_le := empty_norm
  secondSide_norm_le := side_norm
  lo_le := Nat.zero_le _
  le_hi := by decide

end GroupApproximation.GGT.VanKampen.P10BlkBlockModel

#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.G
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.label
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.W
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.cellK0
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.cellS
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.diagram
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.instNeZeroCells
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.instOfNatDiagramDart
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.instDecEqDiagramDart
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.iK0
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.iS
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.letters
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.relator_signs
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.boundaryValue_eq
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.leastArea
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.cellDarts_iS
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.outerDarts_eq
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.sArc
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.sArc_darts
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.tArc
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.tArc_darts
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.faceIn
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.pFaces
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.face_mem_iff
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.cyc
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.bd_iff
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.pCycle
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.decomp
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.side_norm
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.empty_norm
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.pK
