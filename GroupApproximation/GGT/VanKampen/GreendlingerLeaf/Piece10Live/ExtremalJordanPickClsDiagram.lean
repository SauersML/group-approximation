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
