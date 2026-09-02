import GroupApproximation.GGT.VanKampen.CactusFaceBoundary
import Mathlib.Data.Fin.Rev
import Mathlib.Data.List.FinRange

/-!
# The labelled cactus realization

For an oriented least-area algebraic diagram, this file builds the explicit
polygon cactus introduced in `CactusMap`.  Least-area reducedness first rules
out an empty relator word in every cell, while the nonidentity exterior value
rules out an empty exterior word.  These facts give the positive polygon
lengths required by `CactusShape`.

The later sections label the two orientations of every polygon edge by
mutually inverse relative letters, label each stem by its algebraic
conjugator, identify the outer and relator face words, and verify that the
complementary face is a `G`-face.  The Euler computation from
`CactusTopology` then supplies planarity.
-/

namespace GroupApproximation
namespace HullSC

universe u w

namespace Lemma44OrientedRelatorDiagram

open GGT.VanKampen

/-- The cell occupying a finite position in the oriented algebraic list. -/
def cellAt
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) : HullSC.Lemma44OrientedRelatorCell W :=
  Z.cells.get i

/-- Splitting the oriented cell list at an index isolates precisely that
cell. -/
theorem cells_eq_take_append_cellAt_drop
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) :
    Z.cells = Z.cells.take i ++ Z.cellAt i :: Z.cells.drop (i + 1) := by
  calc
    Z.cells = Z.cells.take i ++ Z.cells.drop i :=
      (List.take_append_drop i Z.cells).symm
    _ = Z.cells.take i ++ Z.cellAt i :: Z.cells.drop (i + 1) := by
      rw [cellAt, List.cons_get_drop_succ]

/-- Least-area reducedness makes the complete value of every oriented cell
nonidentity. -/
theorem cellAt_value_ne_one
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) : (Z.cellAt i).value ≠ 1 := by
  have hred := Z.reduced
    (Z.cells.take i |>.map HullSC.Lemma44OrientedRelatorCell.value)
    [(Z.cellAt i).value]
    (Z.cells.drop (i + 1) |>.map HullSC.Lemma44OrientedRelatorCell.value)
    (by
      have hmap := congrArg
        (List.map HullSC.Lemma44OrientedRelatorCell.value)
        (Z.cells_eq_take_append_cellAt_drop i)
      calc
        Z.factors = Z.cells.map HullSC.Lemma44OrientedRelatorCell.value :=
          Z.cell_values.symm
        _ = _ := by
          simpa only [List.map_append, List.map_cons,
            List.singleton_append, List.append_assoc] using hmap)
    (by simp)
  simpa using hred

/-- Every relator polygon has positive length.  An empty relator word has
identity value, so its conjugate would contradict reducedness of the
one-cell subproduct. -/
theorem cellAt_relator_ne_nil
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) : (Z.cellAt i).relator ≠ [] := by
  intro hnil
  apply Z.cellAt_value_ne_one i
  rw [HullSC.Lemma44OrientedRelatorCell.value, hnil]
  simp [GGT.RelLetter.listVal_nil]

/-- The exterior polygon has positive length because its stored word spells
a nonidentity group element. -/
theorem boundaryWord_ne_nil
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.boundaryWord ≠ [] := by
  intro hnil
  apply Z.boundary_ne_one
  rw [← Z.boundaryWord_isWord.prod_eq, hnil]
  rfl

/-- Geometric cells are attached in reverse algebraic order.  The
complementary face encounters their inverse values in forward geometric
order, which is the inverse of the complete algebraic product. -/
def geometricCell
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) : HullSC.Lemma44OrientedRelatorCell W :=
  Z.cellAt i.rev

@[simp] theorem geometricCell_rev
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) : Z.geometricCell i.rev = Z.cellAt i := by
  rw [geometricCell, Fin.rev_rev]

/-- The positive polygon shape underlying the cactus realization. -/
def cactusShape
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) : CactusShape where
  boundaryLength := Z.boundaryWord.length
  boundary_pos := List.length_pos_iff.mpr Z.boundaryWord_ne_nil
  cellCount := Z.cells.length
  relatorLength i := (Z.geometricCell i).relator.length
  relator_pos i := List.length_pos_iff.mpr (Z.cellAt_relator_ne_nil i.rev)

@[simp] theorem cactusShape_boundaryLength
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.cactusShape.boundaryLength = Z.boundaryWord.length := rfl

@[simp] theorem cactusShape_cellCount
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.cactusShape.cellCount = Z.cells.length := rfl

@[simp] theorem cactusShape_relatorLength
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) :
    Z.cactusShape.relatorLength i = (Z.geometricCell i).relator.length := rfl

/-! ## Ordered polygon boundaries -/

/-- Iterating finite rotation from zero visits the index with the same
natural-number value, before the wrap-around step. -/
theorem finRotate_pow_zero {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n) :
    ((finRotate n : Equiv.Perm (Fin n)) ^ k) ⟨0, hn⟩ = ⟨k, hk⟩ := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [← Equiv.Perm.iterate_eq_pow,
    ← finCycle_eq_finRotate_iterate (k := (⟨k, hk⟩ : Fin n))]
  exact Fin.zero_add ⟨k, hk⟩

/-- A permutation orbit which is an explicitly parametrized finite rotation
has its closed orbit list in that parameter order. -/
theorem closedOrbitList_eq_of_finRotate
    {D : Type*} [Fintype D] [DecidableEq D]
    {n : ℕ} (hn : 0 < n) (p : Equiv.Perm D) (f : Fin n → D)
    (hf : Function.Injective f)
    (hstep : ∀ i, p (f i) = f (finRotate n i))
    (hcomplete : ∀ d, p.SameCycle (f ⟨0, hn⟩) d ↔ ∃ i, f i = d) :
    closedOrbitList p (f ⟨0, hn⟩) = List.ofFn f := by
  have hrightNodup : (List.ofFn f).Nodup :=
    List.nodup_ofFn_ofInjective hf
  have hperm : List.Perm (closedOrbitList p (f ⟨0, hn⟩))
      (List.ofFn f) := by
    apply (List.perm_ext_iff_of_nodup
      (closedOrbitList.nodup p (f ⟨0, hn⟩)) hrightNodup).mpr
    intro d
    rw [closedOrbitList.mem_iff_sameCycle, hcomplete]
    simp only [List.mem_ofFn]
  have hlength : (closedOrbitList p (f ⟨0, hn⟩)).length = n := by
    rw [hperm.length_eq, List.length_ofFn]
  by_cases hfixed : p (f ⟨0, hn⟩) = f ⟨0, hn⟩
  · have hsingleton : List.Perm [f ⟨0, hn⟩] (List.ofFn f) := by
      simpa only [closedOrbitList, if_pos hfixed] using hperm
    have heq : List.ofFn f = [f ⟨0, hn⟩] :=
      List.perm_singleton.mp hsingleton.symm
    simpa only [closedOrbitList, if_pos hfixed] using heq.symm
  · have hpow : ∀ k i, (p ^ k) (f i) =
        f (((finRotate n : Equiv.Perm (Fin n)) ^ k) i) := by
      intro k
      induction k with
      | zero => intro i; rfl
      | succ k ih =>
          intro i
          rw [pow_succ, Equiv.Perm.mul_apply, pow_succ,
            Equiv.Perm.mul_apply, hstep, ih]
    apply List.ext_getElem (by simpa only [List.length_ofFn] using hlength)
    intro k hkleft hkright
    simp only [closedOrbitList, if_neg hfixed]
    rw [Equiv.Perm.getElem_toList]
    have hk : k < n := by
      simpa only [List.length_ofFn] using hkright
    rw [hpow, finRotate_pow_zero hn k hk]
    simp only [List.getElem_ofFn]

noncomputable local instance cactusShapeDartDecidableEq (S : CactusShape) :
    DecidableEq S.toCombMap.Dart :=
  Classical.decEq _

/-- The outer face orbit is exactly the forward outer darts. -/
theorem cactus_outer_sameCycle_iff (S : CactusShape)
    (d : CactusDart S) :
    S.toCombMap.facePerm.SameCycle
        (.outerForward S.boundaryZero) d ↔
      ∃ j : Fin S.boundaryLength, CactusDart.outerForward j = d := by
  constructor
  · intro hcycle
    have hclass := OrbitClassifier.eq_of_sameCycle S.toCombMap.facePerm
      S.faceClass S.faceClass_facePerm hcycle
    cases d with
    | outerForward j => exact ⟨j, rfl⟩
    | outerBackward j => simp [CactusShape.faceClass] at hclass
    | relatorForward i j => simp [CactusShape.faceClass] at hclass
    | relatorBackward i j => simp [CactusShape.faceClass] at hclass
    | stemOut i => simp [CactusShape.faceClass] at hclass
    | stemIn i => simp [CactusShape.faceClass] at hclass
  · rintro ⟨j, rfl⟩
    exact S.faceRepresentative_sameCycle (.outerForward j)

/-- The outer indexed face boundary is the forward polygon in increasing
finite-index order. -/
theorem cactus_outerBoundary_darts (S : CactusShape) :
    (S.indexedFaceBoundary .outer).darts =
      List.ofFn (CactusDart.outerForward :
        Fin S.boundaryLength → CactusDart S) := by
  change closedOrbitList S.toCombMap.facePerm
      (.outerForward S.boundaryZero) = _
  apply closedOrbitList_eq_of_finRotate S.boundary_pos
  · intro a b h
    exact CactusDart.outerForward.inj h
  · exact S.facePerm_outerForward
  · exact cactus_outer_sameCycle_iff S

/-- A relator face orbit is exactly the forward darts of that relator
polygon. -/
theorem cactus_relator_sameCycle_iff (S : CactusShape)
    (i : Fin S.cellCount) (d : CactusDart S) :
    S.toCombMap.facePerm.SameCycle
        (.relatorForward i (S.relatorZero i)) d ↔
      ∃ j : Fin (S.relatorLength i),
        CactusDart.relatorForward i j = d := by
  constructor
  · intro hcycle
    have hclass := OrbitClassifier.eq_of_sameCycle S.toCombMap.facePerm
      S.faceClass S.faceClass_facePerm hcycle
    cases d with
    | outerForward j => simp [CactusShape.faceClass] at hclass
    | outerBackward j => simp [CactusShape.faceClass] at hclass
    | relatorForward k j =>
        have hki : k = i := by
          simpa [CactusShape.faceClass] using hclass.symm
        subst k
        exact ⟨j, rfl⟩
    | relatorBackward k j => simp [CactusShape.faceClass] at hclass
    | stemOut k => simp [CactusShape.faceClass] at hclass
    | stemIn k => simp [CactusShape.faceClass] at hclass
  · rintro ⟨j, rfl⟩
    exact S.faceRepresentative_sameCycle (.relatorForward i j)

/-- Each relator indexed face boundary is its forward polygon in increasing
finite-index order. -/
theorem cactus_relatorBoundary_darts (S : CactusShape)
    (i : Fin S.cellCount) :
    (S.indexedFaceBoundary (.relator i)).darts =
      List.ofFn (CactusDart.relatorForward i :
        Fin (S.relatorLength i) → CactusDart S) := by
  change closedOrbitList S.toCombMap.facePerm
      (.relatorForward i (S.relatorZero i)) = _
  apply closedOrbitList_eq_of_finRotate (S.relator_pos i)
  · intro a b h
    injection h
  · exact S.facePerm_relatorForward i
  · exact cactus_relator_sameCycle_iff S i

/-! ## Edge labels and polygon words -/

/-- The closed-map traversal of the outer polygon is opposite to the desired
disc boundary orientation. -/
def cactusOuterFaceWord
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    List (GGT.RelLetter G Lambda) :=
  RelWord.revInv
    (Z.boundaryWord.map (GGT.RelLetter.base : G → GGT.RelLetter G Lambda))

/-- The positive outer index transported to the equal length of the formal
reverse-inverse word. -/
def cactusOuterIndex
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (j : Fin Z.cactusShape.boundaryLength) :
    Fin (Z.cactusOuterFaceWord (Lambda := Lambda)).length :=
  Fin.cast (by
    rw [cactusOuterFaceWord, RelWord.length_revInv, List.length_map]
    exact Z.cactusShape_boundaryLength.symm) j

/-- Labels on forward polygon darts are the prescribed words.  Backward
darts receive the inverse letter, and a stem is labelled by the conjugator of
its geometric cell. -/
def cactusLabel
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    CactusDart Z.cactusShape → GGT.RelLetter G Lambda
  | .outerForward j => Z.cactusOuterFaceWord.get (Z.cactusOuterIndex j)
  | .outerBackward j =>
      RelWord.inv (Z.cactusOuterFaceWord.get (Z.cactusOuterIndex j))
  | .relatorForward i j => (Z.geometricCell i).relator.get j
  | .relatorBackward i j => RelWord.inv ((Z.geometricCell i).relator.get j)
  | .stemOut i => GGT.RelLetter.base (Z.geometricCell i).conjugator
  | .stemIn i => GGT.RelLetter.base (Z.geometricCell i).conjugator⁻¹

/-- Edge reversal formally inverts every cactus label. -/
theorem cactusLabel_alpha
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (d : CactusDart Z.cactusShape) :
    Z.cactusLabel (Z.cactusShape.alpha d) = RelWord.inv (Z.cactusLabel d) := by
  cases d with
  | outerForward j => rfl
  | outerBackward j =>
      change Z.cactusOuterFaceWord.get (Z.cactusOuterIndex j) =
        RelWord.inv (RelWord.inv
          (Z.cactusOuterFaceWord.get (Z.cactusOuterIndex j)))
      exact (RelWord.inv_inv_letter _).symm
  | relatorForward i j => rfl
  | relatorBackward i j =>
      change (Z.geometricCell i).relator.get j =
        RelWord.inv (RelWord.inv ((Z.geometricCell i).relator.get j))
      exact (RelWord.inv_inv_letter _).symm
  | stemOut i => rfl
  | stemIn i =>
      change GGT.RelLetter.base (Z.geometricCell i).conjugator =
        RelWord.inv (GGT.RelLetter.base (Z.geometricCell i).conjugator⁻¹)
      rw [RelWord.inv, inv_inv]

/-- Reindexing a list by an equality of lengths and reading all its entries
returns the original list. -/
theorem ofFn_get_cast {X : Type*} (l : List X) {n : ℕ}
    (h : n = l.length) :
    List.ofFn (fun i : Fin n ↦ l.get (Fin.cast h i)) = l := by
  subst n
  exact List.ofFn_get l

/-- The labels on the canonical outer face are its reverse-inverse word. -/
theorem cactus_outerFaceWord
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    (Z.cactusShape.faceBoundary Z.cactusShape.outerFace).darts.map
        Z.cactusLabel = Z.cactusOuterFaceWord := by
  rw [Z.cactusShape.faceBoundary_outerFace_darts,
    cactus_outerBoundary_darts Z.cactusShape, ← List.ofFn_comp']
  exact ofFn_get_cast Z.cactusOuterFaceWord (by
    rw [cactusOuterFaceWord, RelWord.length_revInv, List.length_map]
    exact Z.cactusShape_boundaryLength.symm)

/-- The labels on a geometric relator face are the corresponding geometric
cell word. -/
theorem cactus_relatorFaceWord
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) :
    (Z.cactusShape.faceBoundary (Z.cactusShape.relatorFace i)).darts.map
        Z.cactusLabel = (Z.geometricCell i).relator := by
  rw [Z.cactusShape.faceBoundary_relatorFace_darts,
    cactus_relatorBoundary_darts Z.cactusShape, ← List.ofFn_comp']
  exact List.ofFn_get (Z.geometricCell i).relator

/-- The disc boundary obtained by reverse-inverting the outer face is exactly
the prescribed base-letter word. -/
theorem cactus_boundaryWord
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    RelWord.revInv
        ((Z.cactusShape.faceBoundary Z.cactusShape.outerFace).darts.map
          Z.cactusLabel) =
      Z.boundaryWord.map
        (GGT.RelLetter.base : G → GGT.RelLetter G Lambda) := by
  rw [Z.cactus_outerFaceWord, cactusOuterFaceWord,
    RelWord.revInv_revInv]

/-! ## The ordered relator cells -/

/-- The planar relator cell corresponding to algebraic cell `i`.  Its
geometric polygon has reversed index so complementary-face traversal sees
the inverse factors in reverse algebraic order. -/
def cactusRelatorCell
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) :
    RelatorCell Z.cactusShape.toCombMap Z.cactusShape.outerFace W where
  face := Z.cactusShape.relatorFace i.rev
  face_ne_outer := Z.cactusShape.relatorFace_ne_outerFace i.rev
  word := (Z.cellAt i).relator
  word_mem := (Z.cellAt i).relator_mem
  conjugator := (Z.cellAt i).conjugator
  reversed := false

/-- The relator cells in algebraic order. -/
def cactusRelatorCells
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    List (RelatorCell Z.cactusShape.toCombMap Z.cactusShape.outerFace W) :=
  List.ofFn Z.cactusRelatorCell

/-- Distinct algebraic cells use distinct relator faces. -/
theorem cactusRelatorCell_face_injective
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Function.Injective (fun i : Fin Z.cells.length ↦
      (Z.cactusRelatorCell i).face) := by
  intro i j hij
  have hrev : i.rev = j.rev :=
    Z.cactusShape.relatorFace_injective hij
  exact Fin.rev_injective hrev

/-- The ordered planar relator faces have no repetitions. -/
theorem cactusRelatorCells_faces_nodup
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    (Z.cactusRelatorCells.map RelatorCell.face).Nodup := by
  rw [cactusRelatorCells, ← List.ofFn_comp']
  exact List.nodup_ofFn_ofInjective Z.cactusRelatorCell_face_injective

/-- The stored word of every ordered relator cell is the word read on its
actual planar face. -/
theorem cactusRelatorCells_word
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (C : RelatorCell Z.cactusShape.toCombMap Z.cactusShape.outerFace W)
    (hC : C ∈ Z.cactusRelatorCells) :
    C.word = (Z.cactusShape.faceBoundary C.face).darts.map Z.cactusLabel := by
  rw [cactusRelatorCells, List.mem_ofFn] at hC
  obtain ⟨i, rfl⟩ := hC
  change (Z.cellAt i).relator =
    (Z.cactusShape.faceBoundary
      (Z.cactusShape.relatorFace i.rev)).darts.map Z.cactusLabel
  rw [Z.cactus_relatorFaceWord, Z.geometricCell_rev]

/-- Each planar relator-cell value is the corresponding algebraic oriented
cell value. -/
theorem cactusRelatorCell_value
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) :
    (Z.cactusRelatorCell i).value = (Z.cellAt i).value := by
  simp [cactusRelatorCell, RelatorCell.value,
    HullSC.Lemma44OrientedRelatorCell.value]

/-- The planar relator-cell values are the original algebraic factor list. -/
theorem cactusRelatorCells_values
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.cactusRelatorCells.map RelatorCell.value = Z.factors := by
  rw [cactusRelatorCells, ← List.ofFn_comp']
  have hcells : List.ofFn (fun i : Fin Z.cells.length ↦
      (Z.cellAt i).value) =
      Z.cells.map HullSC.Lemma44OrientedRelatorCell.value := by
    exact List.ofFn_getElem_eq_map Z.cells
      HullSC.Lemma44OrientedRelatorCell.value
  rw [show (fun i : Fin Z.cells.length ↦ (Z.cactusRelatorCell i).value) =
      (fun i : Fin Z.cells.length ↦ (Z.cellAt i).value) by
        funext i
        exact Z.cactusRelatorCell_value i]
  exact hcells.trans Z.cell_values

end Lemma44OrientedRelatorDiagram

end HullSC
end GroupApproximation
