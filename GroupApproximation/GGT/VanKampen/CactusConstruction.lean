import GroupApproximation.GGT.VanKampen.CactusFaceBoundary
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

/-- The positive polygon shape underlying the cactus realization. -/
def cactusShape
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) : CactusShape where
  boundaryLength := Z.boundaryWord.length
  boundary_pos := List.length_pos_iff.mpr Z.boundaryWord_ne_nil
  cellCount := Z.cells.length
  relatorLength i := (Z.cellAt i).relator.length
  relator_pos i := List.length_pos_iff.mpr (Z.cellAt_relator_ne_nil i)

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
    Z.cactusShape.relatorLength i = (Z.cellAt i).relator.length := rfl

/-! ## Ordered polygon boundaries -/

/-- Iterating finite rotation from zero visits the index with the same
natural-number value, before the wrap-around step. -/
theorem finRotate_pow_zero {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n) :
    ((Equiv.finRotate n : Equiv.Perm (Fin n)) ^ k) ⟨0, hn⟩ = ⟨k, hk⟩ := by
  apply Fin.ext
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply,
        Equiv.coe_finRotate_of_ne_last,
        ih (lt_trans (Nat.lt_succ_self k) hk)]
      rw [Ne, Fin.ext_iff,
        ih (lt_trans (Nat.lt_succ_self k) hk), Fin.val_last]
      exact ne_of_lt (Nat.lt_of_succ_lt_succ hk)

/-- A permutation orbit which is an explicitly parametrized finite rotation
has its closed orbit list in that parameter order. -/
theorem closedOrbitList_eq_of_finRotate
    {D : Type*} [Fintype D] [DecidableEq D]
    {n : ℕ} (hn : 0 < n) (p : Equiv.Perm D) (f : Fin n → D)
    (hf : Function.Injective f)
    (hstep : ∀ i, p (f i) = f (Equiv.finRotate n i))
    (hcomplete : ∀ d, p.SameCycle (f ⟨0, hn⟩) d ↔ ∃ i, f i = d) :
    closedOrbitList p (f ⟨0, hn⟩) = List.ofFn f := by
  have hrightNodup : (List.ofFn f).Nodup :=
    List.nodup_ofFn_ofInjective hf
  have hperm : closedOrbitList p (f ⟨0, hn⟩) ~ List.ofFn f := by
    apply (List.perm_ext_iff_of_nodup
      (closedOrbitList.nodup p (f ⟨0, hn⟩)) hrightNodup).mpr
    intro d
    rw [closedOrbitList.mem_iff_sameCycle, hcomplete]
    simp only [List.mem_ofFn]
  have hlength : (closedOrbitList p (f ⟨0, hn⟩)).length = n := by
    rw [hperm.length_eq, List.length_ofFn]
  by_cases hfixed : p (f ⟨0, hn⟩) = f ⟨0, hn⟩
  · have hsingleton : [f ⟨0, hn⟩] ~ List.ofFn f := by
      simpa only [closedOrbitList, if_pos hfixed] using hperm
    have heq : List.ofFn f = [f ⟨0, hn⟩] :=
      List.perm_singleton.mp hsingleton.symm
    simpa only [closedOrbitList, if_pos hfixed] using heq.symm
  · have hpow : ∀ k i, (p ^ k) (f i) =
        f (((Equiv.finRotate n : Equiv.Perm (Fin n)) ^ k) i) := by
      intro k
      induction k with
      | zero => intro i; rfl
      | succ k ih =>
          intro i
          rw [pow_succ, Equiv.Perm.mul_apply, pow_succ,
            Equiv.Perm.mul_apply, hstep, ih]
    apply List.ext_getElem hlength
    intro k hkleft hkright
    rw [closedOrbitList, if_neg hfixed,
      Equiv.Perm.getElem_toList]
    rw [hpow, finRotate_pow_zero hn k hkright]
    simp only [List.getElem_ofFn]

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
  · exact CactusDart.outerForward.inj
  · exact S.facePerm_outerForward
  · exact S.cactus_outer_sameCycle_iff

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
  · exact CactusDart.relatorForward.inj i
  · exact S.facePerm_relatorForward i
  · exact S.cactus_relator_sameCycle_iff i

end Lemma44OrientedRelatorDiagram

end HullSC
end GroupApproximation
