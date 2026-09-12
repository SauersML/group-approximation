import GroupApproximation.GGT.KazhdanHypSymRelators
import GroupApproximation.GGT.KazhdanHypLiteralFilling
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixLeastAreaCut
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Tactic.Group

set_option linter.unusedSectionVars false

/-!
# Literal fillings over the symmetrized triangle family

`KazhdanHypLiteralFillingDegree` shows that disc diagrams over the positive
triangle words cannot fill words of negative degree, which refutes the first
statements of P1 and P2.  The standard convention lets a face read a relator or
its formal inverse, so this file works over `symTriangleRelatorWords T`
(`KazhdanHypSymRelators`).  No cyclic closure is needed: a `DiscDiagram` may
start a face boundary at any dart.

* `reduced_of_least_of_filling`: in any presentation, a relator-covered disc of
  least area is reduced, as long as every factor list for its boundary value is
  realized by a covered disc with at most as many cells.  A cancelling pair of
  stored cells leaves two fewer factors with the same product.
* `SymmetrizedLiteralFilling T` (P1): a signed word that equals a product of `k`
  signed conjugates of the symmetrized relators bounds a relator-covered disc
  with at most `k` cells.
* `SymmetrizedLeastDisc T`: every nonempty null word bounds a relator-covered,
  reduced disc of least area among covered discs with that boundary
  (`symmetrizedLeastDisc_of_symmetrizedLiteralFilling`).

The cellular local data of P2 is typed over the positive family
(`TriangularDiagramLocalData`), so the local-data half of P2 is stated once that
structure carries a face orientation.
-/

namespace GroupApproximation
namespace GGT
namespace KazhdanHypSymmetrizedFilling

open GroupApproximation.KazhdanHyp
open VanKampen
open KazhdanHypCactusDeletionCounting

universe u w v

section Generic

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A least relator-covered disc is reduced**, given realizations of every
factor list of its boundary value by covered discs with the area bound. -/
theorem reduced_of_least_of_filling (Delta : DiscDiagram.{u, w, v} W)
    (hfill : ∀ cells : List G,
      (∀ x ∈ cells, RelatorDefectBudget.IsSignedConjugate (RelLetter.listVal '' W) x) →
      cells.prod = Delta.boundaryValue →
      ∃ Delta' : DiscDiagram.{u, w, v} W, Delta'.boundaryWord = Delta.boundaryWord ∧
        RelatorCellCover Delta' ∧ Delta'.rCellCount ≤ cells.length)
    (hleast : ∀ Delta' : DiscDiagram.{u, w, v} W,
      Delta'.boundaryWord = Delta.boundaryWord → RelatorCellCover Delta' →
        Delta.rCellCount ≤ Delta'.rCellCount) :
    Delta.Reduced := by
  intro pre between suf C₁ C₂ hsplit hcancel
  have hkey : C₁.value * (between.map RelatorCell.value).prod * C₂.value =
      (between.map RelatorCell.value).prod := by
    calc C₁.value * (between.map RelatorCell.value).prod * C₂.value
        = (between.map RelatorCell.value).prod *
            (((between.map RelatorCell.value).prod)⁻¹ * C₁.value *
              (between.map RelatorCell.value).prod * C₂.value) := by group
      _ = (between.map RelatorCell.value).prod := by rw [hcancel, mul_one]
  have hvals : Delta.relatorCells.map RelatorCell.value =
      pre.map RelatorCell.value ++ C₁.value ::
        (between.map RelatorCell.value ++ C₂.value :: suf.map RelatorCell.value) := by
    rw [hsplit]
    simp only [List.map_append, List.map_cons]
  have hshort : ((pre ++ between ++ suf).map RelatorCell.value).prod =
      Delta.boundaryValue := by
    rw [← Delta.relatorValues_prod_eq_boundaryValue, hvals]
    simp only [List.map_append, List.prod_append, List.prod_cons]
    rw [← mul_assoc C₁.value, ← mul_assoc (C₁.value * (between.map RelatorCell.value).prod),
      hkey, mul_assoc]
  have hcells : ∀ x ∈ (pre ++ between ++ suf).map RelatorCell.value,
      RelatorDefectBudget.IsSignedConjugate (RelLetter.listVal '' W) x := by
    intro x hx
    obtain ⟨C, _, rfl⟩ := List.mem_map.mp hx
    exact C.value_isSignedConjugate
  obtain ⟨Delta', hboundary', hcover', hcount'⟩ :=
    hfill ((pre ++ between ++ suf).map RelatorCell.value) hcells hshort
  have hle := hleast Delta' hboundary' hcover'
  have hlen : Delta.rCellCount = pre.length + between.length + suf.length + 2 := by
    rw [DiscDiagram.rCellCount, hsplit]
    simp only [List.length_append, List.length_cons]
    omega
  simp only [List.length_map, List.length_append] at hcount'
  omega

end Generic

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-- The relators of the table are values of symmetrized words. -/
theorem relators_subset_listVal_image
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) :
    ((TriangularHodgeLayer.relators T : Finset (FreeGroup Generator)) :
        Set (FreeGroup Generator)) ⊆
      RelLetter.listVal '' symTriangleRelatorWords.{0} T := by
  rw [KazhdanHypLiteralFilling.relators_eq_listVal_image T]
  exact Set.image_mono (triangleRelatorWords_subset_sym T)

/-- **P1 over the symmetrized family.**  A nonempty signed word that equals, in
the free group, a product of signed conjugates of the symmetrized relators bounds
a relator-covered disc with at most that many relator cells. -/
def SymmetrizedLiteralFilling
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) : Prop :=
  ∀ (word : List (TriangularHodgeLayer.SignedGenerator Generator))
    (cells : List (FreeGroup Generator)),
    word ≠ [] →
    (∀ x ∈ cells, RelatorDefectBudget.IsSignedConjugate
      (RelLetter.listVal '' symTriangleRelatorWords.{0} T) x) →
    cells.prod = PresentedGroupRelatorReplay.word word →
    ∃ Delta : VanKampen.DiscDiagram.{0, 0, 0} (symTriangleRelatorWords.{0} T),
      Delta.boundaryWord = word.map signedFreeRelLetter ∧
      RelatorCellCover Delta ∧ Delta.rCellCount ≤ cells.length

/-- **Least reduced discs over the symmetrized family.**  Every nonempty word
that is trivial in the presented group bounds a relator-covered reduced disc of
least area among covered discs with the same boundary. -/
def SymmetrizedLeastDisc
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) : Prop :=
  ∀ (word : List (TriangularHodgeLayer.SignedGenerator Generator)), word ≠ [] →
    PresentedGroup.mk (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
      (PresentedGroupRelatorReplay.word word) = 1 →
    ∃ Delta : VanKampen.DiscDiagram.{0, 0, 0} (symTriangleRelatorWords.{0} T),
      Delta.boundaryWord = word.map signedFreeRelLetter ∧ RelatorCellCover Delta ∧
      Delta.Reduced ∧
      ∀ Delta' : VanKampen.DiscDiagram.{0, 0, 0} (symTriangleRelatorWords.{0} T),
        Delta'.boundaryWord = Delta.boundaryWord → RelatorCellCover Delta' →
          Delta.rCellCount ≤ Delta'.rCellCount

/-- **P1 gives least reduced discs.**  Choose a covered disc of least area; a
cancelling pair in it would give a smaller realization. -/
theorem symmetrizedLeastDisc_of_symmetrizedLiteralFilling
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    (hfill : SymmetrizedLiteralFilling T) : SymmetrizedLeastDisc T := by
  classical
  intro word hne hnull
  have hmem : PresentedGroupRelatorReplay.word word ∈
      Subgroup.normalClosure (RelLetter.listVal '' symTriangleRelatorWords.{0} T) :=
    Subgroup.normalClosure_mono (relators_subset_listVal_image T)
      (PresentedGroup.mk_eq_one_iff.mp hnull)
  obtain ⟨k, hk⟩ := RelatorDefectBudget.exists_isRelatorProduct hmem
  obtain ⟨cells, _, hprod, hcells⟩ := hk.exists_flatten
  obtain ⟨D₀, hD₀, hcover₀, _⟩ := hfill word cells hne hcells hprod
  have hex : ∃ m : ℕ, ∃ Delta : VanKampen.DiscDiagram.{0, 0, 0} (symTriangleRelatorWords.{0} T),
      Delta.boundaryWord = word.map signedFreeRelLetter ∧ RelatorCellCover Delta ∧
        Delta.rCellCount = m := ⟨_, D₀, hD₀, hcover₀, rfl⟩
  obtain ⟨Delta, hboundary, hcover, hm⟩ := Nat.find_spec hex
  have hleast : ∀ Delta' : VanKampen.DiscDiagram.{0, 0, 0} (symTriangleRelatorWords.{0} T),
      Delta'.boundaryWord = Delta.boundaryWord → RelatorCellCover Delta' →
        Delta.rCellCount ≤ Delta'.rCellCount := by
    intro Delta' hb' hc'
    have hmin : Nat.find hex ≤ Delta'.rCellCount :=
      Nat.find_min' hex ⟨Delta', hb'.trans hboundary, hc', rfl⟩
    omega
  refine ⟨Delta, hboundary, hcover, ?_, hleast⟩
  refine reduced_of_least_of_filling Delta ?_ hleast
  intro cells' hcells' hprod'
  have hprod'' : cells'.prod = PresentedGroupRelatorReplay.word word := by
    rw [hprod', DiscDiagram.boundaryValue, hboundary, listVal_map_signedFreeRelLetter]
  obtain ⟨Delta', hb', hc', hcount'⟩ := hfill word cells' hne hcells' hprod''
  exact ⟨Delta', hb'.trans hboundary.symm, hc', hcount'⟩

end Table

end KazhdanHypSymmetrizedFilling
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.KazhdanHypSymmetrizedFilling.reduced_of_least_of_filling
#audit_axioms GroupApproximation.GGT.KazhdanHypSymmetrizedFilling.relators_subset_listVal_image
#audit_axioms
  GroupApproximation.GGT.KazhdanHypSymmetrizedFilling.symmetrizedLeastDisc_of_symmetrizedLiteralFilling
