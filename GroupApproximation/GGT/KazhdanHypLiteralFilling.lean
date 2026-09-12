import GroupApproximation.GGT.KazhdanHypCactusDeletionCounting
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixLeastAreaCut
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Tactic.Group

set_option linter.unusedSectionVars false

/-!
# Literal relator-only fillings and least discs

The torsion and hyperbolicity arguments for a girth-eight triangular
presentation read cells off an actual disc diagram whose every inner face is a
literal triangle.  This file names the two van Kampen outputs they need.

* `LiteralRelatorOnlyFilling T` (P1): every signed word that is a product of
  `k` signed conjugates of the literal relators bounds a relator-only disc with
  at most `k` relator cells.  This is van Kampen's lemma for the ordinary
  presentation, proved by folding: the lollipop wedge of the product is folded
  down to the given boundary word.
* `LeastLiteralDiscLocalData T` (P2): under `GirthEightChecks`, a cyclically
  reduced null word bounds a least relator-only disc carrying the cellular local
  data `TriangularDiagramLocalData`.

The area bound in P1 is what makes reducedness of a least disc a theorem.
`DiscDiagram.Reduced` is the algebraic no-cancelling-pair condition on the
stored ordered cells.  A cancelling pair leaves a factor list with two fewer
factors and the same product, and P1 then produces a smaller relator-only disc
with the same boundary (`reduced_of_least`).  From P1 we obtain the
`PowerDiscCandidate` and the reduced `PowerDisc` consumed by the torsion
extraction (`nonempty_powerDisc_of_literalRelatorOnlyFilling`).
-/

namespace GroupApproximation
namespace GGT
namespace KazhdanHypLiteralFilling

open GroupApproximation.KazhdanHyp
open GirthEightVKInterface
open GirthEightPrimitives2
open VanKampen
open KazhdanHypCactusDeletionCounting

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]
  {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}

/-- **P1: literal relator-only fillings with the area bound.**  A nonempty
signed word that equals, in the free group, a product of signed conjugates of
the literal triangle relators bounds a relator-only disc diagram with at most
that many relator cells. -/
def LiteralRelatorOnlyFilling
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) : Prop :=
  ∀ (word : List (TriangularHodgeLayer.SignedGenerator Generator))
    (cells : List (FreeGroup Generator)),
    word ≠ [] →
    (∀ x ∈ cells, RelatorDefectBudget.IsSignedConjugate
      (GGT.RelLetter.listVal '' triangleRelatorWords.{0} T) x) →
    cells.prod = PresentedGroupRelatorReplay.word word →
    ∃ Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T),
      Delta.boundaryWord = word.map signedFreeRelLetter ∧
      RelatorOnly T Delta ∧ Delta.rCellCount ≤ cells.length

/-- **P2: least literal discs with cellular local data.**  At a table passing
the girth-eight checks, a nonempty cyclically reduced word that is trivial in
the presented group bounds a disc with the cellular local data whose relator
area is least among all relator-only discs with the same boundary.  Cyclic
reducedness is needed because a boundary spur `x x⁻¹` is a boundary vertex of
valence one. -/
def LeastLiteralDiscLocalData
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) : Prop :=
  ∀ (d : ℕ), GirthEightChecks T d →
  ∀ (word : List (TriangularHodgeLayer.SignedGenerator Generator)), word ≠ [] →
    FreeGroup.IsCyclicallyReduced word →
    PresentedGroup.mk (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
      (PresentedGroupRelatorReplay.word word) = 1 →
    ∃ Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T),
      Delta.boundaryWord = word.map signedFreeRelLetter ∧
      Nonempty (TriangularDiagramLocalData T Delta) ∧
      ∀ Delta' : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T),
        Delta'.boundaryWord = Delta.boundaryWord → RelatorOnly T Delta' →
          Delta.rCellCount ≤ Delta'.rCellCount

/-- **Least relator-only discs are reduced.**  A cancelling pair of stored
cells leaves a factor list with two fewer factors and the same product, so P1
gives a relator-only disc with the same boundary and fewer cells. -/
theorem reduced_of_least (hfill : LiteralRelatorOnlyFilling T)
    {word : List (TriangularHodgeLayer.SignedGenerator Generator)}
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (hboundary : Delta.boundaryWord = word.map signedFreeRelLetter)
    (hleast : ∀ Delta' : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T),
      Delta'.boundaryWord = Delta.boundaryWord → RelatorOnly T Delta' →
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
  have hne : word ≠ [] := by
    intro hnil
    have hlen := Delta.boundaryWord_length
    rw [hboundary, hnil, List.map_nil, List.length_nil] at hlen
    have hpos := (Delta.faceBoundary Delta.outerFace).length_eq_degree
    rw [← hlen] at hpos
    exact (Delta.faceBoundary Delta.outerFace).nonempty (List.eq_nil_of_length_eq_zero hpos)
  have hcells : ∀ x ∈ (pre ++ between ++ suf).map RelatorCell.value,
      RelatorDefectBudget.IsSignedConjugate
        (GGT.RelLetter.listVal '' triangleRelatorWords T) x := by
    intro x hx
    obtain ⟨C, _, rfl⟩ := List.mem_map.mp hx
    exact C.value_isSignedConjugate
  have hprod : ((pre ++ between ++ suf).map RelatorCell.value).prod =
      PresentedGroupRelatorReplay.word word := by
    rw [hshort, DiscDiagram.boundaryValue, hboundary, listVal_map_signedFreeRelLetter]
  obtain ⟨Delta', hboundary', hrelatorOnly', hcount'⟩ :=
    hfill word ((pre ++ between ++ suf).map RelatorCell.value) hne hcells hprod
  have hle := hleast Delta' (hboundary'.trans hboundary.symm) hrelatorOnly'
  have hlen : Delta.rCellCount = pre.length + between.length + suf.length + 2 := by
    rw [DiscDiagram.rCellCount, hsplit]
    simp only [List.length_append, List.length_cons]
    omega
  simp only [List.length_map, List.length_append] at hcount'
  omega

/-- The literal relators of the table are the values of its triangle words. -/
theorem relators_eq_listVal_image
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) :
    ((TriangularHodgeLayer.relators T : Finset (FreeGroup Generator)) :
        Set (FreeGroup Generator)) =
      GGT.RelLetter.listVal '' triangleRelatorWords T := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    exact ⟨triangleRelatorWord T j, ⟨j, rfl⟩,
      listVal_map_signedFreeRelLetter (TriangularHodgeLayer.letters (T j))⟩
  · rintro ⟨v, ⟨j, rfl⟩, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, Finset.mem_univ j,
      (listVal_map_signedFreeRelLetter (TriangularHodgeLayer.letters (T j))).symm⟩)

/-- The free-group value of `n` literal copies of a word is its `n`-th power. -/
theorem word_flatten_replicate (word : List (TriangularHodgeLayer.SignedGenerator Generator))
    (m : ℕ) :
    PresentedGroupRelatorReplay.word (List.replicate m word).flatten =
      (PresentedGroupRelatorReplay.word word) ^ m := by
  induction m with
  | zero =>
      simp only [List.replicate_zero, List.flatten_nil, pow_zero,
        PresentedGroupRelatorReplay.word, FreeGroup.one_eq_mk]
  | succ m ih =>
      rw [List.replicate_succ, List.flatten_cons, pow_succ', ← ih]
      exact FreeGroup.mul_mk.symm

/-- **P1 supplies the power-disc candidate.** -/
theorem nonempty_powerDiscCandidate_of_literalRelatorOnlyFilling
    (hfill : LiteralRelatorOnlyFilling T) {g : TriangularHodgeLayer.Presented T} {n : ℕ}
    (hn : 0 < n) (hpow : g ^ n = 1) (hne : g ≠ 1) :
    Nonempty (PowerDiscCandidate T g n) := by
  refine nonempty_powerDiscCandidate_of_literalFilling hn hpow hne ?_
  intro word hword _ _ _
  have hwordne : word ≠ [] := by
    intro hnil
    apply hne
    rw [← hword, hnil, PresentedGroupRelatorReplay.word, ← FreeGroup.one_eq_mk, map_one]
  have hmem : (PresentedGroupRelatorReplay.word word) ^ n ∈
      Subgroup.normalClosure (GGT.RelLetter.listVal '' triangleRelatorWords T) := by
    rw [← relators_eq_listVal_image T, ← PresentedGroup.mk_eq_one_iff, map_pow, hword, hpow]
  obtain ⟨k, hk⟩ := RelatorDefectBudget.exists_isRelatorProduct hmem
  obtain ⟨cells, _, hprod, hcells⟩ := hk.exists_flatten
  have hne' : (List.replicate n word).flatten ≠ [] := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [List.replicate_succ, List.flatten_cons]
    intro h
    exact hwordne (List.append_eq_nil_iff.mp h).1
  obtain ⟨Delta, hboundary, hrelatorOnly, _⟩ :=
    hfill (List.replicate n word).flatten cells hne' hcells
      (hprod.trans (word_flatten_replicate word n).symm)
  refine ⟨Delta, ?_, hrelatorOnly⟩
  rw [hboundary, List.map_flatten, List.map_replicate]

/-- **P1 supplies a reduced power disc.**  A candidate of least relator area
for a fixed representative is reduced by `reduced_of_least`. -/
theorem nonempty_powerDisc_of_literalRelatorOnlyFilling
    (hfill : LiteralRelatorOnlyFilling T) {g : TriangularHodgeLayer.Presented T} {n : ℕ}
    (hn : 0 < n) (hpow : g ^ n = 1) (hne : g ≠ 1) :
    Nonempty (PowerDisc T g n) := by
  classical
  obtain ⟨D₀⟩ := nonempty_powerDiscCandidate_of_literalRelatorOnlyFilling hfill hn hpow hne
  have hex : ∃ m : ℕ, ∃ D : PowerDiscCandidate T g n,
      D.word = D₀.word ∧ D.diagram.rCellCount = m := ⟨_, D₀, rfl, rfl⟩
  obtain ⟨D, hDword, hDm⟩ := Nat.find_spec hex
  refine ⟨D.toPowerDisc (reduced_of_least hfill D.diagram
    (word := (List.replicate n D.word).flatten) ?_ ?_)⟩
  · rw [D.boundary_eq, List.map_flatten, List.map_replicate]
  · intro Delta' hboundary' hrelatorOnly'
    have hmin : Nat.find hex ≤ Delta'.rCellCount := Nat.find_min' hex ⟨{
      word := D₀.word
      represents := D₀.represents
      diagram := Delta'
      boundary_eq := by rw [hboundary', D.boundary_eq, hDword]
      relatorOnly := hrelatorOnly' }, rfl, rfl⟩
    omega

end Table

end KazhdanHypLiteralFilling
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.KazhdanHypLiteralFilling.reduced_of_least
#audit_axioms GroupApproximation.GGT.KazhdanHypLiteralFilling.relators_eq_listVal_image
#audit_axioms GroupApproximation.GGT.KazhdanHypLiteralFilling.word_flatten_replicate
#audit_axioms
  GroupApproximation.GGT.KazhdanHypLiteralFilling.nonempty_powerDiscCandidate_of_literalRelatorOnlyFilling
#audit_axioms
  GroupApproximation.GGT.KazhdanHypLiteralFilling.nonempty_powerDisc_of_literalRelatorOnlyFilling
