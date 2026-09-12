import GroupApproximation.GGT.KazhdanHypSymLocalData
import GroupApproximation.GGT.KazhdanHypGirthEightHyperbolicityBridge
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Girth-eight hyperbolicity over the symmetrized family

The positive filling input `CyclicallyReducedLocalDataFilling` of
`KazhdanHypGirthEightLinearIsoperimetric` asks for discs over the positive
triangle words, which cannot fill words of negative degree
(`KazhdanHypLiteralFillingDegree`).  This file restates it over
`symTriangleRelatorWords T`, where a face may read a triangle word or its formal
inverse, and repeats the argument.

* `symRelatorCell_value_mem`: a relator cell over the symmetrized family
  contributes a conjugate of a relator or of its inverse.
* `CyclicallyReducedSymLocalDataFilling T`: every nonempty cyclically reduced
  null word bounds a symmetrized disc with `SymTriangularDiagramLocalData`.
* `linearIsoperimetric_of_symLocalDataFilling`:
  `LinearIsoperimetric (symmetrizedRelators T) 3` at a checked table.
* `girthEightHyperbolicity_of_symLocalDataFilling`: the filling input at every
  checked table gives `GirthEightHyperbolicity`, through hull-bridge's Gromov
  theorem (`KazhdanHypGirthEightHyperbolicityBridge`).
-/

namespace GroupApproximation
namespace GGT
namespace KazhdanHypGirthEightSymHyperbolicity

open GroupApproximation.KazhdanHyp
open GroupApproximation.SmallCancellationRouter
open KazhdanHypGirthEightLinearIsoperimetric
open KazhdanHypSymLocalData

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-- **The filling input over the symmetrized family.**  Every nonempty cyclically
reduced word that is trivial in the presented group is the outer word of a disc
diagram over `symTriangleRelatorWords T` carrying triangular local data. -/
def CyclicallyReducedSymLocalDataFilling
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) : Prop :=
  ∀ word : List (TriangularHodgeLayer.SignedGenerator Generator),
    word ≠ [] → FreeGroup.IsCyclicallyReduced word →
    PresentedGroup.mk (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
        (PresentedGroupRelatorReplay.word word) = 1 →
    ∃ Δ : VanKampen.DiscDiagram.{0, 0, 0} (symTriangleRelatorWords.{0} T),
      Δ.boundaryWord = word.map signedFreeRelLetter ∧
        Nonempty (SymTriangularDiagramLocalData T Δ)

section Fixed

variable {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}

/-- The symmetrized relators are closed under inversion. -/
theorem inv_mem_symmetrizedRelators {s : FreeGroup Generator}
    (hs : s ∈ symmetrizedRelators T) : s⁻¹ ∈ symmetrizedRelators T := by
  rcases hs with hs | ⟨r, hr, rfl⟩
  · exact Or.inr ⟨s, hs, rfl⟩
  · rw [inv_inv]
    exact Or.inl hr

/-- A symmetrized word spells a relator or the inverse of one. -/
theorem listVal_mem_symmetrizedRelators
    {v : List (GGT.RelLetter (FreeGroup Generator) PEmpty.{1})}
    (hv : v ∈ symTriangleRelatorWords.{0} T) :
    GGT.RelLetter.listVal v ∈ symmetrizedRelators T := by
  rcases hv with ⟨j, rfl⟩ | ⟨w, ⟨j, rfl⟩, rfl⟩
  · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨j, Finset.mem_univ _, (listVal_triangleRelatorWord T j).symm⟩))
  · rw [HullSC.RelWord.listVal_revInv, listVal_triangleRelatorWord]
    exact Or.inr ⟨TriangularHodgeLayer.relator (T j),
      Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩), rfl⟩

/-- A relator cell over the symmetrized family contributes a conjugate of a
relator or of its inverse. -/
theorem symRelatorCell_value_mem {M : VanKampen.CombMap} {outer : M.Face}
    (C : VanKampen.RelatorCell M outer (symTriangleRelatorWords.{0} T)) :
    ∃ c s : FreeGroup Generator,
      s ∈ symmetrizedRelators T ∧ C.value = c * s * c⁻¹ := by
  have hval := listVal_mem_symmetrizedRelators C.word_mem
  cases hrev : C.reversed
  · exact ⟨C.conjugator, _, hval, by simp [VanKampen.RelatorCell.value, hrev]⟩
  · exact ⟨C.conjugator, _, inv_mem_symmetrizedRelators hval,
      by simp [VanKampen.RelatorCell.value, hrev]⟩

/-- **Linear isoperimetric inequality, constant three, over the symmetrized
family.** -/
theorem linearIsoperimetric_of_symLocalDataFilling {d : ℕ}
    (hchecks : GirthEightChecks T d)
    (hfill : CyclicallyReducedSymLocalDataFilling T) :
    LinearIsoperimetric (symmetrizedRelators T) 3 := by
  intro g hg
  rw [normalClosure_symmetrizedRelators] at hg
  obtain ⟨c, w, hg_eq, hcyc, hwlen⟩ := exists_cyclicallyReduced_conj g
  have hwmem : FreeGroup.mk w ∈ Subgroup.normalClosure
      (TriangularHodgeLayer.relators T : Set (FreeGroup Generator)) := by
    have hrewrite : FreeGroup.mk w = c⁻¹ * g * c⁻¹⁻¹ := by
      rw [hg_eq]
      group
    rw [hrewrite]
    exact (Subgroup.normalClosure_normal).conj_mem g hg c⁻¹
  by_cases hw : w = []
  · refine ⟨0, Nat.zero_le _, ?_⟩
    show g = 1
    rw [hg_eq, hw, ← FreeGroup.one_eq_mk, mul_one, mul_inv_cancel]
  · have htriv : PresentedGroup.mk
        (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
        (PresentedGroupRelatorReplay.word w) = 1 :=
      PresentedGroup.mk_eq_one_iff.mpr hwmem
    obtain ⟨Δ, hbd, ⟨Lloc⟩⟩ := hfill w hw hcyc htriv
    have hcells : Δ.rCellCount ≤ 3 * Δ.boundaryWord.length :=
      Lloc.rCellCount_le_three_mul_boundaryWord_length hchecks
    have hbdlen : Δ.boundaryWord.length = w.length := by
      rw [hbd, List.length_map]
    have hval : Δ.boundaryValue = FreeGroup.mk w := by
      show GGT.RelLetter.listVal Δ.boundaryWord = FreeGroup.mk w
      rw [hbd]
      exact listVal_map_signedFreeRelLetter w
    refine ⟨Δ.rCellCount, by omega, ?_⟩
    rw [hg_eq]
    apply isConjugateProduct_conj
    have hprod := Δ.relatorValues_prod_eq_boundaryValue
    rw [hval] at hprod
    rw [← hprod]
    have hlen : Δ.rCellCount = (Δ.relatorCells.map VanKampen.RelatorCell.value).length := by
      rw [List.length_map]
      rfl
    rw [hlen]
    apply isConjugateProduct_of_forall
    intro x hx
    obtain ⟨C, _, rfl⟩ := List.mem_map.mp hx
    exact symRelatorCell_value_mem C

end Fixed

end Table

/-- **`GirthEightHyperbolicity` from symmetrized fillings.**  The inequality is
proved for the symmetrized relators, Gromov's theorem makes their presented group
hyperbolic, and adjoining inverses leaves the presented group unchanged. -/
theorem girthEightHyperbolicity_of_symLocalDataFilling
    (hfill : ∀ (Generator TriangleIndex : Type) (_ : Fintype Generator)
      (_ : DecidableEq Generator) (_ : Fintype TriangleIndex)
      (_ : DecidableEq TriangleIndex)
      (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (d : ℕ),
      GirthEightChecks T d → CyclicallyReducedSymLocalDataFilling T) :
    GirthEightHyperbolicity := by
  intro Generator TriangleIndex fg dg _ng ft dt T d hchecks
  have hiso := linearIsoperimetric_of_symLocalDataFilling hchecks
    (hfill Generator TriangleIndex fg dg ft dt T d hchecks)
  have hH : Hyperbolic.IsHyperbolicGroup
      (FreeGroup Generator ⧸ Subgroup.normalClosure (symmetrizedRelators T)) :=
    KazhdanHypGirthEightHyperbolicityBridge.linearIsoperimetricHyperbolicityStatement
      Generator (symmetrizedRelators T) ⟨3, norm_le_three_of_mem_symmetrizedRelators⟩ 3 hiso
  show Hyperbolic.IsHyperbolicGroup (FreeGroup Generator ⧸ Subgroup.normalClosure
    (TriangularHodgeLayer.relators T : Set (FreeGroup Generator)))
  exact Hyperbolic.IsHyperbolicGroup.of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (normalClosure_symmetrizedRelators T)) hH

end KazhdanHypGirthEightSymHyperbolicity
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.KazhdanHypGirthEightSymHyperbolicity.symRelatorCell_value_mem
#audit_axioms GroupApproximation.GGT.KazhdanHypGirthEightSymHyperbolicity.linearIsoperimetric_of_symLocalDataFilling
#audit_axioms GroupApproximation.GGT.KazhdanHypGirthEightSymHyperbolicity.girthEightHyperbolicity_of_symLocalDataFilling
