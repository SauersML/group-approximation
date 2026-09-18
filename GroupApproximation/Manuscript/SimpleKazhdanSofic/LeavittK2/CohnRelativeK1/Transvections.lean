import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.Corner
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Algebra.FinitaryLinearBinarySimple
import GroupApproximation.Meta.AxiomGuard

/-!
# `GL_{ι × S}(F_2)` lands in the relative elementary subgroup

Lane `sk-leavitt-19`, third module.

The corner monoid homomorphism `glMap : M_{ι × S}(F_2) → M_ι(R)` sends the
elementary matrix `x_{(i,α),(j,β)}(c)` to `1 + E_{ij}(c • α p β*)`
(`glMap_elementaryUnit_val`).  For `i ≠ j` this is the elementary matrix
`x_{ij}(c • α p β*)` whose coefficient lies in any two-sided ideal containing
`p`.  For `i = j` (hence `α ≠ β`) one factors through a third row `k ≠ i`
(`ι` nontrivial) with the commutator identity
`[x_{(i,α),(k,α)}(c), x_{(k,α),(i,β)}(1)] = x_{(i,α),(i,β)}(c)`.

Since `GL_N(F_2) = E_N(F_2)` (`FinitaryLinear.elementaryGroup_zmodTwo_eq_top`,
i.e. `K_1(F_2) = 0` in every finite rank), every unit of `M_{ι × S}(F_2)` is
mapped into any subgroup containing the elementary matrices with coefficients in
the ideal (`glMap_units_mem`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1

namespace CohnTwoData

variable {R : Type*} [Ring R] [Algebra (ZMod 2) R] (C : CohnTwoData R)
  (S : Finset (List (Fin 2))) {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem unit_mem (I : TwoSidedIdeal R) (hpI : C.p ∈ I) (α β : List (Fin 2)) :
    C.unit α β ∈ I := by
  show C.word α * C.p * C.coword β ∈ I
  exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hpI)

theorem smul_unit_mem (I : TwoSidedIdeal R) (hpI : C.p ∈ I) (c : ZMod 2)
    (α β : List (Fin 2)) : c • C.unit α β ∈ I := by
  rw [Algebra.smul_def]
  exact I.mul_mem_left _ _ (C.unit_mem I hpI α β)

theorem block_single (i j : ι) (α β : S) (c : ZMod 2) :
    C.block S (Matrix.single (i, α) (j, β) c) =
      Matrix.single i j (c • C.unit (α : List (Fin 2)) (β : List (Fin 2))) := by
  have hsymm : (Matrix.comp ι ι S S (ZMod 2)).symm (Matrix.single (i, α) (j, β) c) =
      Matrix.single i j (Matrix.single α β c) := by
    rw [Equiv.symm_apply_eq, Matrix.comp_single_single]
  rw [block, hsymm, Matrix.map_single, cornerHom_apply, corner_single]

theorem glMap_elementaryUnit_val (i j : ι) (α β : S) (h : (i, α) ≠ (j, β))
    (c : ZMod 2) :
    ((Units.map (C.glMap S) (elementaryUnit (i, α) (j, β) h c) : (Matrix ι ι R)ˣ) :
        Matrix ι ι R) =
      1 + Matrix.single i j (c • C.unit (α : List (Fin 2)) (β : List (Fin 2))) := by
  rw [Units.coe_map]
  show C.glMap S (1 + Matrix.single (i, α) (j, β) c) = _
  rw [glMap_one_add, block_single]

theorem glMap_elementaryUnit (i j : ι) (hij : i ≠ j) (α β : S) (h : (i, α) ≠ (j, β))
    (c : ZMod 2) :
    Units.map (C.glMap S) (elementaryUnit (i, α) (j, β) h c) =
      elementaryUnit i j hij (c • C.unit (α : List (Fin 2)) (β : List (Fin 2))) :=
  Units.ext (C.glMap_elementaryUnit_val S i j α β h c)

/-- **Every unit of `M_{ι × S}(F_2)` lands in the relative elementary subgroup**
(any subgroup containing the elementary matrices with coefficients in an ideal
`I ∋ p`), provided `ι` has at least two elements. -/
theorem glMap_units_mem [Nontrivial ι] (I : TwoSidedIdeal R) (hpI : C.p ∈ I)
    (H : Subgroup (Matrix ι ι R)ˣ)
    (hH : ∀ (i j : ι) (hij : i ≠ j) (a : R), a ∈ I → elementaryUnit i j hij a ∈ H)
    (U : (Matrix (ι × S) (ι × S) (ZMod 2))ˣ) : Units.map (C.glMap S) U ∈ H := by
  have hcross : ∀ (i j : ι) (hij : i ≠ j) (α β : S) (h : (i, α) ≠ (j, β)) (c : ZMod 2),
      elementaryUnit (i, α) (j, β) h c ∈ H.comap (Units.map (C.glMap S)) := by
    intro i j hij α β h c
    rw [Subgroup.mem_comap, C.glMap_elementaryUnit S i j hij α β h c]
    exact hH i j hij _ (C.smul_unit_mem I hpI c _ _)
  have hle : elementaryGroup (ι × S) (ZMod 2) ≤ H.comap (Units.map (C.glMap S)) := by
    rw [elementaryGroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, α⟩, ⟨j, β⟩, hne, c, rfl⟩
    by_cases hij : i = j
    · subst hij
      obtain ⟨k, hki⟩ := exists_ne i
      have h1 : ((i, α) : ι × S) ≠ (k, α) := fun h ↦ hki (congrArg Prod.fst h).symm
      have h2 : ((k, α) : ι × S) ≠ (i, β) := fun h ↦ hki (congrArg Prod.fst h)
      exact elementaryUnit_mem_of_two_step _ (i, α) (k, α) (i, β) h1 h2 hne c
        (hcross i k hki.symm α α h1 c) (hcross k i hki α β h2 1)
    · exact hcross i j hij α β hne c
  have hU : U ∈ elementaryGroup (ι × S) (ZMod 2) := by
    rw [FinitaryLinear.elementaryGroup_zmodTwo_eq_top]
    exact Subgroup.mem_top U
  exact Subgroup.mem_comap.mp (hle hU)

end CohnTwoData

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.unit_mem
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.smul_unit_mem
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.block_single
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.glMap_elementaryUnit_val
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.glMap_elementaryUnit
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.glMap_units_mem
