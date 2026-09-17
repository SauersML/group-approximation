import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.Transvections
import GroupApproximation.Leavitt.CongruenceSubgroups
import Mathlib.LinearAlgebra.Span.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# Excision: a unit congruent to `1` modulo the matrix units is relatively elementary

Lane `sk-leavitt-19`, fourth module.

Let `M ⊆ R` be the `F_2`-span of the matrix units `u(α, β) = α p β*`.  If the
entries of `u - 1` and of `u⁻¹ - 1` lie in `M`, then finitely many words `S`
suffice, so `u - 1 = block A` and `u⁻¹ - 1 = block B` for matrices `A, B` over
`F_2` indexed by `ι × S` (`exists_block_eq`).  As `p ≠ 0`, `glMap` is injective
(`glMap_injective`), so `1 + A` is invertible with inverse `1 + B`, and
`u = glMap (1 + A)`.  By `glMap_units_mem` (`K_1(F_2) = 0` plus the
commutator trick), `u` lies in `EL_ι(R, I)` for every two-sided ideal `I ∋ p`
(`mem_relativeElementary_of_unitSpan`).  This is excision for the ideal with
local units `α p β*`: `GL(R, I) ∩ (1 + M_ι(M)) = E(R, I)` needs only
`K_1(F_2) = 0`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1

namespace CohnTwoData

variable {R : Type*} [Ring R] [Algebra (ZMod 2) R] (C : CohnTwoData R)

/-- The `F_2`-span of the matrix units `α p β*`. -/
def unitSpan : Submodule (ZMod 2) R :=
  Submodule.span (ZMod 2) (Set.range fun ab : List (Fin 2) × List (Fin 2) ↦ C.unit ab.1 ab.2)

theorem unit_mem_unitSpan (α β : List (Fin 2)) : C.unit α β ∈ C.unitSpan := by
  rw [unitSpan]
  exact Submodule.subset_span ⟨(α, β), rfl⟩

theorem corner_smul (S : Finset (List (Fin 2))) (c : ZMod 2) (N : Matrix S S (ZMod 2)) :
    C.corner S (c • N) = c • C.corner S N := by
  simp only [corner, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- Every element of the span of the matrix units is a corner over all large
enough finite sets of words. -/
theorem exists_corner_of_mem {x : R} (hx : x ∈ C.unitSpan) :
    ∃ S₀ : Finset (List (Fin 2)), ∀ S : Finset (List (Fin 2)), S₀ ⊆ S →
      ∃ N : Matrix S S (ZMod 2), C.corner S N = x := by
  rw [unitSpan] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    refine ⟨{a, b}, fun S hS ↦ ?_⟩
    have ha : a ∈ S := hS (Finset.mem_insert_self a {b})
    have hb : b ∈ S := hS (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
    exact ⟨Matrix.single ⟨a, ha⟩ ⟨b, hb⟩ 1,
      (C.corner_single S ⟨a, ha⟩ ⟨b, hb⟩ 1).trans (one_smul _ _)⟩
  | zero => exact ⟨∅, fun S _ ↦ ⟨0, C.corner_zero S⟩⟩
  | add x y _ _ hx hy =>
    obtain ⟨S₁, h₁⟩ := hx
    obtain ⟨S₂, h₂⟩ := hy
    refine ⟨S₁ ∪ S₂, fun S hS ↦ ?_⟩
    obtain ⟨N₁, hN₁⟩ := h₁ S (Finset.union_subset_left hS)
    obtain ⟨N₂, hN₂⟩ := h₂ S (Finset.union_subset_right hS)
    exact ⟨N₁ + N₂, by rw [corner_add, hN₁, hN₂]⟩
  | smul c x _ hx =>
    obtain ⟨S₁, h₁⟩ := hx
    refine ⟨S₁, fun S hS ↦ ?_⟩
    obtain ⟨N, hN⟩ := h₁ S hS
    exact ⟨c • N, by rw [corner_smul, hN]⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_block_eq (X Y : Matrix ι ι R) (hX : ∀ i j, X i j ∈ C.unitSpan)
    (hY : ∀ i j, Y i j ∈ C.unitSpan) :
    ∃ (S : Finset (List (Fin 2))) (A B : Matrix (ι × S) (ι × S) (ZMod 2)),
      C.block S A = X ∧ C.block S B = Y := by
  choose SX hSX using fun i j ↦ C.exists_corner_of_mem (hX i j)
  choose SY hSY using fun i j ↦ C.exists_corner_of_mem (hY i j)
  obtain ⟨S, hS⟩ : ∃ S : Finset (List (Fin 2)), ∀ i j, SX i j ∪ SY i j ⊆ S :=
    ⟨(Finset.univ : Finset (ι × ι)).biUnion fun ij ↦ SX ij.1 ij.2 ∪ SY ij.1 ij.2,
      fun i j ↦ Finset.subset_biUnion_of_mem (fun ij : ι × ι ↦ SX ij.1 ij.2 ∪ SY ij.1 ij.2)
        (Finset.mem_univ (i, j))⟩
  choose NX hNX using fun i j ↦ hSX i j S (Finset.union_subset_left (hS i j))
  choose NY hNY using fun i j ↦ hSY i j S (Finset.union_subset_right (hS i j))
  refine ⟨S, Matrix.comp ι ι S S (ZMod 2) (Matrix.of NX),
    Matrix.comp ι ι S S (ZMod 2) (Matrix.of NY), ?_, ?_⟩
  · ext i j
    rw [block, Equiv.symm_apply_apply, Matrix.map_apply, Matrix.of_apply, cornerHom_apply, hNX]
  · ext i j
    rw [block, Equiv.symm_apply_apply, Matrix.map_apply, Matrix.of_apply, cornerHom_apply, hNY]

theorem glMap_injective (hp : C.p ≠ 0) (S : Finset (List (Fin 2))) :
    Function.Injective (C.glMap (ι := ι) S) := by
  intro B B' h
  rw [glMap_apply, glMap_apply] at h
  exact C.block_injective S hp (add_left_cancel h)

/-- **Excision for the matrix units.**  If `p ≠ 0`, `ι` has at least two
elements, `I` is a two-sided ideal containing `p`, and the entries of `u - 1`
and `u⁻¹ - 1` lie in the `F_2`-span of the matrix units, then `u ∈ EL_ι(R, I)`. -/
theorem mem_relativeElementary_of_unitSpan [Nontrivial ι] (hp : C.p ≠ 0)
    (I : TwoSidedIdeal R) (hpI : C.p ∈ I) (u : (Matrix ι ι R)ˣ)
    (hu : ∀ i j, ((u : Matrix ι ι R) - 1) i j ∈ C.unitSpan)
    (hu' : ∀ i j, (((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) - 1) i j ∈ C.unitSpan) :
    ∃ g ∈ relativeElementary ι I, (g : (Matrix ι ι R)ˣ) = u := by
  obtain ⟨S, A, B, hA, hB⟩ := C.exists_block_eq _ _ hu hu'
  have hgA : C.glMap S (1 + A) = (u : Matrix ι ι R) := by
    rw [glMap_one_add, hA, add_sub_cancel]
  have hgB : C.glMap S (1 + B) = ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) := by
    rw [glMap_one_add, hB, add_sub_cancel]
  have hAB : (1 + A) * (1 + B) = 1 := by
    refine C.glMap_injective hp S ?_
    rw [map_mul, map_one, hgA, hgB, Units.mul_inv]
  have hBA : (1 + B) * (1 + A) = 1 := by
    refine C.glMap_injective hp S ?_
    rw [map_mul, map_one, hgA, hgB, Units.inv_mul]
  let U : (Matrix (ι × S) (ι × S) (ZMod 2))ˣ := ⟨1 + A, 1 + B, hAB, hBA⟩
  have hU : Units.map (C.glMap S) U = u := by
    apply Units.ext
    rw [Units.coe_map]
    exact hgA
  have hH : ∀ (i j : ι) (hij : i ≠ j) (a : R), a ∈ I →
      elementaryUnit i j hij a ∈ (relativeElementary ι I).map (elementaryGroup ι R).subtype :=
    fun i j hij a ha ↦
      Subgroup.mem_map.mpr ⟨elGen i j hij a, elGen_mem_relativeElementary i j hij ha, rfl⟩
  have hmem := C.glMap_units_mem S I hpI _ hH U
  rw [hU] at hmem
  obtain ⟨g, hg, hgu⟩ := Subgroup.mem_map.mp hmem
  exact ⟨g, hg, hgu⟩

end CohnTwoData

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.unit_mem_unitSpan
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.corner_smul
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.exists_corner_of_mem
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.exists_block_eq
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.glMap_injective
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.mem_relativeElementary_of_unitSpan
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.CohnTwoData.unitSpan
