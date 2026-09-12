import GroupApproximation.Algebra.FinitaryLinearBinarySimple
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The printed group `⋃_N SL_N(F_2)`

`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring`
(tex lines 1141--1145):

> `Rad_MF(EL_n(J)) = EL_n(J,JeJ) ≅ ⋃_N SL_N(F_2)  (n ≥ 4)`, an infinite simple
> locally finite group.

`V = F_2^{(ℕ)}` is carried as `F_2[X]` with its monomial basis `(b_j) = (X^j)`,
the same model as the Toeplitz--Jacobson algebra's shift space.  `SL_N(F_2)`
acts on `V` by the matrix on `b_0, …, b_{N-1}` and by the identity on the other
basis vectors (`blockSL N`, injective), and the printed union is the directed
supremum of those images, `binarySLUnion`.  It is exactly the finitary linear
group of `V` (`binarySLUnion_eq_finitary`), so it is infinite, simple, and
locally finite (`manuscriptSentence_binarySLUnionInfiniteSimpleLocallyFinite`).
-/

namespace GroupApproximation
namespace FinitaryLinear

open Matrix

/-- The printed `V = F_2^{(ℕ)}`, as `F_2[X]`. -/
abbrev BinarySpace : Type := Polynomial (ZMod 2)

/-- The standard basis `(b_j) = (X^j)` of `V`. -/
noncomputable abbrev binaryBasis : Module.Basis ℕ (ZMod 2) BinarySpace :=
  Polynomial.basisMonomials (ZMod 2)

/-- `Fin N ≃ {j : ℕ // j ∈ range N}`. -/
def finEquivRange (N : ℕ) : Fin N ≃ (Finset.range N) :=
  Fin.equivSubtype.trans (Equiv.subtypeEquivRight fun _ ↦ Finset.mem_range.symm)

/-- Reindexing invertible matrices along `Fin N ≃ range N`. -/
noncomputable def glReindex (N : ℕ) :
    (Matrix (Fin N) (Fin N) (ZMod 2))ˣ ≃* (Matrix (Finset.range N) (Finset.range N) (ZMod 2))ˣ :=
  Units.mapEquiv (reindexAlgEquiv (ZMod 2) (ZMod 2) (finEquivRange N)).toRingEquiv.toMulEquiv

/-- **The block embedding `SL_N(F_2) → Aut(V)`.** -/
noncomputable def blockSL (N : ℕ) :
    SpecialLinearGroup (Fin N) (ZMod 2) →* (BinarySpace ≃ₗ[ZMod 2] BinarySpace) :=
  (blockHom binaryBasis (Finset.range N)).comp
    ((glReindex N).toMonoidHom.comp SpecialLinearGroup.toGL)

theorem blockSL_injective (N : ℕ) : Function.Injective (blockSL N) := by
  intro A A' h
  have h1 := blockHom_injective binaryBasis (Finset.range N) h
  have h2 := (glReindex N).injective h1
  apply Subtype.ext
  exact congrArg (fun u : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ ↦ (u : Matrix (Fin N) (Fin N) (ZMod 2))) h2

/-- The image of `SL_N(F_2)` is the stabilizer of the block `b_0, …, b_{N-1}`. -/
theorem range_blockSL (N : ℕ) : (blockSL N).range = supportedOn binaryBasis (Finset.range N) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨A, rfl⟩
    exact blockHom_mem_supportedOn binaryBasis (Finset.range N) _
  · intro g hg
    obtain ⟨A, hA⟩ := supportedOn_le_range binaryBasis (Finset.range N) hg
    let A' : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ := (glReindex N).symm A
    have h2 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    have hdet : det (A' : Matrix (Fin N) (Fin N) (ZMod 2)) = 1 :=
      h2 _ (det_ne_zero_of_right_inverse
        (B := ((A'⁻¹ : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ) : Matrix (Fin N) (Fin N) (ZMod 2)))
        A'.mul_inv)
    refine ⟨⟨(A' : Matrix (Fin N) (Fin N) (ZMod 2)), hdet⟩, ?_⟩
    have htoGL : SpecialLinearGroup.toGL
        (⟨(A' : Matrix (Fin N) (Fin N) (ZMod 2)), hdet⟩ : SpecialLinearGroup (Fin N) (ZMod 2)) = A' :=
      Units.ext rfl
    simp only [blockSL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, htoGL, A',
      MulEquiv.apply_symm_apply]
    exact hA

/-- **The printed union `⋃_N SL_N(F_2)`**: the directed supremum of the block
images. -/
noncomputable def binarySLUnion : Subgroup (BinarySpace ≃ₗ[ZMod 2] BinarySpace) :=
  ⨆ N : ℕ, (blockSL N).range

/-- The printed union is the finitary linear group of `V`. -/
theorem binarySLUnion_eq_finitary : binarySLUnion = finitary binaryBasis := by
  refine le_antisymm (iSup_le fun N ↦ ?_) fun g hg ↦ ?_
  · rw [range_blockSL]
    exact supportedOn_le_finitary binaryBasis _
  · obtain ⟨T, hT⟩ := (mem_finitary binaryBasis).mp hg
    let N : ℕ := T.sup id + 1
    have hsub : T ⊆ Finset.range N := fun x hx ↦
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hx))
    have hmem : g ∈ (blockSL N).range := by
      rw [range_blockSL]
      exact hT.mono hsub
    exact Subgroup.mem_iSup_of_mem N hmem

/-- **Printed (tex 1142--1145).**  `⋃_N SL_N(F_2)` is a directed union of
injective block images, and it is an infinite simple locally finite group. -/
theorem manuscriptSentence_binarySLUnionInfiniteSimpleLocallyFinite :
    (∀ N : ℕ, Function.Injective (blockSL N)) ∧ Infinite binarySLUnion ∧
      IsSimpleGroup binarySLUnion ∧ IsLocallyFiniteGroup binarySLUnion := by
  let e : binarySLUnion ≃* finitary binaryBasis := MulEquiv.subgroupCongr binarySLUnion_eq_finitary
  haveI : Infinite (finitary binaryBasis) := infinite_finitary_zmodTwo binaryBasis
  haveI : IsSimpleGroup (finitary binaryBasis) :=
    isSimpleGroup_finitary_zmodTwo binaryBasis ⟨Finset.range 3, by simp⟩
  haveI : Nontrivial binarySLUnion := e.symm.injective.nontrivial
  exact ⟨blockSL_injective, Infinite.of_injective e.symm e.symm.injective,
    IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective,
    (isLocallyFiniteGroup_finitary binaryBasis).comap e.toMonoidHom e.injective⟩

end FinitaryLinear
end GroupApproximation

#audit_axioms GroupApproximation.FinitaryLinear.binarySLUnion_eq_finitary
#audit_closed_axioms GroupApproximation.FinitaryLinear.manuscriptSentence_binarySLUnionInfiniteSimpleLocallyFinite
