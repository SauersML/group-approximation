import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Nontrivial
import GroupApproximation.Meta.AxiomGuard

/-!
# Torsion-free linearity: a common field of characteristic zero (lane bh-met-42)

Finitely many fields of characteristic zero embed into one field of characteristic zero.
For two fields `K₁, K₂` take a maximal ideal `m` of `K₁ ⊗[ℚ] K₂` (nontrivial since both
`K_i` are domains into which `ℚ` injects) and `L := K₁ ⊗[ℚ] K₂ ⧸ m`; every ring map out of a
field into a nontrivial ring is injective, so `L` has characteristic zero.  Finite families
follow by induction on a `Finset`.
-/

open scoped TensorProduct

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

/-- Two fields of characteristic zero embed into a common field of characteristic zero. -/
theorem exists_common_field (K₁ K₂ : Type) [Field K₁] [Field K₂] [CharZero K₁]
    [CharZero K₂] :
    ∃ (L : Type) (_ : Field L), CharZero L ∧ Nonempty (K₁ →+* L) ∧ Nonempty (K₂ →+* L) := by
  haveI : Nontrivial (K₁ ⊗[ℚ] K₂) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain ℚ K₁ K₂
      (algebraMap ℚ K₁).injective (algebraMap ℚ K₂).injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K₁ ⊗[ℚ] K₂)
  letI : Field (K₁ ⊗[ℚ] K₂ ⧸ m) := Ideal.Quotient.field m
  let f₁ : K₁ →+* K₁ ⊗[ℚ] K₂ ⧸ m :=
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeLeftRingHom :
      K₁ →+* K₁ ⊗[ℚ] K₂)
  let f₂ : K₂ →+* K₁ ⊗[ℚ] K₂ ⧸ m :=
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight :
      K₂ →ₐ[ℚ] K₁ ⊗[ℚ] K₂).toRingHom
  exact ⟨K₁ ⊗[ℚ] K₂ ⧸ m, inferInstance, charZero_of_injective_ringHom f₁.injective,
    ⟨f₁⟩, ⟨f₂⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.exists_common_field

/-- A finite family of fields of characteristic zero embeds into a common field of
characteristic zero. -/
theorem exists_common_field_finset {J : Type} [DecidableEq J] (K : J → Type)
    [∀ i, Field (K i)] [∀ i, CharZero (K i)] (s : Finset J) :
    ∃ (L : Type) (_ : Field L), CharZero L ∧ ∀ i ∈ s, Nonempty (K i →+* L) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨ℚ, inferInstance, inferInstance, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s _ ih =>
    obtain ⟨L, _, _, hs⟩ := ih
    obtain ⟨M, _, hM, ⟨g⟩, ⟨f⟩⟩ := exists_common_field L (K a)
    refine ⟨M, inferInstance, hM, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact ⟨f⟩
    · obtain ⟨h⟩ := hs i hi'
      exact ⟨g.comp h⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.exists_common_field_finset

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
