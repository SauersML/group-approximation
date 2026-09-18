import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Nontrivial
import GroupApproximation.Meta.AxiomGuard

/-!
# Pure characteristic `p`, exponent `p`: a common field (lane bh-met-52)

Two fields of characteristic `p` embed into a common field of characteristic `p`: view both as
`ZMod p`-algebras, take a maximal ideal of the (nonzero) tensor product and pass to the quotient.
By induction the same holds for finitely many fields.  This is the characteristic-`p` analogue of
`exists_common_field` / `exists_common_field_finset` (`TorsionFreeCoprimaryField`).
-/

open scoped TensorProduct

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

/-- Two fields of characteristic `p` embed into a common field of characteristic `p`. -/
theorem exists_common_field_charP (p : ℕ) [Fact p.Prime] (K₁ K₂ : Type) [Field K₁] [Field K₂]
    [CharP K₁ p] [CharP K₂ p] :
    ∃ (L : Type) (_ : Field L), CharP L p ∧ Nonempty (K₁ →+* L) ∧ Nonempty (K₂ →+* L) := by
  letI : Algebra (ZMod p) K₁ := ZMod.algebra K₁ p
  letI : Algebra (ZMod p) K₂ := ZMod.algebra K₂ p
  haveI : Nontrivial (K₁ ⊗[ZMod p] K₂) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain (ZMod p) K₁ K₂
      (algebraMap (ZMod p) K₁).injective (algebraMap (ZMod p) K₂).injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K₁ ⊗[ZMod p] K₂)
  letI : Field (K₁ ⊗[ZMod p] K₂ ⧸ m) := Ideal.Quotient.field m
  let f₁ : K₁ →+* K₁ ⊗[ZMod p] K₂ ⧸ m :=
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeLeftRingHom :
      K₁ →+* K₁ ⊗[ZMod p] K₂)
  let f₂ : K₂ →+* K₁ ⊗[ZMod p] K₂ ⧸ m :=
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight :
      K₂ →ₐ[ZMod p] K₁ ⊗[ZMod p] K₂).toRingHom
  exact ⟨K₁ ⊗[ZMod p] K₂ ⧸ m, inferInstance, charP_of_injective_ringHom f₁.injective p,
    ⟨f₁⟩, ⟨f₂⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.exists_common_field_charP

/-- A finite family of fields of characteristic `p` embeds into a common field of
characteristic `p`. -/
theorem exists_common_field_charP_finset (p : ℕ) [Fact p.Prime] {J : Type} [DecidableEq J]
    (K : J → Type) [∀ i, Field (K i)] [∀ i, CharP (K i) p] (s : Finset J) :
    ∃ (L : Type) (_ : Field L), CharP L p ∧ ∀ i ∈ s, Nonempty (K i →+* L) := by
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨ZMod p, inferInstance, inferInstance, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s _ ih =>
    obtain ⟨L, _, _, hs⟩ := ih
    obtain ⟨M, _, hM, ⟨g⟩, ⟨f⟩⟩ := exists_common_field_charP p L (K a)
    refine ⟨M, inferInstance, hM, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact ⟨f⟩
    · obtain ⟨h⟩ := hs i hi'
      exact ⟨g.comp h⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.exists_common_field_charP_finset

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
