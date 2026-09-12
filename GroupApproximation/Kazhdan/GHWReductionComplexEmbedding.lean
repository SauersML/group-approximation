import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Complex embeddings of a field with a prescribed transcendence basis

Guentner--Higson--Weinberger, *The Novikov conjecture for linear groups*
(Publ. Math. IHÉS 101 (2005)), §2, Lemma 2 extends an embedding `K ⊆ ℂ` to `K(X)` "in
countably many distinct ways", sending `X` to distinct complex numbers.  The field-theoretic
fact behind every archimedean place of their proof of Theorem 4 is the following
(`ghwComplexEmbeddingExtension`).

> Let `K` be a field of characteristic zero, `t₁, …, tₙ ∈ K` algebraically independent over `ℚ`
> with `K` algebraic over `ℚ(t)`, and `z₁, …, zₙ ∈ ℂ` algebraically independent over `ℚ`.  Then
> there is a ring homomorphism `σ : K → ℂ` with `σ(tᵢ) = zᵢ`.

The proof: the rational function field `ℚ(t)` and `ℚ(z)` are both the fraction field of
`ℚ[X₁, …, Xₙ]` (`AlgebraicIndependent.aevalEquivField`), which gives `ℚ(t) → ℂ` with `tᵢ ↦ zᵢ`
(`exists_algHom_adjoin_apply`); an algebraic extension embeds into the algebraically closed
`ℂ` over any embedding of its base (`IsAlgClosed.surjective_restrictDomain_of_isAlgebraic`).

## Manuscript status

Infrastructure for the Toeplitz--Jacobson remark (tex line 1146, "every countable subgroup of
`GL_2` over a field has the Haagerup property [GHW, Theorem 4]"); certifies no printed sentence
on its own.
-/

namespace GroupApproximation
namespace GHW

/-- **The complex embedding extension of GHW's archimedean places.** -/
def GHWComplexEmbeddingExtension : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] [Countable K] {ι : Type} [Finite ι]
    (t : ι → K), AlgebraicIndependent ℚ t → Algebra.IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) K →
    ∀ z : ι → ℂ, AlgebraicIndependent ℚ z → ∃ σ : K →+* ℂ, ∀ i, σ (t i) = z i

/-- **`ℚ(t)` embeds into `ℂ` with `tᵢ ↦ zᵢ`**, for algebraically independent `t` and `z`. -/
theorem exists_algHom_adjoin_apply {K : Type} [Field K] [CharZero K] {ι : Type}
    {t : ι → K} (ht : AlgebraicIndependent ℚ t) {z : ι → ℂ} (hz : AlgebraicIndependent ℚ z) :
    ∃ τ : IntermediateField.adjoin ℚ (Set.range t) →ₐ[ℚ] ℂ,
      ∀ i, τ ⟨t i, IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)⟩ = z i := by
  refine ⟨(IntermediateField.val _).comp
    (hz.aevalEquivField.toAlgHom.comp ht.aevalEquivField.symm.toAlgHom), fun i => ?_⟩
  have h1 : ht.aevalEquivField.symm
      ⟨t i, IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)⟩ =
      algebraMap (MvPolynomial ι ℚ) (FractionRing (MvPolynomial ι ℚ)) (MvPolynomial.X i) := by
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe, MvPolynomial.aeval_X]
  show ((hz.aevalEquivField (ht.aevalEquivField.symm
    ⟨t i, IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)⟩)) : ℂ) = z i
  rw [h1, AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe, MvPolynomial.aeval_X]

/-- **GHW's archimedean places exist with prescribed values on a transcendence basis.** -/
theorem ghwComplexEmbeddingExtension : GHWComplexEmbeddingExtension := by
  intro K _ _ _ ι _ t ht halg z hz
  obtain ⟨τ, hτ⟩ := exists_algHom_adjoin_apply ht hz
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
    (K := ℚ) (L := IntermediateField.adjoin ℚ (Set.range t)) (M := ℂ) (E := K) τ
  refine ⟨φ.toRingHom, fun i => ?_⟩
  have h := congrArg
    (fun ψ : IntermediateField.adjoin ℚ (Set.range t) →ₐ[ℚ] ℂ =>
      ψ ⟨t i, IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)⟩) hφ
  simp only at h
  rw [hτ i] at h
  exact h

end GHW
end GroupApproximation

#audit_axioms GroupApproximation.GHW.exists_algHom_adjoin_apply
#audit_closed_axioms GroupApproximation.GHW.ghwComplexEmbeddingExtension
