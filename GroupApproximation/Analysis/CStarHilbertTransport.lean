import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Moving a representation along an isometric isomorphism of Hilbert spaces

A `*`-representation on `H` becomes one on `K` as soon as `H` and `K` are
isometrically isomorphic: conjugate every operator by the isomorphism.  This is
the last step of the route that puts a separable C-star algebra on a Hilbert
space in `Type 0` — the GNS sum lives in the algebra's own universe, and a
countable Hilbert basis identifies it with `ℓ²` over a countable index, which is
small.

`conjStarAlgHom e : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)` is that conjugation,
`T ↦ e ∘ T ∘ e⁻¹`.  The algebraic clauses are the cancellation `e⁻¹ ∘ e = 1`
read off `LinearIsometryEquiv.symm_apply_apply`.  The adjoint clause is the one
with content and it is where the *isometry* is used rather than mere
invertibility: `⟪e a, e b⟫ = ⟪a, b⟫` is what turns the adjoint of the conjugate
into the conjugate of the adjoint.  It is proved through
`ContinuousLinearMap.eq_adjoint_iff` — the inner-product characterisation —
rather than through `adjoint_comp`, so that only `inner_map_map` and
`adjoint_inner_left` are needed.

`conjStarAlgHom_injective` is immediate: conjugation is undone by conjugating
back.  Composing it with a faithful representation of an algebra on `H` gives a
faithful representation on `K`, which is the only use this module has.
-/

namespace GroupApproximation
namespace CStarHilbertTransport

open scoped InnerProductSpace

noncomputable section

universe u v

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Conjugation of an operator by an isometric isomorphism. -/
def hilbertConjOp (e : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) : K →L[ℂ] K :=
  (e : H →L[ℂ] K) ∘L T ∘L (e.symm : K →L[ℂ] H)

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] theorem hilbertConjOp_apply (e : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) (x : K) :
    hilbertConjOp e T x = e (T (e.symm x)) := rfl

/-- **Conjugation by an isometric isomorphism, as a `*`-homomorphism.**  Every
algebraic clause is the cancellation `e⁻¹ ∘ e = 1`; the adjoint clause is where
the isometry is used. -/
def conjStarAlgHom (e : H ≃ₗᵢ[ℂ] K) :
    (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K) where
  toFun := hilbertConjOp e
  map_one' := by
    refine ContinuousLinearMap.ext fun x ↦ ?_
    rw [hilbertConjOp_apply, _root_.one_apply_eq_self, e.apply_symm_apply,
      _root_.one_apply_eq_self]
  map_mul' S T := by
    refine ContinuousLinearMap.ext fun x ↦ ?_
    rw [hilbertConjOp_apply, _root_.mul_apply_eq_comp, _root_.mul_apply_eq_comp]
    show e (S (T (e.symm x))) = hilbertConjOp e S (hilbertConjOp e T x)
    rw [hilbertConjOp_apply, hilbertConjOp_apply, e.symm_apply_apply]
  map_zero' := by
    refine ContinuousLinearMap.ext fun x ↦ ?_
    rw [hilbertConjOp_apply, _root_.zero_apply, map_zero, _root_.zero_apply]
  map_add' S T := by
    refine ContinuousLinearMap.ext fun x ↦ ?_
    rw [hilbertConjOp_apply, _root_.add_apply, map_add, _root_.add_apply,
      hilbertConjOp_apply, hilbertConjOp_apply]
  commutes' c := by
    refine ContinuousLinearMap.ext fun x ↦ ?_
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      hilbertConjOp_apply, _root_.smul_apply, _root_.one_apply_eq_self, map_smul,
      e.apply_symm_apply, _root_.smul_apply, _root_.one_apply_eq_self]
  map_star' T := by
    rw [ContinuousLinearMap.star_eq_adjoint (hilbertConjOp e T),
      ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    -- `⟪e a, b⟫ = ⟪a, e⁻¹ b⟫`, twice, with `inner_map_map` supplying the
    -- isometry; the middle step is the adjoint of `T` on `H`.
    have hx : ⟪hilbertConjOp e (star T) x, y⟫_ℂ
        = ⟪(star T) (e.symm x), e.symm y⟫_ℂ := by
      rw [hilbertConjOp_apply, ← e.inner_map_map ((star T) (e.symm x)) (e.symm y),
        e.apply_symm_apply]
    have hy : ⟪x, hilbertConjOp e T y⟫_ℂ = ⟪e.symm x, T (e.symm y)⟫_ℂ := by
      rw [hilbertConjOp_apply, ← e.inner_map_map (e.symm x) (T (e.symm y)),
        e.apply_symm_apply]
    rw [hx, hy, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]

@[simp] theorem conjStarAlgHom_apply (e : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    conjStarAlgHom e T = hilbertConjOp e T := rfl

/-- **Conjugation is faithful.**  It is undone by conjugating back. -/
theorem conjStarAlgHom_injective (e : H ≃ₗᵢ[ℂ] K) :
    Function.Injective (conjStarAlgHom e) := by
  intro S T hST
  refine ContinuousLinearMap.ext fun x ↦ ?_
  have h := congrArg (fun U : K →L[ℂ] K ↦ U (e x)) hST
  simp only [conjStarAlgHom_apply, hilbertConjOp_apply, e.symm_apply_apply] at h
  exact e.injective h

/-- **A faithful representation moves along an isometric isomorphism.**  This is
the only use of the conjugation: it relocates a faithful representation from the
Hilbert space the GNS construction produces to any space isometric to it. -/
theorem injective_comp_conjStarAlgHom {A : Type*} [CStarAlgebra A]
    (e : H ≃ₗᵢ[ℂ] K) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hπ : Function.Injective π) :
    Function.Injective ((conjStarAlgHom e).comp π) :=
  (conjStarAlgHom_injective e).comp hπ

end

end CStarHilbertTransport
end GroupApproximation
