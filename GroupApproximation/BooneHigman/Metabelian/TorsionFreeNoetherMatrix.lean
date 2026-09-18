import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Free
import GroupApproximation.BooneHigman.Metabelian.TorsionFreeCoprimaryStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Torsion-free linearity, coprimary case: matrix packaging (lane bh-met-43)

The conclusion of `CoprimaryTorsionFreeLinearityStatement` asks for matrices over a field of
characteristic zero.  This file turns a `Q`-action by `K`-linear endomorphisms of a
finite-dimensional `K`-vector space `V`, together with an equivariant additive embedding
`W ↪ V`, into that matrix form, by choosing a basis `Fin d → V`.

* `noether_exists_matrix_rep`: the packaging lemma.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

/-- **Packaging.** A `Q`-equivariant additive embedding of `W` into a finite-dimensional vector
space over a field of characteristic zero, on which `Q` acts linearly, gives the matrix
conclusion of `CoprimaryTorsionFreeLinearityStatement`. -/
theorem noether_exists_matrix_rep {Q W K V : Type} [CommGroup Q] [AddCommGroup W]
    [Module (MonoidAlgebra ℤ Q) W] [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hK : ringChar K = 0) (σ : Q →* Module.End K V)
    (ι₀ : W →+ V) (hι₀ : Function.Injective ι₀)
    (hσ : ∀ (q : Q) (w : W), ι₀ (MonoidAlgebra.of ℤ Q q • w) = σ q (ι₀ w)) :
    ∃ (K' : Type) (_ : Field K') (d : ℕ) (ρ : Q →* Matrix.GeneralLinearGroup (Fin d) K')
      (ι : W →+ (Fin d → K')), ringChar K' = 0 ∧ Function.Injective ι ∧
      ∀ (q : Q) (w : W), ι (MonoidAlgebra.of ℤ Q q • w) =
        Matrix.mulVec (ρ q : Matrix (Fin d) (Fin d) K') (ι w) := by
  let b := Module.finBasis K V
  let ρ : Q →* Matrix.GeneralLinearGroup (Fin (Module.finrank K V)) K :=
    (Units.map (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom).comp σ.toHomUnits
  let ι : W →+ (Fin (Module.finrank K V) → K) := b.equivFun.toLinearMap.toAddMonoidHom.comp ι₀
  refine ⟨K, inferInstance, Module.finrank K V, ρ, ι, hK, b.equivFun.injective.comp hι₀, ?_⟩
  intro q w
  show b.equivFun (ι₀ (MonoidAlgebra.of ℤ Q q • w)) =
    Matrix.mulVec (LinearMap.toMatrix b b (σ q)) (b.equivFun (ι₀ w))
  rw [hσ, b.equivFun_apply, b.equivFun_apply, LinearMap.toMatrix_mulVec_repr]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.noether_exists_matrix_rep

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
