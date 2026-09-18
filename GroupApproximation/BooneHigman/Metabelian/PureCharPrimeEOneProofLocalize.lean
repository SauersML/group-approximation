import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Finite
import GroupApproximation.BooneHigman.Metabelian.TorsionFreeCoprimaryBlock
import GroupApproximation.Meta.AxiomGuard

/-!
# Linearizing a torsion-free finite module over a domain (lane bh-met-52)

Let `D` be a domain and `N` a finitely generated `D`-module on which every nonzero `c : D` acts
injectively, and let a group `Q` act on `N` by `D`-linear maps.  Then `N` embeds
`Q`-equivariantly into `(Frac D)^d` with `Q` acting through `GL_d(Frac D)`: the map
`N → Frac D ⊗[D] N`, `x ↦ 1 ⊗ x`, is a localization map at the nonzero divisors, hence injective
on torsion-free `N`; the target is finite-dimensional, and `Q` acts on it by base change.

* `exists_matrix_of_domain_torsionFree`: the linearization.
-/

open scoped TensorProduct

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

/-- **Linearization over the fraction field.**  A finitely generated torsion-free module over a
domain `D`, with a group acting `D`-linearly, embeds equivariantly into `(Frac D)^d` with the
group acting through matrices. -/
theorem exists_matrix_of_domain_torsionFree {Q D N : Type} [Group Q] [CommRing D] [IsDomain D]
    [AddCommGroup N] [Module D N] [Module.Finite D N]
    (htf : ∀ c : D, c ≠ 0 → Function.Injective fun x : N => c • x)
    (act : Q → N → N) (T : Q →* Module.End D N) (hT : ∀ q x, act q x = T q x) :
    ∃ (d : ℕ) (ρ : Q →* Matrix.GeneralLinearGroup (Fin d) (FractionRing D))
      (ι : N →+ (Fin d → FractionRing D)), Function.Injective ι ∧
        ∀ q x, ι (act q x) =
          Matrix.mulVec (ρ q : Matrix (Fin d) (Fin d) (FractionRing D)) (ι x) := by
  let σ : Q →* Module.End (FractionRing D) (FractionRing D ⊗[D] N) :=
    { toFun := fun q => (T q).baseChange (FractionRing D)
      map_one' := by simp only [map_one, LinearMap.baseChange_one]
      map_mul' := fun a b => by simp only [map_mul, LinearMap.baseChange_mul] }
  refine exists_matrix_of_end act σ (TensorProduct.mk D (FractionRing D) N 1).toAddMonoidHom
    ?_ fun q x => ?_
  · intro x₁ x₂ hx
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors D)
      (TensorProduct.mk D (FractionRing D) N 1) (x₁ := x₁) (x₂ := x₂)).mp hx
    exact htf c (nonZeroDivisors.coe_ne_zero c) hc
  · show (1 : FractionRing D) ⊗ₜ[D] act q x = (T q).baseChange (FractionRing D) (1 ⊗ₜ[D] x)
    rw [LinearMap.baseChange_tmul, hT]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Coprimary.exists_matrix_of_domain_torsionFree

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
