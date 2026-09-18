import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.ChoiEffrosKraus
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-27, part 2: Cauchy--Schwarz for the column pairing

`‖⟨u, v⟩‖ ≤ √‖⟨u, u⟩‖ · √‖⟨v, v⟩‖` for `u v : Y → A`.

The column space `Y → A` is a Hilbert `A`-module, `C⋆ᵐᵒᵈ(A, Y → A)`, with the Mathlib inner
product `⟪x, y⟫ = ∑_y (y i) (x i)⋆`.  The column pairing is
`⟨u, v⟩ = ⟪v⋆, u⋆⟫`, where `⋆` is applied pointwise.  Mathlib's Cauchy--Schwarz inequality
`CStarModule.norm_inner_le` is then applied.  The Hilbert-module structure needs a partial
order on `A`, supplied locally by `CStarAlgebra.spectralOrder`.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-- **Cauchy--Schwarz for the column pairing.** -/
theorem choiEffros_norm_pair_le {Y : Type} [Fintype Y] (u v : Y → A) :
    ‖choiEffrosPair u v‖ ≤ √‖choiEffrosPair u u‖ * √‖choiEffrosPair v v‖ := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hinner : ∀ w z : Y → A,
      Inner.inner A ((_root_.WithCStarModule.equiv A (Y → A)).symm fun y ↦ star (w y))
        ((_root_.WithCStarModule.equiv A (Y → A)).symm fun y ↦ star (z y)) =
        choiEffrosPair z w := by
    intro w z
    rw [_root_.WithCStarModule.pi_inner]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [_root_.WithCStarModule.equiv_symm_pi_apply, _root_.WithCStarModule.equiv_symm_pi_apply,
      _root_.WithCStarModule.inner_def, star_star]
  have hnorm : ∀ w : Y → A,
      ‖(_root_.WithCStarModule.equiv A (Y → A)).symm fun y ↦ star (w y)‖ =
        √‖choiEffrosPair w w‖ := by
    intro w
    rw [_root_.CStarModule.norm_eq_sqrt_norm_inner_self (A := A)
      ((_root_.WithCStarModule.equiv A (Y → A)).symm fun y ↦ star (w y)), hinner]
  have h := _root_.CStarModule.norm_inner_le (A := A) (_root_.WithCStarModule A (Y → A))
    (x := (_root_.WithCStarModule.equiv A (Y → A)).symm fun y ↦ star (v y))
    (y := (_root_.WithCStarModule.equiv A (Y → A)).symm fun y ↦ star (u y))
  rw [hinner, hnorm, hnorm] at h
  exact h.trans_eq (mul_comm _ _)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffros_norm_pair_le

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
