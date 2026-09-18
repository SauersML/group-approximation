import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.ChoiEffrosCauchySchwarz
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-27, part 3: Choi's inequality for Kraus-column maps

Let `G : Y → A` satisfy `⟨G, G⟩ = 1`, and suppose `ψ = ψ_G` is contractive.  Then for all
matrices `x` and `M`,

`‖ψ(x M) − ψ(x) ψ(M)‖ ≤ √‖ψ(x x⋆) − ψ(x) ψ(x)⋆‖ · ‖M‖`.

The proof works in the Hilbert module of columns.  Set `ξ = x⋆ G`, `η = M G` and
`ξ' = ξ − G ψ(x)⋆`.  Then

* `⟨ξ', η⟩ = ψ(x M) − ψ(x) ψ(M)`;
* `⟨ξ', ξ'⟩ = ψ(x x⋆) − ψ(x) ψ(x)⋆`, using `⟨G, G⟩ = 1`;
* `⟨η, η⟩ = ψ(M⋆ M)`, and `‖ψ(M⋆ M)‖ ≤ ‖M⋆ M‖ = ‖M‖²` by contractivity and the
  C⋆-identity for the operator norm.

Cauchy--Schwarz (`choiEffros_norm_pair_le`) finishes the argument.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-- **Choi's inequality** for a contractive Kraus-column map with `⟨G, G⟩ = 1`. -/
theorem choiEffros_norm_krausMap_mul_sub_le {Y : Type} [Fintype Y] [DecidableEq Y]
    (G : Y → A) (hG : choiEffrosPair G G = 1)
    (hcontr : ∀ M : Matrix Y Y ℂ, ‖choiEffrosKrausMap G M‖ ≤ ‖M‖) (x M : Matrix Y Y ℂ) :
    ‖choiEffrosKrausMap G (x * M) - choiEffrosKrausMap G x * choiEffrosKrausMap G M‖ ≤
      √‖choiEffrosKrausMap G (x * star x) -
          choiEffrosKrausMap G x * star (choiEffrosKrausMap G x)‖ * ‖M‖ := by
  have hξG : choiEffrosPair (choiEffrosAct (star x) G) G = choiEffrosKrausMap G x := by
    have h := choiEffros_pair_act_act G x (1 : Matrix Y Y ℂ)
    rwa [choiEffros_act_one, mul_one] at h
  have hGξ : choiEffrosPair G (choiEffrosAct (star x) G) = star (choiEffrosKrausMap G x) := by
    rw [← hξG, choiEffros_star_pair]
  have hξη : choiEffrosPair (choiEffrosAct (star x) G) (choiEffrosAct M G) =
      choiEffrosKrausMap G (x * M) :=
    choiEffros_pair_act_act G x M
  have hGη : choiEffrosPair G (choiEffrosAct M G) = choiEffrosKrausMap G M := rfl
  have hξξ : choiEffrosPair (choiEffrosAct (star x) G) (choiEffrosAct (star x) G) =
      choiEffrosKrausMap G (x * star x) :=
    choiEffros_pair_act_act G x (star x)
  have hηη : choiEffrosPair (choiEffrosAct M G) (choiEffrosAct M G) =
      choiEffrosKrausMap G (star M * M) := by
    have h := choiEffros_pair_act_act G (star M) M
    rwa [star_star] at h
  have hmain :
      choiEffrosPair (choiEffrosShift (choiEffrosAct (star x) G) G (star (choiEffrosKrausMap G x)))
          (choiEffrosAct M G) =
        choiEffrosKrausMap G (x * M) - choiEffrosKrausMap G x * choiEffrosKrausMap G M := by
    rw [choiEffros_pair_shift_left, hξη, hGη, star_star]
  have hself :
      choiEffrosPair (choiEffrosShift (choiEffrosAct (star x) G) G (star (choiEffrosKrausMap G x)))
          (choiEffrosShift (choiEffrosAct (star x) G) G (star (choiEffrosKrausMap G x))) =
        choiEffrosKrausMap G (x * star x) -
          choiEffrosKrausMap G x * star (choiEffrosKrausMap G x) := by
    rw [choiEffros_pair_shift_left, choiEffros_pair_shift_right, choiEffros_pair_shift_right, hG,
      hGξ, hξG, hξξ, one_mul, sub_self, mul_zero, sub_zero]
  have hsq : √‖choiEffrosKrausMap G (star M * M)‖ ≤ ‖M‖ := by
    have h : ‖choiEffrosKrausMap G (star M * M)‖ ≤ ‖M‖ * ‖M‖ :=
      calc ‖choiEffrosKrausMap G (star M * M)‖ ≤ ‖star M * M‖ := hcontr _
        _ = ‖M‖ * ‖M‖ := by
          rw [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose_mul_self]
    exact (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_mul_self (norm_nonneg M))
  rw [← hmain]
  refine (choiEffros_norm_pair_le _ _).trans ?_
  rw [hself, hηη]
  exact mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffros_norm_krausMap_mul_sub_le

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
