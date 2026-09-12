import GroupApproximation.Manuscript.OneSidedMFRadical.UniversalGroupB
import GroupApproximation.Leavitt.ElementaryWeylMonomial
import GroupApproximation.Leavitt.ElementaryDoubleSwap
import GroupApproximation.Leavitt.ElementaryFinitelyGeneratedRing
import GroupApproximation.Leavitt.ElementaryTransvectionExtraction
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite generation and an involution normally generating the universal group

The current manuscript uses the positive double transposition
`w₀₁ w₂₃ w₀₂²`.  `ElementaryDoubleSwap` proves that it has order two and
normally generates the rank-four elementary group over every nontrivial
unital ring, including rings of characteristic two.

The single Weyl element called `sigma` below is retained as a separate
order-four normal generator.  It is not the manuscript's involution, and
its square does not normally generate in characteristic two.  The printed
statement at the end uses `ElementaryDoubleSwap.doubleSwap` instead.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace UniversalGroupSigma

open UniversalGroupB
open UniversalPair
open ElementaryWeyl

/-! ## Indices -/

theorem h01 : (0 : Fin 4) ≠ 1 := by decide
theorem h02 : (0 : Fin 4) ≠ 2 := by decide
theorem h12 : (1 : Fin 4) ≠ 2 := by decide

/-! ## `2 ≠ 0` in the universal ring -/

/-- **`2 ≠ 0` in `𝒞`.**  The witness is the binary Leavitt algebra over `ℚ`: it
carries a Leavitt family, hence a properly infinite unit, hence a ring map out
of `𝒞`; and it is a nontrivial `ℚ`-algebra, hence of characteristic zero. -/
theorem two_ne_zero_universalPairRing : (2 : UniversalPairRing) ≠ 0 := by
  haveI : CharZero (BinaryLeavitt.BinaryLeavittAlgebra ℚ) :=
    charZero_of_injective_ringHom
      (algebraMap ℚ (BinaryLeavitt.BinaryLeavittAlgebra ℚ)).injective
  intro h
  have himg := congrArg (lift (ofLeavittFamily (BinaryLeavitt.family ℚ))) h
  rw [map_zero, map_ofNat] at himg
  exact (two_ne_zero) himg

/-! ## The element `σ` -/

/-- The separate order-four Weyl generator, in zero-based indices. -/
noncomputable def sigma : B := weyl (0 : Fin 4) 1 h01

theorem sigma_def : sigma = weyl (S := UniversalPairRing) (0 : Fin 4) 1 h01 := rfl

/-- The Weyl unit underlying `σ`. -/
noncomputable def sigmaUnit : (Matrix (Fin 4) (Fin 4) UniversalPairRing)ˣ :=
  weylUnit (S := UniversalPairRing) (0 : Fin 4) 1 h01

theorem sigma_val :
    ((sigma : B) : (Matrix (Fin 4) (Fin 4) UniversalPairRing)ˣ) = sigmaUnit :=
  weyl_val _ _ _

/-- **`σ² = diag(-1,-1,1,1)`.** -/
theorem sigmaUnit_sq_val :
    ((sigmaUnit * sigmaUnit : (Matrix (Fin 4) (Fin 4) UniversalPairRing)ˣ) :
        Matrix (Fin 4) (Fin 4) UniversalPairRing)
      = 1 - Matrix.single 0 0 (2 : UniversalPairRing)
          - Matrix.single 1 1 (2 : UniversalPairRing) := by
  rw [Units.val_mul, sigmaUnit, weylUnit_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply,
      Matrix.one_apply, Matrix.sub_apply, Matrix.add_apply] <;> norm_num

/-- `σ² · σ² = 1`: the square of `diag(-1,-1,1,1)` is the identity. -/
theorem sigmaUnit_sq_mul_sq :
    (sigmaUnit * sigmaUnit) * (sigmaUnit * sigmaUnit) = 1 := by
  apply Units.ext
  rw [Units.val_mul, sigmaUnit_sq_val, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply,
      Matrix.one_apply, Matrix.sub_apply] <;> norm_num

/-- **`σ⁴ = 1`**, over every ring. -/
theorem sigmaUnit_pow_four : sigmaUnit ^ 4 = 1 := by
  have h4 : sigmaUnit ^ 4 = (sigmaUnit ^ 2) ^ 2 := pow_mul sigmaUnit 2 2
  rw [h4, pow_two, pow_two]
  exact sigmaUnit_sq_mul_sq

theorem sigma_pow_four : sigma ^ 4 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, sigma_val, sigmaUnit_pow_four]
  rfl

/-- **`σ² ≠ 1`**, which is exactly `2 ≠ 0` in `𝒞`. -/
theorem sigma_sq_ne_one : sigma ^ 2 ≠ 1 := by
  intro h
  have hcoe : (sigmaUnit * sigmaUnit :
      (Matrix (Fin 4) (Fin 4) UniversalPairRing)ˣ) = 1 := by
    have hv := congrArg
      (fun g : B ↦ ((g : (Matrix (Fin 4) (Fin 4) UniversalPairRing)ˣ))) h
    simpa [Subgroup.coe_pow, sigma_val, pow_two] using hv
  have hmat := congrArg
    (fun u : (Matrix (Fin 4) (Fin 4) UniversalPairRing)ˣ ↦
      (u : Matrix (Fin 4) (Fin 4) UniversalPairRing)) hcoe
  rw [sigmaUnit_sq_val, Units.val_one] at hmat
  have h00 := congrFun (congrFun hmat 0) 0
  simp [Matrix.sub_apply] at h00
  exact two_ne_zero_universalPairRing h00

/-- **`σ` has order four.** -/
theorem orderOf_sigma : orderOf sigma = 4 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := sigma)
    (by simpa using sigma_sq_ne_one) (by simpa using sigma_pow_four)
  simpa using h

/-! ## `σ` normally generates -/

/-- The root `e₀₂(1)` lies in the normal closure of the Weyl generator. -/
theorem elGen_mem_normalClosure :
    elGen (R := UniversalPairRing) (0 : Fin 4) 2 h02 1 ∈
      Subgroup.normalClosure ({sigma} : Set B) := by
  set N : Subgroup B := Subgroup.normalClosure ({sigma} : Set B) with hNdef
  haveI hNn : N.Normal := Subgroup.normalClosure_normal
  have hsig : sigma ∈ N := Subgroup.subset_normalClosure rfl
  have hAinv : (elGen (R := UniversalPairRing) (0 : Fin 4) 2 h02 1)⁻¹
      = elGen (0 : Fin 4) 2 h02 (-1) :=
    (elGen_neg_eq_inv (S := UniversalPairRing) (0 : Fin 4) 2 h02 1).symm
  -- One branch of the Weyl sign gives `e₀₂(e)` in `N`.
  have hmain : ∀ e : UniversalPairRing,
      sigma * elGen (0 : Fin 4) 2 h02 (-1) * sigma⁻¹ =
        elGen (1 : Fin 4) 2 h12 e →
      elGen (R := UniversalPairRing) (0 : Fin 4) 2 h02 e ∈ N := by
    intro e he
    have hstep : elGen (R := UniversalPairRing) (0 : Fin 4) 2 h02 1 * sigma *
        (elGen (0 : Fin 4) 2 h02 1)⁻¹ * sigma⁻¹ =
        elGen (0 : Fin 4) 2 h02 1 * elGen (1 : Fin 4) 2 h12 e := by
      rw [hAinv, mul_assoc, mul_assoc]
      congr 1
      rw [← mul_assoc]
      exact he
    have hcmem : elGen (R := UniversalPairRing) (0 : Fin 4) 2 h02 1 *
        elGen (1 : Fin 4) 2 h12 e ∈ N := by
      rw [← hstep]
      exact N.mul_mem (hNn.conj_mem _ hsig _) (N.inv_mem hsig)
    have hcomm : elGen (R := UniversalPairRing) (0 : Fin 4) 1 h01 1 *
        elGen (0 : Fin 4) 2 h02 1 =
        elGen (0 : Fin 4) 2 h02 1 * elGen (0 : Fin 4) 1 h01 1 :=
      elGen_commute h01 h02 (by decide) (by decide) 1 1
    have hshift : elGen (R := UniversalPairRing) (0 : Fin 4) 1 h01 1 *
        elGen (1 : Fin 4) 2 h12 e * (elGen (0 : Fin 4) 1 h01 1)⁻¹ =
        elGen (0 : Fin 4) 2 h02 (1 * e) * elGen (1 : Fin 4) 2 h12 e := by
      rw [← elGen_commutator (R := UniversalPairRing) (0 : Fin 4) 1 2 h01 h12 h02 1 e]
      group
    have hconjC : elGen (R := UniversalPairRing) (0 : Fin 4) 1 h01 1 *
        (elGen (0 : Fin 4) 2 h02 1 * elGen (1 : Fin 4) 2 h12 e) *
        (elGen (0 : Fin 4) 1 h01 1)⁻¹ =
        elGen (0 : Fin 4) 2 h02 (1 + e) * elGen (1 : Fin 4) 2 h12 e := by
      calc elGen (R := UniversalPairRing) (0 : Fin 4) 1 h01 1 *
            (elGen (0 : Fin 4) 2 h02 1 * elGen (1 : Fin 4) 2 h12 e) *
            (elGen (0 : Fin 4) 1 h01 1)⁻¹
          = elGen (0 : Fin 4) 2 h02 1 *
              (elGen (0 : Fin 4) 1 h01 1 * elGen (1 : Fin 4) 2 h12 e *
                (elGen (0 : Fin 4) 1 h01 1)⁻¹) := by
            rw [← mul_assoc, hcomm]; group
        _ = elGen (0 : Fin 4) 2 h02 1 *
              (elGen (0 : Fin 4) 2 h02 (1 * e) * elGen (1 : Fin 4) 2 h12 e) := by
            rw [hshift]
        _ = elGen (0 : Fin 4) 2 h02 (1 + e) * elGen (1 : Fin 4) 2 h12 e := by
            rw [one_mul, ← mul_assoc, elGen_mul]
    have hkey : elGen (R := UniversalPairRing) (0 : Fin 4) 1 h01 1 *
        (elGen (0 : Fin 4) 2 h02 1 * elGen (1 : Fin 4) 2 h12 e) *
        (elGen (0 : Fin 4) 1 h01 1)⁻¹ *
        (elGen (0 : Fin 4) 2 h02 1 * elGen (1 : Fin 4) 2 h12 e)⁻¹ =
        elGen (0 : Fin 4) 2 h02 e := by
      rw [hconjC, mul_inv_rev, ← elGen_neg_eq_inv, ← elGen_neg_eq_inv,
        show elGen (R := UniversalPairRing) (0 : Fin 4) 2 h02 (1 + e) *
            elGen (1 : Fin 4) 2 h12 e *
            (elGen (1 : Fin 4) 2 h12 (-e) * elGen (0 : Fin 4) 2 h02 (-1)) =
            elGen (0 : Fin 4) 2 h02 (1 + e) *
              (elGen (1 : Fin 4) 2 h12 e * elGen (1 : Fin 4) 2 h12 (-e)) *
              elGen (0 : Fin 4) 2 h02 (-1) from by group,
        elGen_mul, add_neg_cancel, elGen_zero, mul_one, elGen_mul]
      congr 1
      abel
    have hfinal := N.mul_mem
      (hNn.conj_mem _ hcmem (elGen (0 : Fin 4) 1 h01 1)) (N.inv_mem hcmem)
    rw [hkey] at hfinal
    exact hfinal
  have hconj := weyl_conj_elGen (S := UniversalPairRing) (0 : Fin 4) 1 h01
    (p := 0) (q := 2) h02 (p' := 1) (q' := 2) (by decide) (by decide) h12
    (-1 : UniversalPairRing)
  rw [← sigma_def] at hconj
  rcases hconj with hplus | hminus
  · have hx := hmain (-1) hplus
    have hinv : elGen (R := UniversalPairRing) (0 : Fin 4) 2 h02 1 =
        (elGen (0 : Fin 4) 2 h02 (-1))⁻¹ := by
      have h := elGen_neg_eq_inv (S := UniversalPairRing) (0 : Fin 4) 2 h02 (-1)
      simpa using h
    rw [hinv]
    exact N.inv_mem hx
  · refine hmain 1 ?_
    rw [hminus]
    norm_num

/-- **`σ` normally generates `B`.** -/
theorem normalClosure_sigma_eq_top :
    Subgroup.normalClosure ({sigma} : Set B) = ⊤ := by
  haveI : (Subgroup.normalClosure ({sigma} : Set B)).Normal :=
    Subgroup.normalClosure_normal
  exact elementaryGroup_normal_eq_top_of_elGen_mem (by simp) _ h02
    elGen_mem_normalClosure ⟨1, 1, by simp⟩

/-! ## Finite generation, and the printed theorem -/

theorem finitelyGenerated : Group.FG B :=
  elementaryGroup_finitelyGenerated_of_isFinitelyGeneratedRing
    UniversalPair.isFinitelyGeneratedRing 4 (by norm_num)

/-- **All printed clauses about `B`**, as one closed proposition: the
three of `PrintedUniversalGroupCore`, finite generation, and normal generation
by an involution. -/
def PrintedFullComplementaryIdempotentsUniversal : Prop :=
  PrintedUniversalGroupCore ∧
    Group.FG B ∧
    ∃ g : B, orderOf g = 2 ∧
      Subgroup.normalClosure ({g} : Set B) = ⊤

theorem manuscriptFullComplementaryIdempotentsUniversal :
    PrintedFullComplementaryIdempotentsUniversal :=
  ⟨manuscriptUniversalGroupCore, finitelyGenerated,
    ElementaryDoubleSwap.doubleSwap, ElementaryDoubleSwap.orderOf_doubleSwap,
    ElementaryDoubleSwap.normalClosure_doubleSwap_eq_top⟩

end UniversalGroupSigma
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation
open GroupApproximation.Manuscript.OneSidedMFRadical

#audit_closed_axioms
  UniversalGroupSigma.manuscriptFullComplementaryIdempotentsUniversal
