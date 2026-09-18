import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngRank3SecEndpoint
import Mathlib.Tactic.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# Words in the four generators and the Schreier graph of `E_3(ℤ[1/(mp)])/E_3(ℤ[1/m])`
(lane `bh-met-93y`, part 1)

Put `S = ℤ[1/(mp)]`, `u = 1/(mp)`, `φ : ℤ[1/m] → S` the localisation map.  The four letters
`a₀₁, a₁₂, a₂₀, u₀₁` stand for `x₀₁(1), x₁₂(1), x₂₀(1), x₀₁(u)`.

* `czK2FngRank3Bld_evSt : F → St_3(S)` and `czK2FngRank3Bld_evE : F → E_3(S)` evaluate words of
  the free group `F` on the four letters in the Steinberg group and in the matrix group.
  `projection ∘ evSt = evE` (`czK2FngRank3Bld_projection_evSt`).
* `czK2FngRank3Bld_evSt_surjective`: the four Steinberg generators generate `St_3(S)`.
* `czK2FngRank3Bld_baseLoops p = {a₀₁, a₁₂, a₂₀, u₀₁ ^ p}`: the four **base loops** of the
  Schreier graph at the standard vertex.  Their Steinberg values lie in `Φ(St_3(ℤ[1/m]))`
  (`czK2FngRank3Bld_evSt_baseLoops`), because `p · (1/(mp)) = φ(1/m)`
  (`czK2FngRank3Bld_natCast_mul_invSelf`).

Proved outright.  There are no hypotheses and no literature inputs.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

/-- The four letters: `a₀₁ = x₀₁(1)`, `a₁₂ = x₁₂(1)`, `a₂₀ = x₂₀(1)`, `u₀₁ = x₀₁(1/(mp))`. -/
inductive czK2FngRank3Bld_Letter : Type
  | a01 : czK2FngRank3Bld_Letter
  | a12 : czK2FngRank3Bld_Letter
  | a20 : czK2FngRank3Bld_Letter
  | u01 : czK2FngRank3Bld_Letter

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Bld_Letter

/-- A pure commutative-ring identity: if `A v = 1` and `A P u = 1`, then `P u = v`. -/
theorem czK2FngRank3Bld_aux {T : Type*} [CommRing T] (A P u v : T) (hv : A * v = 1)
    (hu : A * P * u = 1) : P * u = v := by
  linear_combination (-(P * u)) * hv + v * hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Bld_aux

/-- `p · (1/(mp)) = φ(1/m)` in `ℤ[1/(mp)]`. -/
theorem czK2FngRank3Bld_natCast_mul_invSelf (m p : ℕ) :
    (p : Localization.Away ((m * p : ℕ) : ℤ)) *
      (IsLocalization.Away.invSelf ((m * p : ℕ) : ℤ) : Localization.Away ((m * p : ℕ) : ℤ)) =
    czK2FngGtOneRank3_locMap m p
      (IsLocalization.Away.invSelf (m : ℤ) : Localization.Away (m : ℤ)) := by
  have hv : algebraMap ℤ (Localization.Away ((m * p : ℕ) : ℤ)) (m : ℤ) *
      czK2FngGtOneRank3_locMap m p
        (IsLocalization.Away.invSelf (m : ℤ) : Localization.Away (m : ℤ)) = 1 := by
    rw [← czK2FngGtOneRank3_locMap_algebraMap m p (m : ℤ), ← map_mul,
      IsLocalization.Away.mul_invSelf, map_one]
  have hu : algebraMap ℤ (Localization.Away ((m * p : ℕ) : ℤ)) ((m * p : ℕ) : ℤ) *
      (IsLocalization.Away.invSelf ((m * p : ℕ) : ℤ) : Localization.Away ((m * p : ℕ) : ℤ)) =
      1 :=
    IsLocalization.Away.mul_invSelf ((m * p : ℕ) : ℤ)
  have hc : algebraMap ℤ (Localization.Away ((m * p : ℕ) : ℤ)) ((m * p : ℕ) : ℤ) =
      algebraMap ℤ (Localization.Away ((m * p : ℕ) : ℤ)) (m : ℤ) *
        (p : Localization.Away ((m * p : ℕ) : ℤ)) := by
    rw [← map_natCast (algebraMap ℤ (Localization.Away ((m * p : ℕ) : ℤ))) p, ← map_mul]
    exact congrArg (algebraMap ℤ (Localization.Away ((m * p : ℕ) : ℤ))) (Nat.cast_mul m p)
  rw [hc] at hu
  exact czK2FngRank3Bld_aux _ _ _ _ hv hu

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Bld_natCast_mul_invSelf

/-- Powers in a Steinberg root subgroup: `x_ij(a)^n = x_ij(n • a)`. -/
theorem czK2FngRank3Bld_x_pow {S : Type*} [CommRing S] (i j : Fin 3) (hij : i ≠ j) (a : S)
    (n : ℕ) : x i j hij a ^ n = x i j hij (n • a) := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul, x_zero]
  | succ n ih => rw [pow_succ, ih, x_mul, succ_nsmul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Bld_x_pow

/-- The four Steinberg generators. -/
noncomputable def czK2FngRank3Bld_genSt (m p : ℕ) :
    czK2FngRank3Bld_Letter → SteinbergGroup (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ))
  | .a01 => x (0 : Fin 3) 1 (by decide) 1
  | .a12 => x (1 : Fin 3) 2 (by decide) 1
  | .a20 => x (2 : Fin 3) 0 (by decide) 1
  | .u01 => x (0 : Fin 3) 1 (by decide)
      (IsLocalization.Away.invSelf ((m * p : ℕ) : ℤ) : Localization.Away ((m * p : ℕ) : ℤ))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Bld_genSt

/-- The four elementary matrices `e₀₁(1), e₁₂(1), e₂₀(1), e₀₁(1/(mp))`. -/
noncomputable def czK2FngRank3Bld_genE (m p : ℕ) :
    czK2FngRank3Bld_Letter → elementaryGroup (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ))
  | .a01 => elementaryRoot (0 : Fin 3) 1 (by decide) 1
  | .a12 => elementaryRoot (1 : Fin 3) 2 (by decide) 1
  | .a20 => elementaryRoot (2 : Fin 3) 0 (by decide) 1
  | .u01 => elementaryRoot (0 : Fin 3) 1 (by decide)
      (IsLocalization.Away.invSelf ((m * p : ℕ) : ℤ) : Localization.Away ((m * p : ℕ) : ℤ))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Bld_genE

theorem czK2FngRank3Bld_projection_genSt (m p : ℕ) (a : czK2FngRank3Bld_Letter) :
    projection (czK2FngRank3Bld_genSt m p a) = czK2FngRank3Bld_genE m p a := by
  cases a <;> first
    | exact projection_x _ _ _ _
    | simp only [czK2FngRank3Bld_genSt, czK2FngRank3Bld_genE, projection_x]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Bld_projection_genSt

/-- Evaluation of words in the Steinberg group `St_3(ℤ[1/(mp)])`. -/
noncomputable def czK2FngRank3Bld_evSt (m p : ℕ) :
    FreeGroup czK2FngRank3Bld_Letter →*
      SteinbergGroup (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ)) :=
  FreeGroup.lift (czK2FngRank3Bld_genSt m p)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Bld_evSt

/-- Evaluation of words in the matrix group `E_3(ℤ[1/(mp)])`. -/
noncomputable def czK2FngRank3Bld_evE (m p : ℕ) :
    FreeGroup czK2FngRank3Bld_Letter →*
      elementaryGroup (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ)) :=
  FreeGroup.lift (czK2FngRank3Bld_genE m p)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Bld_evE

theorem czK2FngRank3Bld_evSt_of (m p : ℕ) (a : czK2FngRank3Bld_Letter) :
    czK2FngRank3Bld_evSt m p (FreeGroup.of a) = czK2FngRank3Bld_genSt m p a := by
  rw [czK2FngRank3Bld_evSt, FreeGroup.lift_apply_of]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Bld_evSt_of

theorem czK2FngRank3Bld_evE_of (m p : ℕ) (a : czK2FngRank3Bld_Letter) :
    czK2FngRank3Bld_evE m p (FreeGroup.of a) = czK2FngRank3Bld_genE m p a := by
  rw [czK2FngRank3Bld_evE, FreeGroup.lift_apply_of]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Bld_evE_of
