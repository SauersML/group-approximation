import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionExtInverseComplement
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.StdOperatorAlgebraNorm
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ChoiEffrosCPBasics
import GroupApproximation.Analysis.CStarCompletelyPositiveStar
import GroupApproximation.Analysis.CStarPositiveOrder
import GroupApproximation.Analysis.CStarFiniteRank

/-!
# From a completely positive map into `𝓛(H_J)` to a pointwise cpc map

Lane `TWWSch-Inv1`, work order `WO-Inv-1`. Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership`, through the Busby picture of `Ext(S, J)` in Schafhauser's proof
of the Tikuisis--White--Winter theorem.

The Choi--Effros lift (Choi--Effros, Ann. of Math. (2) **104** (1976), Thm. 3.10; Brown--Ozawa,
Thm. C.3) produces a completely positive contraction `ψ : S →ₗ[ℂ] StdBdd J` in the matrix sense.
The Kasparov--Stinespring dilation (Arveson, Duke Math. J. **44** (1977), §4) consumes the
pointwise form `IsCPCOp`. This file converts one into the other:

* `map_star_of_isCompletelyPositive`: a completely positive map between unital C⋆-algebras is
  `⋆`-preserving (the `B(H)`-valued case is `CStarExactness.IsCompletelyPositive.map_star`);
* `isPositiveElem_sum_inner_of_eq_sum_star_mul`: if `T i j = ∑ₖ P(k,i)⋆ P(k,j)` then
  `∑ᵢⱼ ⟨ξᵢ, T i j ξⱼ⟩ = ∑ₖ ⟨ηₖ, ηₖ⟩ ≥ 0` with `ηₖ = ∑ⱼ P(k,j) ξⱼ`;
* **`isCPCOp_of_linearMap`**.
-/

noncomputable section

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

section Star

variable {A : Type} {B : Type} [CStarAlgebra A] [CStarAlgebra B]

/-- **Completely positive maps preserve selfadjointness** (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`): polarize `h` into elements `x⋆x`, each sent to some `p⋆p`. -/
theorem isSelfAdjoint_map_of_isCompletelyPositive {L : A →ₗ[ℂ] B}
    (hL : CStarExactness.IsCompletelyPositive L) {h : A} (hh : IsSelfAdjoint h) :
    IsSelfAdjoint (L h) := by
  have hsa : ∀ x : A, IsSelfAdjoint (L (star x * x)) := fun x => by
    obtain ⟨p, hp⟩ := exists_map_star_mul_self_eq hL x
    rw [hp]
    exact IsSelfAdjoint.star_mul_self p
  rw [CStarExactness.selfadjoint_eq_smul_sub_star_mul_self hh, map_sub, map_smul, map_smul]
  have hreal : ((4 : ℂ)⁻¹) = star ((4 : ℂ)⁻¹) := by
    rw [Complex.star_def, map_inv₀, map_ofNat]
  refine IsSelfAdjoint.sub ?_ ?_
  · rw [IsSelfAdjoint, star_smul, ← hreal, (hsa (h + 1)).star_eq]
  · rw [IsSelfAdjoint, star_smul, ← hreal, (hsa (h - 1)).star_eq]

/-- **Completely positive maps are `⋆`-preserving** (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`): split `x` into real and imaginary parts. -/
theorem map_star_of_isCompletelyPositive {L : A →ₗ[ℂ] B}
    (hL : CStarExactness.IsCompletelyPositive L) (x : A) :
    L (star x) = star (L x) := by
  set hre : A := ((2 : ℂ)⁻¹) • (x + star x) with hre_def
  set him : A := (((2 : ℂ) * Complex.I)⁻¹) • (x - star x) with him_def
  have hre_sa : IsSelfAdjoint hre := by
    rw [hre_def, IsSelfAdjoint, star_smul, star_add, star_star,
      Complex.star_def]
    rw [show (starRingEnd ℂ) ((2 : ℂ)⁻¹) = ((2 : ℂ)⁻¹) by
      rw [map_inv₀, map_ofNat]]
    rw [add_comm]
  have him_sa : IsSelfAdjoint him := by
    rw [him_def, IsSelfAdjoint, star_smul, star_sub, star_star,
      Complex.star_def]
    rw [show (starRingEnd ℂ) (((2 : ℂ) * Complex.I)⁻¹)
        = -(((2 : ℂ) * Complex.I)⁻¹) by
      rw [map_inv₀, map_mul, Complex.conj_I]
      rw [show (starRingEnd ℂ) (2 : ℂ) = 2 from map_ofNat _ 2]
      rw [show (2 : ℂ) * -Complex.I = -(2 * Complex.I) by ring]
      rw [inv_neg]]
    rw [neg_smul, ← smul_neg, neg_sub]
  have hx : x = hre + Complex.I • him := by
    rw [hre_def, him_def, smul_smul]
    have hI : Complex.I * ((2 : ℂ) * Complex.I)⁻¹ = -((2 : ℂ))⁻¹ * (-1) := by
      rw [mul_inv, ← mul_assoc]
      rw [show Complex.I * ((2:ℂ))⁻¹ * (Complex.I)⁻¹
          = ((2:ℂ))⁻¹ * (Complex.I * (Complex.I)⁻¹) by ring]
      rw [mul_inv_cancel₀ Complex.I_ne_zero, mul_one]
      ring
    rw [hI]
    rw [show (-((2:ℂ))⁻¹ * (-1)) = ((2:ℂ))⁻¹ by ring]
    rw [← smul_add]
    rw [show x + star x + (x - star x) = x + x by abel]
    rw [show ((2 : ℂ))⁻¹ • (x + x) = ((2 : ℂ))⁻¹ • (((2 : ℂ)) • x) by
      rw [show ((2 : ℂ)) • x = x + x by
        rw [show ((2:ℂ)) = 1 + 1 by norm_num, add_smul, one_smul]]]
    rw [smul_smul]
    norm_num
  have hstar : star x = hre - Complex.I • him := by
    rw [hx, star_add, hre_sa.star_eq, star_smul, him_sa.star_eq,
      Complex.star_def, Complex.conj_I, neg_smul, ← sub_eq_add_neg]
  rw [hstar, hx, map_sub, map_add, star_add,
    (isSelfAdjoint_map_of_isCompletelyPositive hL hre_sa).star_eq,
    map_smul, map_smul, star_smul, Complex.star_def, Complex.conj_I,
    (isSelfAdjoint_map_of_isCompletelyPositive hL him_sa).star_eq, neg_smul,
    ← sub_eq_add_neg]

end Star

section Form

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- Evaluation of bounded operators at a vector, as an additive map (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
def stdBddEval (ξ : (standardModule ℕ J).carrier) :
    StdBdd J →+ (standardModule ℕ J).carrier where
  toFun T := T.1.toFun ξ
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A finite sum of operators, evaluated at a vector (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem StdBdd.sum_toFun {ι : Type} (s : Finset ι) (f : ι → StdBdd J)
    (ξ : (standardModule ℕ J).carrier) :
    (∑ k ∈ s, f k).1.toFun ξ = ∑ k ∈ s, (f k).1.toFun ξ :=
  map_sum (stdBddEval ξ) f s

/-- **Positivity of the form of a factored matrix** (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`; Lance, *Hilbert C⋆-modules*, Lemma 4.2): if
`T i j = ∑ₖ P(k,i)⋆ P(k,j)` then `∑ᵢⱼ ⟨ξᵢ, T i j ξⱼ⟩ = ∑ₖ ⟨ηₖ, ηₖ⟩` is positive. -/
theorem isPositiveElem_sum_inner_of_eq_sum_star_mul {n : ℕ} (T P : Fin n → Fin n → StdBdd J)
    (hP : ∀ i j, T i j = ∑ k, star (P k i) * P k j)
    (ξ : Fin n → (standardModule ℕ J).carrier) :
    OrderZero.IsPositiveElem
      (∑ i, ∑ j, (standardModule ℕ J).inner (ξ i) ((T i j).1.toFun (ξ j))) := by
  have hterm : ∀ i j, (standardModule ℕ J).inner (ξ i) ((T i j).1.toFun (ξ j)) =
      ∑ k, (standardModule ℕ J).inner ((P k i).1.toFun (ξ i)) ((P k j).1.toFun (ξ j)) := by
    intro i j
    rw [hP i j, StdBdd.sum_toFun, CStarModule.inner_sum_right]
    exact Finset.sum_congr rfl fun k _ =>
      ((P k i).1.inner_adj (ξ i) ((P k j).1.toFun (ξ j))).symm
  have hsum : (∑ i, ∑ j, (standardModule ℕ J).inner (ξ i) ((T i j).1.toFun (ξ j))) =
      ∑ k, (standardModule ℕ J).inner (∑ i, (P k i).1.toFun (ξ i))
        (∑ j, (P k j).1.toFun (ξ j)) := by
    calc (∑ i, ∑ j, (standardModule ℕ J).inner (ξ i) ((T i j).1.toFun (ξ j)))
        = ∑ i, ∑ j, ∑ k,
            (standardModule ℕ J).inner ((P k i).1.toFun (ξ i)) ((P k j).1.toFun (ξ j)) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
      _ = ∑ i, ∑ k, ∑ j,
            (standardModule ℕ J).inner ((P k i).1.toFun (ξ i)) ((P k j).1.toFun (ξ j)) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j,
            (standardModule ℕ J).inner ((P k i).1.toFun (ξ i)) ((P k j).1.toFun (ξ j)) :=
          Finset.sum_comm
      _ = ∑ k, (standardModule ℕ J).inner (∑ i, (P k i).1.toFun (ξ i))
            (∑ j, (P k j).1.toFun (ξ j)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [CStarModule.inner_sum_left]
          exact Finset.sum_congr rfl fun i _ =>
            (CStarModule.inner_sum_right (standardModule ℕ J) Finset.univ
              ((P k i).1.toFun (ξ i)) fun j => (P k j).1.toFun (ξ j)).symm
  rw [hsum]
  exact OrderZero.isPositiveElem_of_nonneg (Finset.sum_nonneg fun k _ =>
    ((standardModule ℕ J).inner_self_isPositive (∑ i, (P k i).1.toFun (ξ i))).nonneg)

end Form

section CPC

variable {S : Type} [CStarAlgebra S]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **A completely positive contraction into the bounded operators is a pointwise cpc map**
(`non_mf_group_notes.tex`, `thm:fixed-radical-membership`): the matrix factorization of
`[ψ(aᵢ⋆aⱼ)]` gives positivity of the form `∑ᵢⱼ ⟨ξᵢ, ψ(aᵢ⋆aⱼ) ξⱼ⟩`. -/
theorem isCPCOp_of_linearMap (ψ : S →ₗ[ℂ] StdBdd J)
    (hstar : ∀ a, ψ (star a) = star (ψ a))
    (hpos : ∀ (n : ℕ) (a : Fin n → S), ∃ P : Fin n → Fin n → StdBdd J,
      ∀ i j, ψ (star (a i) * a j) = ∑ k, star (P k i) * P k j)
    (hone : ‖ψ 1‖ ≤ 1) : IsCPCOp (fun a => (ψ a).1) where
  bounded a := StdBdd.isBounded (ψ a)
  map_add a a' ξ := congrArg (fun T : StdBdd J => T.1.toFun ξ) (map_add ψ a a')
  map_smul c a ξ := congrArg (fun T : StdBdd J => T.1.toFun ξ) (map_smul ψ c a)
  map_star a ξ := congrArg (fun T : StdBdd J => T.1.toFun ξ) (hstar a)
  posDef n a ξ := by
    obtain ⟨P, hP⟩ := hpos n a
    exact isPositiveElem_sum_inner_of_eq_sum_star_mul (fun i j => ψ (star (a i) * a j)) P hP ξ
  contractive := (Adjointable.isBoundedBy_opNorm (StdBdd.isBounded (ψ 1))).mono hone

end CPC

end GroupApproximation.Full.TWWSchafhauser

end
