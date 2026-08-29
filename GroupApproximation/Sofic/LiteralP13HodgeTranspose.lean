import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

/-!
# Transpose reuse for the exact P13 residual certificate

Swapping a support pair replaces its collected product by the inverse product
class. The residual matrix is self-adjoint, so the exact certificate can reuse
every upper-triangular block for its lower-triangular mate. The finite lookup
facts below are much cheaper to replay than the 15 duplicated residual
computations they replace.
-/

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

open LiteralP13HodgeData
open scoped BigOperators

noncomputable section

/-- The product class of the reversed first pair stored in class `c`.

Every class fiber is nonempty. `headD` keeps the definition total; the checked
lookup theorems below verify its value on every reachable class. -/
def inverseClass (c : Fin 293) : Fin 293 :=
  let pair := (LiteralP13HodgePairTable.classPairList c).headD (0, 0)
  LiteralP13HodgeReplay.productClassIndex pair.2 pair.1

/-- Flattened support pair used to keep the finite transpose check balanced. -/
def supportPairOfIndex (u : Fin 484) : Fin 22 × Fin 22 :=
  (finProdFinEquiv : Fin 22 × Fin 22 ≃ Fin 484).symm u

def productClassIndexSwapCheck (u : Fin 484) : Prop :=
  let pair := supportPairOfIndex u
  LiteralP13HodgeReplay.productClassIndex pair.2 pair.1 =
    inverseClass
      (LiteralP13HodgeReplay.productClassIndex pair.1 pair.2)

mk_kernel_batched_theorem 484 productClassIndexSwapCheck

theorem productClassIndex_swap_all :
    ∀ u : Fin 484, productClassIndexSwapCheck u :=
  combine_kernel_batched_theorems% productClassIndexSwapCheck 484

/-- Reversing a support pair applies `inverseClass` to its product class. -/
theorem productClassIndex_swap (left right : Fin 22) :
    LiteralP13HodgeReplay.productClassIndex right left =
      inverseClass
        (LiteralP13HodgeReplay.productClassIndex left right) := by
  simpa [productClassIndexSwapCheck, supportPairOfIndex] using
    productClassIndex_swap_all (finProdFinEquiv (left, right))

def inverseClassInvolutiveCheck (c : Fin 293) : Prop :=
  inverseClass (inverseClass c) = c

mk_kernel_batched_theorem 293 inverseClassInvolutiveCheck

theorem inverseClass_involutive_all :
    ∀ c : Fin 293, inverseClassInvolutiveCheck c :=
  combine_kernel_batched_theorems% inverseClassInvolutiveCheck 293

/-- Reversing product classes twice is the identity. -/
theorem inverseClass_involutive (c : Fin 293) :
    inverseClass (inverseClass c) = c :=
  inverseClass_involutive_all c

/-- Product-class inversion as a finite equivalence. -/
def inverseClassEquiv : Fin 293 ≃ Fin 293 where
  toFun := inverseClass
  invFun := inverseClass
  left_inv := inverseClass_involutive
  right_inv := inverseClass_involutive

/-- Swap the two entries of a support pair. -/
def supportPairSwap : (Fin 22 × Fin 22) ↪ (Fin 22 × Fin 22) :=
  (Equiv.prodComm (Fin 22) (Fin 22)).toEmbedding

/-- The fiber of an inverse product class is the swapped original fiber. -/
theorem classPairs_inverse (c : Fin 293) :
    LiteralP13HodgePairTable.classPairs (inverseClass c) =
      (LiteralP13HodgePairTable.classPairs c).map supportPairSwap := by
  ext pair
  constructor
  · intro hpair
    have hclass := LiteralP13HodgePairTable.classPairs_sound
      (inverseClass c) pair hpair
    have hswap :
        LiteralP13HodgeReplay.productClassIndex pair.2 pair.1 = c := by
      calc
        LiteralP13HodgeReplay.productClassIndex pair.2 pair.1 =
            inverseClass
              (LiteralP13HodgeReplay.productClassIndex pair.1 pair.2) :=
          productClassIndex_swap pair.1 pair.2
        _ = inverseClass (inverseClass c) := by rw [hclass]
        _ = c := inverseClass_involutive c
    refine Finset.mem_map.mpr ⟨(pair.2, pair.1), ?_, ?_⟩
    · simpa [hswap] using
        LiteralP13HodgePairTable.classPairs_complete pair.2 pair.1
    · rfl
  · intro hpair
    obtain ⟨source, hsource, hsource_pair⟩ := Finset.mem_map.mp hpair
    have hclass := LiteralP13HodgePairTable.classPairs_sound c source hsource
    have hswap :
        LiteralP13HodgeReplay.productClassIndex source.2 source.1 =
          inverseClass c := by
      rw [productClassIndex_swap, hclass]
    have hmem : (source.2, source.1) ∈
        LiteralP13HodgePairTable.classPairs (inverseClass c) := by
      simpa [hswap] using
        LiteralP13HodgePairTable.classPairs_complete source.2 source.1
    change supportPairSwap source ∈
      LiteralP13HodgePairTable.classPairs (inverseClass c) at hmem
    exact hsource_pair ▸ hmem

theorem gramPairNumerator_swap (i k : Fin 6) (pair : Fin 22 × Fin 22) :
    gramPairNumerator k i (pair.2, pair.1) =
      gramPairNumerator i k pair := by
  unfold gramPairNumerator
  apply congrArg₂ (fun a b : ℤ ↦ a + b)
  · apply Finset.sum_congr rfl
    intro block _
    apply Finset.sum_congr rfl
    intro offset _
    rw [mul_comm]
  · apply Finset.sum_congr rfl
    intro offset _
    rw [mul_comm]

theorem gramNumerator_inverse (i k : Fin 6) (c : Fin 293) :
    gramNumerator k i (inverseClass c) = gramNumerator i k c := by
  unfold gramNumerator
  rw [classPairs_inverse, Finset.sum_map]
  exact Finset.sum_congr rfl fun pair _ ↦ gramPairNumerator_swap i k pair

theorem hodgeNumerator_inverse (i k : Fin 6) (c : Fin 293) :
    hodgeNumerator k i (inverseClass c) = hodgeNumerator i k c := by
  unfold hodgeNumerator
  rw [classPairs_inverse, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro pair _
  apply congrArg₂ (fun a b : ℤ ↦ a + b)
  · apply Finset.sum_congr rfl
    intro relator _
    change LiteralP13HodgeReplay.boundaryNumerator relator k pair.2 *
        LiteralP13HodgeReplay.boundaryNumerator relator i pair.1 =
      LiteralP13HodgeReplay.boundaryNumerator relator i pair.1 *
        LiteralP13HodgeReplay.boundaryNumerator relator k pair.2
    rw [mul_comm]
  · change LiteralP13HodgeData.adjointCoboundaryNumerator k pair.2 *
        LiteralP13HodgeData.adjointCoboundaryNumerator i pair.1 =
      LiteralP13HodgeData.adjointCoboundaryNumerator i pair.1 *
        LiteralP13HodgeData.adjointCoboundaryNumerator k pair.2
    rw [mul_comm]

/-- Off-diagonal residual coefficients are transposes under class inversion. -/
theorem residualNumerator_inverse_of_ne (i k : Fin 6) (c : Fin 293)
    (hik : i ≠ k) :
    residualNumerator k i (inverseClass c) = residualNumerator i k c := by
  unfold residualNumerator
  rw [hodgeNumerator_inverse, gramNumerator_inverse]
  simp [hik, Ne.symm hik]

/-- The coefficient-`ℓ1` total of an off-diagonal block equals that of its
transpose, so only one triangular half needs direct kernel computation. -/
theorem sum_residual_natAbs_transpose_of_ne (i k : Fin 6) (hik : i ≠ k) :
    (∑ c : Fin 293, (residualNumerator k i c).natAbs) =
      ∑ c : Fin 293, (residualNumerator i k c).natAbs := by
  symm
  exact Fintype.sum_equiv inverseClassEquiv
    (fun c : Fin 293 ↦ (residualNumerator i k c).natAbs)
    (fun c : Fin 293 ↦ (residualNumerator k i c).natAbs)
    (fun c ↦ congrArg Int.natAbs
      (residualNumerator_inverse_of_ne i k c hik).symm)

end

end LiteralP13HodgeCertificate
end GroupApproximation
