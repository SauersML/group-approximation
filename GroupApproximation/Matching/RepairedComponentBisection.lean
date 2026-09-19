import GroupApproximation.Matching.AsymptoticBlockArrow
import GroupApproximation.Matching.ComponentInvolutionRepair
import GroupApproximation.Matching.FiniteGroupoidBisection

/-!
# The component bisection of a centralizing involution

On reciprocal components use the actual overlap partial bijection.  On the
nonreciprocal locus, where the repaired object permutation is the identity,
use the full identity arrow.  Thus every component sequence obtains an
asymptotic arrow, while the exceptional vertex mass is already controlled by
the nonreciprocity estimate.
-/

namespace GroupApproximation
namespace ExpanderDecomposition

variable {G : Type} [Group G] {S : SoficApproximation G} {T : Finset G}
variable (D : ExpanderDecomposition S T)

/-- The finite partial arrow covering the repaired component involution. -/
noncomputable def repairedComponentArrow
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n) :
    FinitePartialBijection
      (indexedBlockModel (D.blocks n) C)
      (indexedBlockModel (D.blocks n) (D.repairedComponentInvolution q C)) :=
  if hC : D.refineIndex q (D.refineIndex q C) = C then
    FinitePartialBijection.castTarget
      (congrArg (indexedBlockModel (D.blocks n))
        (D.repairedComponentInvolution_eq_refineIndex_of_reciprocal q C hC).symm)
      (D.refinementPartialBijection q C)
  else
    FinitePartialBijection.castTarget
      (congrArg (indexedBlockModel (D.blocks n))
        (D.repairedComponentInvolution_eq_self_of_nonreciprocal q C hC).symm)
      (FinitePartialBijection.refl _)

/-- The repaired arrow's source defect is bounded by forward leakage. -/
theorem repairedComponentArrow_sourceDefect_le
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n) :
    (D.repairedComponentArrow q C).sourceDefect ≤
      D.componentLeakage (D.blocks n) q C := by
  classical
  by_cases hC : D.refineIndex q (D.refineIndex q C) = C
  · simp only [repairedComponentArrow, dif_pos hC,
      FinitePartialBijection.castTarget_sourceDefect]
    exact le_of_eq (D.refinementPartialBijection_sourceDefect q C)
  · simp only [repairedComponentArrow, dif_neg hC,
      FinitePartialBijection.castTarget_sourceDefect]
    simp [FinitePartialBijection.sourceDefect, FinitePartialBijection.refl,
      indexedBlockModel]

/-- For an exact model involution, the repaired arrow's target defect is
bounded by leakage at its repaired target. -/
theorem repairedComponentArrow_targetDefect_le
    (q : Equiv.Perm (S.model n)) (hsq : q * q = 1)
    (C : D.componentIndex n) :
    (D.repairedComponentArrow q C).targetDefect ≤
      D.componentLeakage (D.blocks n) q (D.repairedComponentInvolution q C) := by
  classical
  by_cases hC : D.refineIndex q (D.refineIndex q C) = C
  · simp only [repairedComponentArrow, dif_pos hC,
      FinitePartialBijection.castTarget_targetDefect,
      D.repairedComponentInvolution_eq_refineIndex_of_reciprocal q C hC]
    exact le_of_eq
      (D.refinementPartialBijection_targetDefect_of_involution q hsq C hC)
  · simp only [repairedComponentArrow, dif_neg hC,
      FinitePartialBijection.castTarget_targetDefect,
      D.repairedComponentInvolution_eq_self_of_nonreciprocal q C hC]
    simp [FinitePartialBijection.targetDefect, FinitePartialBijection.refl,
      indexedBlockModel]

/-- Pointwise repaired action on component sequences. -/
noncomputable def repairedComponentSequenceEquiv
    (q : ∀ n, Equiv.Perm (S.model n)) :
    D.ComponentSequence ≃ D.ComponentSequence where
  toFun C n := D.repairedComponentInvolution (q n) (C n)
  invFun C n := D.repairedComponentInvolution (q n) (C n)
  left_inv C := by
    funext n
    have h := D.repairedComponentInvolution_mul_self (q n)
    exact DFunLike.congr_fun h (C n)
  right_inv C := by
    funext n
    have h := D.repairedComponentInvolution_mul_self (q n)
    exact DFunLike.congr_fun h (C n)

/-- Every component sequence carries an asymptotic arrow to its image under
the repaired involution. -/
noncomputable def repairedComponentAsymptoticArrow
    (q : ∀ n, Equiv.Perm (S.model n)) (hsq : ∀ n, q n * q n = 1)
    (hLeak : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n,
        (D.componentLeakage (D.blocks n) (q n) C : ℝ)))
    (C : D.ComponentSequence) :
    AsymptoticPartialBijection
      (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (D.componentSequenceModel C)
      (D.componentSequenceModel (D.repairedComponentSequenceEquiv q C)) where
  map n := D.repairedComponentArrow (q n) (C n)
  source_negligible := by
    apply Negligible.mono_nonneg (fun _ ↦ by positivity)
      (fun _ ↦ by positivity) (fun n ↦ ?_) hLeak
    change ((D.repairedComponentArrow (q n) (C n)).sourceDefect : ℝ) ≤ _
    calc
      ((D.repairedComponentArrow (q n) (C n)).sourceDefect : ℝ) ≤
          D.componentLeakage (D.blocks n) (q n) (C n) := by
        exact_mod_cast D.repairedComponentArrow_sourceDefect_le (q n) (C n)
      _ ≤ ∑ E : D.componentIndex n,
          (D.componentLeakage (D.blocks n) (q n) E : ℝ) :=
        Finset.single_le_sum
          (fun E _ ↦ by positivity : ∀ E : D.componentIndex n,
            E ∈ Finset.univ →
              0 ≤ (D.componentLeakage (D.blocks n) (q n) E : ℝ))
          (Finset.mem_univ _)
  target_negligible := by
    apply Negligible.mono_nonneg (fun _ ↦ by positivity)
      (fun _ ↦ by positivity) (fun n ↦ ?_) hLeak
    change ((D.repairedComponentArrow (q n) (C n)).targetDefect : ℝ) ≤ _
    calc
      ((D.repairedComponentArrow (q n) (C n)).targetDefect : ℝ) ≤
          D.componentLeakage (D.blocks n) (q n)
            (D.repairedComponentInvolution (q n) (C n)) := by
        exact_mod_cast D.repairedComponentArrow_targetDefect_le
          (q n) (hsq n) (C n)
      _ ≤ ∑ E : D.componentIndex n,
          (D.componentLeakage (D.blocks n) (q n) E : ℝ) :=
        Finset.single_le_sum
          (fun E _ ↦ by positivity : ∀ E : D.componentIndex n,
            E ∈ Finset.univ →
              0 ≤ (D.componentLeakage (D.blocks n) (q n) E : ℝ))
          (Finset.mem_univ _)

/-- The repaired action on component sequences, bundled at the object level
of the asymptotic partial-bijection groupoid. -/
noncomputable def repairedComponentObjectEquiv
    (q : ∀ n, Equiv.Perm (S.model n)) :
    (asymptoticPartialGroupoidPresentation D.ComponentSequence
      (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun _ ↦ by positivity) D.componentSequenceModel).Obj ≃
    (asymptoticPartialGroupoidPresentation D.ComponentSequence
      (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun _ ↦ by positivity) D.componentSequenceModel).Obj where
  toFun X := ⟨D.repairedComponentSequenceEquiv q X.val⟩
  invFun X := ⟨(D.repairedComponentSequenceEquiv q).symm X.val⟩
  left_inv X := by cases X; simp
  right_inv X := by cases X; simp

/-- The repaired component action and its overlap arrows form a bisection of
the asymptotic partial-bijection groupoid presentation. -/
noncomputable def repairedComponentBisection
    (q : ∀ n, Equiv.Perm (S.model n)) (hsq : ∀ n, q n * q n = 1)
    (hLeak : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n,
        (D.componentLeakage (D.blocks n) (q n) C : ℝ))) :
    FiniteGroupoid.Bisection
      (asymptoticPartialGroupoidPresentation D.ComponentSequence
        (fun n ↦ (Fintype.card (S.model n) : ℝ))
        (fun _ ↦ by positivity) D.componentSequenceModel).Obj where
  objEquiv := D.repairedComponentObjectEquiv q
  hom X := GroupoidPresentation.ofRep _
    (D.repairedComponentAsymptoticArrow q hsq hLeak X.val)

end ExpanderDecomposition
end GroupApproximation
