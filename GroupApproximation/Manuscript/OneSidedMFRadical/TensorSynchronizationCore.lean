import GroupApproximation.GroupTheory.FiniteHNNFreeLabelAction

/-!
# The finite-group core of tensor synchronization

The tensor-synchronization argument in the manuscript uses two elementary
finite-group facts.  First, two homomorphisms with the same kernel have
canonically isomorphic images.  Second, after those images are regarded as
subgroups of one finite group, the two restrictions of the left regular
action are conjugate by a permutation of the ambient group.

The second assertion is stronger than a character calculation: the
conjugating permutation is obtained from right-coset transversals.  It is the
same explicit transversal construction used by the finite-base HNN action.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TensorSynchronizationCore

noncomputable section

universe u v

variable {S : Type u} {E : Type v} [Group S] [Group E]

/-- Homomorphisms with the same kernel have canonically isomorphic images. -/
def rangeMulEquivOfKerEq (f g : S →* E) (hker : f.ker = g.ker) :
    f.range ≃* g.range :=
  (QuotientGroup.quotientKerEquivRange f).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivRange g))

/-- The image isomorphism sends the image of `s` under the first homomorphism
to its image under the second homomorphism. -/
@[simp] theorem rangeMulEquivOfKerEq_rangeRestrict
    (f g : S →* E) (hker : f.ker = g.ker) (s : S) :
    rangeMulEquivOfKerEq f g hker (f.rangeRestrict s) = g.rangeRestrict s := by
  have hpre :
      (QuotientGroup.quotientKerEquivRange f).symm (f.rangeRestrict s) =
        QuotientGroup.mk s := by
    apply (QuotientGroup.quotientKerEquivRange f).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  change (QuotientGroup.quotientKerEquivRange g)
      (QuotientGroup.quotientMulEquivOfEq hker
        ((QuotientGroup.quotientKerEquivRange f).symm (f.rangeRestrict s))) =
    g.rangeRestrict s
  rw [hpre, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- **Finite left-regular synchronization.**  If two homomorphisms into the
same finite group have equal kernels, a permutation of the finite group
conjugates their left-regular actions pointwise.

This is the exact finite-dimensional algebraic core used to choose the
permutation unitaries `W_n` in the manuscript's tensor-synchronization lemma.
-/
theorem exists_leftRegular_conjugator_of_ker_eq [Fintype E]
    (f g : S →* E) (hker : f.ker = g.ker) :
    ∃ W : Equiv.Perm E, ∀ s : S,
      W * Equiv.mulLeft (f s) * W⁻¹ = Equiv.mulLeft (g s) := by
  let φ : f.range ≃* g.range := rangeMulEquivOfKerEq f g hker
  obtain ⟨d⟩ :=
    HNNExtension.NormalWord.TransversalPair.nonempty E f.range g.range
  let W : Equiv.Perm E :=
    FiniteHNNFreeLabelAction.baseIntertwiner φ d
  refine ⟨W, ?_⟩
  intro s
  apply Equiv.ext
  intro x
  have hintertwine :=
    FiniteHNNFreeLabelAction.baseIntertwiner_mul_left φ d
      (f.rangeRestrict s) (W⁻¹ x)
  have hcancel : W (W⁻¹ x) = x := by
    change W (W.symm x) = x
    exact W.apply_symm_apply x
  change W (f s * W⁻¹ x) = g s * x
  calc
    W (f s * W⁻¹ x) =
        ((φ (f.rangeRestrict s) : g.range) : E) * W (W⁻¹ x) := by
      simpa [W] using hintertwine
    _ = g s * x := by
      rw [hcancel, rangeMulEquivOfKerEq_rangeRestrict]
      change g s * x = g s * x
      rfl

/-- Pointwise intertwining form of finite left-regular synchronization.  This
is equivalent to the conjugation identity but is often the more convenient
form when constructing the associated permutation matrix. -/
theorem exists_leftRegular_intertwiner_of_ker_eq [Fintype E]
    (f g : S →* E) (hker : f.ker = g.ker) :
    ∃ W : Equiv.Perm E, ∀ (s : S) (x : E),
      W (f s * x) = g s * W x := by
  obtain ⟨W, hW⟩ := exists_leftRegular_conjugator_of_ker_eq f g hker
  refine ⟨W, ?_⟩
  intro s x
  have h := DFunLike.congr_fun (hW s) (W x)
  simpa [Equiv.Perm.mul_apply] using h

end

end TensorSynchronizationCore
end OneSidedMFRadical
end Manuscript
end GroupApproximation
