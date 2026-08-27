import GroupApproximation.Higman.OmegaHalfLineTargetCutter

/-!
# A global label shift for the finite one-sided Omega cutter

The right-tail labels and the labels obtained by prepending a fixed block are
both infinite and co-infinite subsets of Higman's conjugator alphabet.  The
intended insertion is a bijection between the two distinguished subsets.  We
extend that bijection arbitrarily across their complements.  Transporting a
benign witness along the resulting free-group automorphism leaves its finite
overgroup and its cutting subgroup literally unchanged; only its source
embedding changes.  This is the finite-rank replacement for an infinite edge
on all right-tail basis letters.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-- Right-tail sequences, regarded as their source conjugator labels. -/
noncomputable def rightTailIndexEquivLabel (m : ℕ) :
    RightTailIndex m ≃ ↥(rightTailLabel m) := by
  apply Equiv.ofBijective
    (fun l : RightTailIndex m ↦
      ⟨rightTailIndexToK m l, ⟨(l : E), l.property, rfl⟩⟩)
  constructor
  · intro l r hlr
    apply rightTailIndexToK_injective m
    exact congrArg Subtype.val hlr
  · intro q
    obtain ⟨l, hl, hlq⟩ := q.property
    refine ⟨⟨l, hl⟩, Subtype.ext ?_⟩
    exact hlq

/-- Right-tail sequences, regarded as their inserted target labels. -/
noncomputable def rightTailIndexEquivInsertedLabel (m : ℕ) (beta : E) :
    RightTailIndex m ≃ ↥(insertedRightTailLabel m beta) := by
  apply Equiv.ofBijective
    (fun l : RightTailIndex m ↦
      ⟨insertedRightTailIndexToK m beta l,
        ⟨beta + (l : E), ⟨(l : E), l.property, rfl⟩, rfl⟩⟩)
  constructor
  · intro l r hlr
    apply insertedRightTailIndexToK_injective m beta
    exact congrArg Subtype.val hlr
  · intro q
    obtain ⟨x, ⟨l, hl, rfl⟩, hxq⟩ := q.property
    refine ⟨⟨l, hl⟩, Subtype.ext ?_⟩
    exact hxq

/-- An arbitrary bijection between the two complementary label sets. -/
noncomputable def outsideRightTailLabelEquiv
    (m : ℕ) (beta : E) :
    ↥((rightTailLabel m)ᶜ : Set ↥Conj.K) ≃
      ↥((insertedRightTailLabel m beta)ᶜ : Set ↥Conj.K) := by
  letI : Denumerable ↥((rightTailLabel m)ᶜ : Set ↥Conj.K) :=
    outsideRightTailLabelDenumerable m
  letI : Denumerable
      ↥((insertedRightTailLabel m beta)ᶜ : Set ↥Conj.K) :=
    outsideInsertedRightTailLabelDenumerable m beta
  exact (Denumerable.eqv _).trans (Denumerable.eqv _).symm

/-- A permutation of the whole conjugator alphabet extending the intended
right insertion on every right-tail label. -/
noncomputable def rightTailLabelShiftEquiv (m : ℕ) (beta : E) :
    ↥Conj.K ≃ ↥Conj.K := by
  classical
  exact (Equiv.Set.sumCompl (rightTailLabel m)).symm |>.trans
      ((rightTailIndexEquivLabel m).symm.trans
          (rightTailIndexEquivInsertedLabel m beta) |>.sumCongr
        (outsideRightTailLabelEquiv m beta)) |>.trans
      (Equiv.Set.sumCompl (insertedRightTailLabel m beta))

/-- On the distinguished right-tail basis, the global permutation is exactly
the requested insertion `l ↦ beta + l`. -/
@[simp] theorem rightTailLabelShiftEquiv_apply
    (m : ℕ) (beta : E) (l : RightTailIndex m) :
    rightTailLabelShiftEquiv m beta (rightTailIndexToK m l) =
      insertedRightTailIndexToK m beta l := by
  classical
  have hs : rightTailIndexToK m l ∈ rightTailLabel m :=
    ⟨(l : E), l.property, rfl⟩
  have hsource :
      rightTailIndexEquivLabel m l =
        ⟨rightTailIndexToK m l, hs⟩ := rfl
  rw [rightTailLabelShiftEquiv]
  simp only [Equiv.trans_apply]
  rw [Equiv.Set.sumCompl_symm_apply_of_mem hs]
  simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.trans_apply,
    Equiv.Set.sumCompl_apply_inl]
  rw [← hsource, Equiv.symm_apply_apply]
  rfl

/-- The induced automorphism of the free conjugator group. -/
noncomputable def rightTailFreeShiftEquiv (m : ℕ) (beta : E) :
    FreeGroup ↥Conj.K ≃* FreeGroup ↥Conj.K :=
  FreeGroup.freeGroupCongr (rightTailLabelShiftEquiv m beta)

@[simp] theorem rightTailFreeShiftEquiv_of
    (m : ℕ) (beta : E) (l : RightTailIndex m) :
    rightTailFreeShiftEquiv m beta
        (FreeGroup.of (rightTailIndexToK m l)) =
      FreeGroup.of (insertedRightTailIndexToK m beta l) := by
  rw [rightTailFreeShiftEquiv]
  change FreeGroup.of
      (rightTailLabelShiftEquiv m beta (rightTailIndexToK m l)) = _
  rw [rightTailLabelShiftEquiv_apply]

end Omega
end Higman
end GroupApproximation
