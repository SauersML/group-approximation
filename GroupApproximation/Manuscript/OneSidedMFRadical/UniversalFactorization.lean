import GroupApproximation.Sofic.MFCamouflage

/-!
# Universal factorization for prescribed quotients

This module is the exact manuscript-facing endpoint for
`non_mf_groups_exist.tex`, Proposition `prop:universal-factorization`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

/-- **Proposition `prop:universal-factorization`.** For the amalgam
`W_Q = B *_{⟨d⟩} (Q × ⟨d⟩)`, every map to a target that cannot see `B`
factors uniquely through the split projection to `Q`. If `d` normally
generates `B`, the kernel of that projection is the normal closure of `d` in
the amalgam. -/
def UniversalFactorization : Prop :=
  ∀ (B Q T : Type) [Group B] [Group Q] [Group T] (d : B),
    (∀ f : B →* T, f = 1) →
    Subgroup.normalClosure ({d} : Set B) = ⊤ →
      Function.Bijective
          (fun f : Q →* T ↦
            f.comp (MFCamouflage.projection d Q)) ∧
        (MFCamouflage.projection d Q).ker =
          Subgroup.normalClosure
            ({MFCamouflage.defect d Q} : Set (MFCamouflage.Camouflage d Q))

/-- Closed proof of the manuscript's universal-factorization proposition. -/
theorem manuscriptUniversalFactorization : UniversalFactorization := by
  intro B Q T _ _ _ d htrivial hnormal
  exact ⟨MFCamouflage.precomp_bijective d Q htrivial,
    MFCamouflage.projection_ker_eq_normalClosure d Q hnormal⟩

end OneSidedMFRadical
end Manuscript
end GroupApproximation
