import GroupApproximation.Sofic.LiteralTheoremAPackage

/-!
# The explicit seed: one relation MF cannot see

The literal eight-generator, forty-one-relator group `E` carries a nontrivial
*central involution* that every matrix-corona representation kills.  It is the
cleanest elementary witness in the paper and the initial datum some later
constructions amplify — but it is no longer the climax: the climax is that the
radical can be everything (`FullRadical`, `SimpleSofic`) and that it can be
computed exactly (`PerfectLampExact`).

The seed statement below is deliberately weaker than the literal package it is
proved from: it advertises only what the paper's Section 4 displays.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRadicals

open LiteralNonMFPresentation

/-- **The seed theorem.**  There is a finitely presented sofic group carrying a
nontrivial central element that lies in the MF radical; the group is not MF. -/
theorem manuscriptExplicitSeed :
    ∃ (G : Type) (_ : Group G) (_ : Countable G) (w : G),
      Group.IsFinitelyPresented G ∧ IsSofic G ∧
        w ≠ 1 ∧ w ^ 2 = 1 ∧ (∀ g : G, Commute w g) ∧
        w ∈ actualCoronaMFResidual G ∧
        ¬ IsCDEOperatorMF G ∧ ¬ IsOperatorMF G := by
  obtain ⟨⟨-, -, -, hfp⟩, ⟨hsofic, -⟩, ⟨-, hne, hsq, hcentral⟩, -, hcde,
    hop, -, -⟩ := LiteralTheoremAPackage.manuscriptTheoremA_package
  refine ⟨MarkedGroup, inferInstance, inferInstance, mark, hfp, hsofic, hne,
    hsq, hcentral,
    ?_, hcde, hop⟩
  rw [← manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
  exact LiteralNonMFEndpoint.literal_mark_mem_manuscriptCoronaMFResidual

end MFRadicals
end Manuscript
end GroupApproximation
