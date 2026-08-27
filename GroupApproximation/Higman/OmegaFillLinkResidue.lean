import GroupApproximation.Higman.OmegaFillLinkPreimage
import GroupApproximation.Higman.OmegaFatShearedLinkSemantic

/-!
# The `ωₘ` residue, at the sheared block link

`Higman.OmegaFillLinkPreimage` moves the residue to any group in which the
slim link is cut out of a benign subgroup by an injection.
`Omega.fatShearedBlockLink` is the canonical choice: it lives in
`FatCent3 m × F₃`, which is finitely presented and torsion-free, and
`Omega.fatShearedBlockLink_comap_slimFatSemanticBaseEmb` is the preimage
equation on the nose.

After this file the `ωₘ` lane owes exactly one statement,

    `∀ m, BenignTF (Omega.fatShearedBlockLink m)` ,

which is Mikaelian's Example 3.12 read in the fat first stage, and which
`Higman.OmegaFillLeadLinkBenign` proves.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Seq

/-- **The slim link is benign as soon as its sheared image is.** -/
theorem benignTF_slimLink_of_shearedLink {m : ℕ}
    (h : BenignTF (fatShearedBlockLink m)) : BenignTF (slimLink m) :=
  benignTF_slimLink_of_preimage (slimFatSemanticBaseEmb m)
    (slimFatSemanticBaseEmb_injective m)
    (fatShearedBlockLink_comap_slimFatSemanticBaseEmb m) h

/-- **Higman's `ωₘ` closure, from the slim descent and one benignness
statement in a finitely presented group.** -/
theorem omegaInput_of_shearedLinkBenign (hd : SlimDescent)
    (h : ∀ m : ℕ, BenignTF (fatShearedBlockLink m)) : OmegaInput :=
  omegaInput_of_slimLinkBenign hd fun m => benignTF_slimLink_of_shearedLink (h m)

end Omega
end Higman
end GroupApproximation
