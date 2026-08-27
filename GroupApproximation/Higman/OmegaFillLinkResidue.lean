import GroupApproximation.Higman.OmegaFillLinkPreimage
import GroupApproximation.Higman.OmegaFatShearedLinkSemantic

/-!
# The `ωₘ` residue, at the sheared block link

`Higman.OmegaFillLinkPreimage` relocates the residue to any group in which the
slim link is cut out of a benign subgroup.  The peer lane's
`Omega.fatShearedBlockLink` is the canonical choice: it lives in
`FatCent3 m × F₃`, which is finitely presented and torsion-free, and
`Omega.fatShearedBlockLink_comap_slimFatSemanticBaseEmb` is the preimage
equation on the nose.

After this file the `ωₘ` lane owes exactly one statement,

    `∀ m, BenignTF (Omega.fatShearedBlockLink m)` ,

which is Mikaelian's Example 3.12 read in the fat first stage.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Seq

/-- **The sheared image cuts the link out.** -/
theorem linkPreimage_of_shearedLinkBenign
    (h : ∀ m : ℕ, BenignTF (fatShearedBlockLink m)) : LinkPreimage :=
  ⟨fun m => ⟨FatCent3 m × F₃, inferInstance, slimFatSemanticBaseEmb m,
    fatShearedBlockLink m, slimFatSemanticBaseEmb_injective m, h m,
    fatShearedBlockLink_comap_slimFatSemanticBaseEmb m⟩⟩

/-- **The slim link is benign as soon as its sheared image is.** -/
theorem benignTF_slimLink_of_shearedLink {m : ℕ}
    (h : BenignTF (fatShearedBlockLink m)) : BenignTF (slimLink m) :=
  benignTF_of_comap_eq (slimFatSemanticBaseEmb m)
    (slimFatSemanticBaseEmb_injective m)
    (fatShearedBlockLink_comap_slimFatSemanticBaseEmb m) h

/-- **Higman's `ωₘ` closure, from the slim descent and one benignness
statement in a finitely presented group.** -/
theorem omegaInput_of_shearedLinkBenign (hd : SlimDescent)
    (h : ∀ m : ℕ, BenignTF (fatShearedBlockLink m)) : OmegaInput :=
  omegaInput_of_linkPreimage hd (linkPreimage_of_shearedLinkBenign h)

end Omega
end Higman
end GroupApproximation
