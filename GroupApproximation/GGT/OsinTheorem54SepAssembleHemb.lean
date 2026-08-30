import GroupApproximation.GGT.OsinTheorem54SepAssembleFull
import GroupApproximation.GGT.OsinTheorem54SepFourPointBridge
import GroupApproximation.GGT.OsinTheorem54SepLemma511Intersection

/-!
# The assembly with the §4.2 threshold discharged

`sepDataFam_of_binders_of_lemma510` asks for `hthr`: some constant `C` bounding
the isolated components of six-sided polygons, with `4C ≤ Dc`.  That is a
hypothesis about `Dc`, and it can only be met by a caller who chooses `Dc` AFTER
the constant exists.  This module states the theorem in that order --- `C`
first, `Dc` past the threshold, then the two remaining conditions --- so the
caller never has to produce a threshold at all.

`C` comes from clause (a) of `IsHyperbolicallyEmbedded` and nothing else:
`exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded` moves it to the
four-point form and `sixBound_one_of_fourPointHyperbolic` produces the bound.

## What is left

One condition: `h511`, the remaining geometry in Osin's Lemma 5.11.  It is
`OsinComponents.Lemma511Geometry`, consisting of setwise Lemma 4.9 and the
entrance-gap estimate (38).  Equation (37), the choice of the shared separator
outside `S(1,k;D)`, the `3R` entrance enumeration, and the final finite counting
are proved in `OsinTheorem54SepLemma511Intersection` and
`OsinTheorem54SepLemma511Count`.
The local finiteness of the enlarged relative metrics is now
`OsinComponents.relBall_enlargedY_finite`, the completed Lemma 5.8 assembly.
The bounded-detour condition of Lemma 5.6 is not among the binders either --- it is
`OsinLemma56Inheritance.exists_boundedDetour`, supplied inside the assembly ---
and neither is anything from §4.2.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **`SepDataStatementFam` from hyperbolic embedding and the remaining
geometry of Lemma 5.11.**  Equation (37), the finite counting at the end of
Lemma 5.11, the §4.2 threshold, Lemma 5.6's condition, and Lemma 5.8 are
discharged. -/
theorem exists_sepDataFam_of_hemb [Fintype Λ] (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (hemb : D.IsHyperbolicallyEmbedded) :
    ∃ C : ℕ, 0 < C ∧ ∀ (Dc : ℕ) (hDc : 1 ≤ Dc), C * 4 ≤ Dc →
      Lemma511Geometry D (enlargedY D hDc hsymm) Dc →
      ∃ S : SepDataFam D, S.AcylindricalCore := by
  obtain ⟨δ, hδ⟩ :=
    exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded D hemb
  obtain ⟨C, hCpos, hbnd⟩ :=
    sixBound_one_of_fourPointHyperbolic D hsymm hδ 0 le_rfl
  refine ⟨C, hCpos, fun Dc hDc hthr h511 => ?_⟩
  obtain ⟨h48, hcover, hgap⟩ := h511
  have h49 := lemmaFourNine_of_bound D hsymm hbnd hthr h48
  have hdist := dist_le_sep_enlargedY D hDc hsymm h48
  have hsle := sep_le_dist_enlargedY D hDc hsymm h48
    (mult_of_relBall_one D hDc) h49
  have hencode : Lemma511EntranceEncoding D (enlargedY D hDc hsymm) Dc :=
    entranceEncoding_of_sharedGap D (enlargedY D hDc hsymm) Dc h48 hcover
      hdist hsle hgap
  exact sepDataFam_of_binders_of_lemma510 D hDc hsymm ⟨C, hbnd, hthr⟩ hemb
    (relBall_enlargedY_finite D hDc hsymm hemb)
    (acylindricalCore_of_entranceEncoding D (enlargedY D hDc hsymm) Dc hemb hencode)

end OsinEnlargement
end GGT
end GroupApproximation
