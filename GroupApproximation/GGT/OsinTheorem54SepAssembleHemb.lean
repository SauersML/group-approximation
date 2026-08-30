import GroupApproximation.GGT.OsinTheorem54SepAssembleFull
import GroupApproximation.GGT.OsinTheorem54SepFourPointBridge
import GroupApproximation.GGT.OsinTheorem54SepLemma58

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

One condition: `h511`, Osin's acylindricity residue (Lemma 5.11).
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

/-- **`SepDataStatementFam` from hyperbolic embedding and Lemma 5.11.**
The §4.2 threshold, Lemma 5.6's condition, and Lemma 5.8 are discharged. -/
theorem exists_sepDataFam_of_hemb [Fintype Λ] (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (hemb : D.IsHyperbolicallyEmbedded) :
    ∃ C : ℕ, 0 < C ∧ ∀ (Dc : ℕ) (hDc : 1 ≤ Dc), C * 4 ≤ Dc →
      (∀ m : ℕ, ∃ R N : ℕ, 0 < R ∧ ∀ z : G,
        wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 z = R →
          {k : G | wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 k ≤ m ∧
              wordDist (enlargedY D hDc hsymm).alphabet.carrier 1
                (z⁻¹ * k * z) ≤ m}.Finite ∧
            {k : G | wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 k ≤ m ∧
              wordDist (enlargedY D hDc hsymm).alphabet.carrier 1
                (z⁻¹ * k * z) ≤ m}.ncard ≤ N) →
      ∃ S : SepDataFam D, S.AcylindricalCore := by
  obtain ⟨δ, hδ⟩ :=
    exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded D hemb
  obtain ⟨C, hCpos, hbnd⟩ :=
    sixBound_one_of_fourPointHyperbolic D hsymm hδ 0 le_rfl
  refine ⟨C, hCpos, fun Dc hDc hthr h511 => ?_⟩
  exact sepDataFam_of_binders_of_lemma510 D hDc hsymm ⟨C, hbnd, hthr⟩ hemb
    (relBall_enlargedY_finite D hDc hsymm hemb) h511

end OsinEnlargement
end GGT
end GroupApproximation
