import GroupApproximation.Manuscript.OneSidedMFRadical.KazhdanTransportSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.TransportProjectionCommutation
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work: where the rigidity of the compression criterion comes from

`non_mf_groups_exist.tex`, subsection *Related work* (tex lines 343–349 at
origin/main 68481e4d7), sentence `523f02126056`:

> Here the rigidity comes from the Kazhdan projection of `L` in a norm matrix
> corona, which commutes with the compressor because the corona is stably
> finite, and the obstruction is a commutator `[ucu⁻¹, ℓ] ≠ 1` that every
> operator norm asymptotic representation sends to `1` in Hilbert--Schmidt
> norm; Theorem~`thm:normal-kazhdan` then shows that every corona
> homomorphism is trivial on each normal Kazhdan subgroup of the defect.

The sentence summarizes the paper's own proof, so its carrier is one closed
proposition with one conjunct per printed clause, each proved by the theorem
that carries that clause inside the printed proofs:

1. the Kazhdan projection of `L` in the printed corona commutes with every
   compressor: `TransportProjectionCommutation.commute_sigmaB_projection`,
   whose proof is `lem:kazhdan-projection-order` followed by
   `lem:stable-finite` (the corona is stably finite);
2. every operator norm asymptotic representation sends `[ucu⁻¹, ℓ]` to `1` in
   normalized Hilbert--Schmidt norm:
   `manuscriptSentence_commutatorHilbertSchmidtVanishing` (`cor:defect-hs`);
3. at the paper's configuration the commutator is nontrivial:
   `RankTwelveEndpoint.manuscriptPropositionDefect`;
4. every corona homomorphism is trivial on each normal Kazhdan subgroup of the
   defect: clause one of `manuscriptOneSidedCompressionCriterion`, proved
   through `thm:normal-kazhdan`. `manuscriptCoronaMFResidual G` is the
   intersection of the kernels of all homomorphisms into the norm matrix
   coronas `∏_n M_{d_n}(ℂ) / ⊕_n M_{d_n}(ℂ)`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RelatedWork

open Filter Matrix
open MaximalCStarKazhdanProjection
open scoped commutatorElement

/-- **Sentence `523f02126056`, as one closed proposition.** The four printed
clauses, in the printed order. -/
def PrintedRelatedWorkKazhdanRigidity : Prop :=
  (∀ (G : Type) [Group G] (L : Subgroup G) (B : OpAlmostRepresentation G)
      [∀ n, Nonempty (B.model n)] (KD : KazhdanData ↥L)
      (f : MaximalGroupCStar ↥L →⋆ₐ[ℂ] TransportProjectionCommutation.sqCorona B),
      (∀ s : ↥L, f (maximalGroupCStarGenerator ↥L s) =
        ((TransportProjectionCommutation.sigmaB B (L.subtype s) :
            unitary (TransportProjectionCommutation.sqCorona B)) :
          TransportProjectionCommutation.sqCorona B)) →
      ∀ u ∈ compressionSet L,
        ((TransportProjectionCommutation.sigmaB B u :
            unitary (TransportProjectionCommutation.sqCorona B)) :
          TransportProjectionCommutation.sqCorona B) * f KD.projection =
        f KD.projection *
          ((TransportProjectionCommutation.sigmaB B u :
              unitary (TransportProjectionCommutation.sqCorona B)) :
            TransportProjectionCommutation.sqCorona B)) ∧
    (∀ (G : Type) [Group G] (L : Subgroup G), HasKazhdanPropertyT.{0, 0} ↥L →
      ∀ (u : G), (∀ l ∈ L, u * l * u⁻¹ ∈ L) →
      ∀ (c : G), (∀ l ∈ L, Commute c l) →
      ∀ ell ∈ L, ∀ (V : OpAlmostRepresentation G),
        Tendsto
          (fun n ↦ Real.sqrt (hsLengthSq (V.model n)
            ((V.map n ⁅u * c * u⁻¹, ell⁆ :
              Matrix (V.model n) (V.model n) ℂ))))
          atTop (nhds 0)) ∧
    RankTwelveEndpoint.PropositionDefect ∧
    (∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
      HasKazhdanPropertyT.{0, 0} ↥L →
      ∀ (K : Subgroup G) [K.Normal], HasKazhdanPropertyT.{0, 0} ↥K →
        K ≤ printedDefect L → K ≤ manuscriptCoronaMFResidual G)

/-- **Sentence `523f02126056`, proved, hypothesis-free.** -/
theorem manuscriptSentence_relatedWorkKazhdanRigidity :
    PrintedRelatedWorkKazhdanRigidity := by
  refine ⟨?_, ?_, RankTwelveEndpoint.manuscriptPropositionDefect, ?_⟩
  · intro G _ L B _ KD f hf u hu
    exact TransportProjectionCommutation.commute_sigmaB_projection B L KD f hf hu
  · intro G _ L hL u hu c hc ell hell V
    exact manuscriptSentence_commutatorHilbertSchmidtVanishing L hL u hu c hc ell hell V
  · intro G _ _ L hL K _ hK hKD
    exact (manuscriptOneSidedCompressionCriterion G L hL).1 K hK hKD

end RelatedWork
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.OneSidedMFRadical.RelatedWork.manuscriptSentence_relatedWorkKazhdanRigidity
#audit_axioms
  Manuscript.OneSidedMFRadical.manuscriptSentence_commutatorHilbertSchmidtVanishing
#audit_axioms
  Manuscript.OneSidedMFRadical.TransportProjectionCommutation.commute_sigmaB_projection
#audit_closed_axioms Manuscript.OneSidedMFRadical.manuscriptOneSidedCompressionCriterion
