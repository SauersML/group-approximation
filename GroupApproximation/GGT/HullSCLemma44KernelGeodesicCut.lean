import GroupApproximation.GGT.HullSCLemma44RelativeDehn
import GroupApproximation.GGT.HullSCLemma44PrefixGeometry

/-!
# One actual kernel-geodesic cut

This file performs the algebraic part of Osin's least-area step.  A relative
Greendlinger certificate gives a `RelativeDehnCut`; the shortened boundary is
still null in the quotient.  A shortest word for its new source endpoint is
then chosen in the prefix alphabet, and its length is strictly smaller than
the old designated boundary length.  The source endpoint is allowed to
change, as a relator cut changes it by a conjugate relator while preserving
its quotient value.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u v w

/-- A Greendlinger certificate and a quotient-null boundary produce a shorter
geodesic kernel word.  The word is over the prefix enlargement, while its
endpoint is a new element of `q.ker`. -/
theorem exists_shorter_kernelGeodesic_of_relativeDiagramCertificate
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000) (hrho : 20 * (eps + 1) ≤ rho)
    {R : ℕ} {Z : RelativeReducedDiagram D W R}
    (K : RelativeDiagramCertificate D W eps mu Z)
    (q : G →* Q) (_hq : Function.Surjective q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hboundary : q K.boundaryWord.prod = 1) :
    ∃ (nextKernel : G) (nextWord : List G),
      nextKernel ∈ q.ker ∧
        nextWord.prod = nextKernel ∧
        (∀ x ∈ nextWord,
          x ∈ (D.adjoinRelatorPrefixes W
            hsc.toIsSmallCancellation).alphabet.carrier) ∧
        nextWord.length < K.boundaryWord.length ∧
        nextWord.length = wordDist
          (D.adjoinRelatorPrefixes W
            hsc.toIsSmallCancellation).alphabet.carrier
          1 nextKernel := by
  have hcut : Nonempty (RelativeDehnCut D W eps q K.boundaryWord) := by
    apply exists_relativeDehnCut_of_certificate D hsc hmu hrho K q
    intro relator hrelator
    apply MonoidHom.mem_ker.mp
    rw [hker]
    exact Subgroup.subset_normalClosure ⟨relator, hrelator, rfl⟩
  obtain ⟨cut⟩ := hcut
  let nextKernel : G := cut.contiguity.shortenedBoundaryWord.prod
  have hnextQuotient : q nextKernel = 1 := by
    dsimp [nextKernel]
    rw [cut.quotient_value, hboundary]
  have hnextKer : nextKernel ∈ q.ker :=
    MonoidHom.mem_ker.mpr hnextQuotient
  let E := D.adjoinRelatorPrefixes W hsc.toIsSmallCancellation
  obtain ⟨nextWord, hnextWord, hnextLength⟩ :=
    exists_isWord_length_eq E.alphabet.symmetricGenerating nextKernel
  have hnextProd : nextWord.prod = nextKernel := hnextWord.prod_eq
  have hshortWord : IsWord E.alphabet.carrier
      cut.contiguity.shortenedBoundaryWord nextKernel := by
    have hsource := cut.shortenedWord_isWord
    refine ⟨?_, ?_⟩
    · intro x hx
      exact alphabet_subset_adjoinRelatorPrefixes D W
        hsc.toIsSmallCancellation (hsource.letters x hx)
    · exact hsource.prod_eq.trans rfl
  have hshortNorm : wordNorm E.alphabet.carrier nextKernel ≤
      cut.contiguity.shortenedBoundaryWord.length :=
    wordNorm_le_length hshortWord
  have hnextShort : nextWord.length < K.boundaryWord.length := by
    rw [hnextLength]
    exact lt_of_le_of_lt hshortNorm cut.length_lt
  refine ⟨nextKernel, nextWord, hnextKer, hnextProd, ?_, hnextShort, ?_⟩
  · exact hnextWord.letters
  · rw [wordDist_one_left]
    exact hnextLength

end HullSC
end GroupApproximation
