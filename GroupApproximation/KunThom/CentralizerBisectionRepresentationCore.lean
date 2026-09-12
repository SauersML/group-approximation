import GroupApproximation.KunThom.CentralizerBisectionRepresentationFrameRetained
import GroupApproximation.KunThom.CompressorNormalizationAssemblyCore

/-!
# The per-compressor core with the forward half of Kun--Thom Lemma 4.2(4)

`seqNormalizes_distinguished_of_steps` leaves `hrep` open.  It is
`ClusterFrame.exists_bis_patch_close_of_retained`, so
`seqNormalizes_distinguished_of_representation` drops it.  Its open hypotheses are the
matching error and `hmatching`, `hfunctor` and `hhamming`.
-/

namespace GroupApproximation
namespace CompressorNormalizationAssembly

/-- **The forward inclusion for the distinguished compressor, with `hrep` discharged.** -/
theorem seqNormalizes_distinguished_of_representation {G : Type} [Group G] [Countable G]
    {Γ : Subgroup G} [Infinite ↥Γ]
    (hTG : HasKazhdanPropertyT.{0, 0} G) (hTΓ : HasKazhdanPropertyT.{0, 0} ↥Γ)
    (C : CompressionSetup G ↥Γ PUnit.{1}) (hembed : ∀ g : ↥Γ, C.embedΓ g = (g : G))
    (matchingError : ∀ {A : SoficApproximation G},
      CompressorDecomposition (normalizedSetup C hembed) A → ℕ → ℝ)
    (hmatching : ∀ (A : SoficApproximation G)
      (D : CompressorDecomposition (normalizedSetup C hembed) A),
        (∀ n, 0 ≤ matchingError D n) ∧ Vanishing (matchingError D))
    (hfunctor : ∀ (A : SoficApproximation G)
      (D : CompressorDecomposition (normalizedSetup C hembed) A) (F : ClusterFrame D.retained),
        F.repairFactor = compressorRepairFactor (normalizedSetup C hembed) →
          Vanishing F.threshold →
            (Vanishing fun n ↦ matchingError D n / F.threshold n) →
              Nonempty (CountingEndgame.CompressorRelativeData C.distinguished F))
    (hhamming : ∀ (A : SoficApproximation G)
      (D : CompressorDecomposition (normalizedSetup C hembed) A) (F : ClusterFrame D.retained)
      (M : CountingEndgame.CompressorRelativeData C.distinguished F) (a b : ∀ n, F.Bis n),
        M.Transported a b →
          Vanishing fun n ↦ hammingDistance (A.model n) (F.patch n (b n))
            (A.map n C.distinguished * F.patch n (a n) * (A.map n C.distinguished)⁻¹)) :
    SeqNormalizes Γ C.distinguished :=
  seqNormalizes_distinguished_of_steps hTG hTΓ C hembed matchingError hmatching
    (fun _ _ F _ hthr v _ hdom ↦ F.exists_bis_patch_close_of_retained hthr v hdom)
    hfunctor hhamming

end CompressorNormalizationAssembly
end GroupApproximation
