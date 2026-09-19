import GroupApproximation.Kazhdan.AmenableKazhdanFinite
import GroupApproximation.Manuscript.OneSidedMFRadical.DefectSaturation
import GroupApproximation.Manuscript.OneSidedMFRadical.FiniteDimensionalCommutant
import GroupApproximation.Manuscript.OneSidedMFRadical.HeadlineTheorem
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedRemarks

/-!
# Sentence closure for the explicit configuration's consequences

Exact-route wrappers for census rows 69--78.  They compose the existing
unconditional compression, commutant, residual-finiteness, amenability, and
scope theorems; none restates their proofs.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open RankTwelveEndpoint

universe u v w

/-- **Sentence 69.**  Saturation of the explicit printed defect and the
compression criterion give the full MF radical of the rank-twelve group. -/
theorem manuscriptSentence69_configuration_gives_fullRadical :
    printedDefect corner = ⊤ ∧ actualCoronaMFResidual H = ⊤ :=
  ⟨printedDefect_eq_top_of_configuration printedDefectConfiguration,
    rankTwelve_actualCoronaMFResidual_eq_top⟩

/-- **Sentence 70.**  A one-sided compressor acts surjectively on the
finite-dimensional commutant, in exactly the represented form used in the
manuscript. -/
theorem manuscriptSentence70_finiteDimensional_commutant_bijection :
    FiniteDimensionalCommutantRigidity.{u, v, w} :=
  manuscriptFiniteDimensionalCommutantRigidity

/-- **Sentence 71.**  Consequently every finite-dimensional linear
representation kills the whole printed defect. -/
theorem manuscriptSentence71_finiteDimensional_kills_printedDefect :
    PrintedDefectFiniteDimensionalSterility.{u, v, w} :=
  manuscriptPrintedDefectFiniteDimensionalSterility

/-- **Sentence 72.**  A faithful finite-dimensional representation forces
the printed defect to be trivial. -/
theorem manuscriptSentence72_faithful_finiteDimensional_defect_bot
    {G : Type u} [Group G] {k : Type v} {V : Type w}
    [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : G →* (V ≃ₗ[k] V)) (hrho : Function.Injective rho)
    (L : Subgroup G) :
    printedDefect L = ⊥ :=
  printedDefect_eq_bot_of_faithful_finiteDimensional rho hrho L

/-- **Sentence 73.**  Residual finiteness forces the printed defect to be
trivial. -/
theorem manuscriptSentence73_residuallyFinite_defect_bot
    {G : Type u} [Group G] (hG : IsResiduallyFinite G) (L : Subgroup G) :
    printedDefect L = ⊥ :=
  printedDefect_eq_bot_of_isResiduallyFinite hG L

/-- **Sentences 74--77.**  In an amenable ambient group a Kazhdan subgroup is
finite; a one-sided compressor is therefore onto that subgroup, the conjugated
centralizer still centralizes it, and the printed defect is trivial. -/
theorem manuscriptSentences74_77_amenableKazhdan_chain
    {G : Type u} [Group G] (hA : Amenability.IsAmenable G)
    (L : Subgroup G) (hL : HasKazhdanPropertyT.{u, u} ↥L) :
    Finite ↥L ∧
      (∀ u ∈ compressionSet L,
        (fun x ↦ u * x * u⁻¹) '' (L : Set G) = (L : Set G)) ∧
      (∀ u ∈ compressionSet L, ∀ c : G,
        (∀ delta ∈ L, Commute c delta) →
          ∀ ell ∈ L, Commute (u * c * u⁻¹) ell) ∧
      printedDefect L = ⊥ := by
  have hfinite : Finite ↥L :=
    finite_subgroup_of_isAmenable_of_kazhdan hA L hL
  refine ⟨hfinite, ?_, ?_,
    printedDefect_eq_bot_of_isAmenable_of_kazhdan hA L hL⟩
  · intro u hu
    exact conj_image_eq_of_isAmenable_of_kazhdan hA hL hu
  · intro u hu c hc ell hell
    exact commute_conj_of_isAmenable_of_kazhdan hA hL hu hc hell

/-- **Sentence 78.**  Full MF or operator-to-Hilbert--Schmidt shadow radicals
do not entail nonsoficity or nonhyperlinearity. -/
theorem manuscriptSentence78_fullRadicals_do_not_obstruct_soficity :
    FullRadicalsDoNotEntailNonsoficity :=
  manuscriptFullRadicalsDoNotEntailNonsoficity

end OneSidedMFRadical
end Manuscript
end GroupApproximation
