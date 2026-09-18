import GroupApproximation.Manuscript.OneSidedMFRadical.UnitGroupHeadline
import GroupApproximation.Manuscript.NonMF.SimpleInDefect
import GroupApproximation.Meta.AxiomGuard

/-!
# The group of [OAI] and Fournier-Facio's configuration (Related work)

`non_mf_groups_exist.tex`, section *Related work*, **lines 349--351**
(census row `b89e90ea6607`):

> The group H is the group of [OAI], and Theorem thm:torsion-free reuses
> Fournier-Facio's configuration [FFF].

The sentence credits two sources.  What it identifies can be stated, and is
stated here; the credit itself stays attribution.

* **The group of [OAI].**  Lines 146--154 of the manuscript describe the group
  used in [OAI, Chapter 3] as the unit group `L_{𝔽₂}(1,2)^×` of the binary
  Leavitt algebra.  In the corpus the headline group is
  `OneSidedMFRadical.RankFourEndpoint.H = EL₄(L_{𝔽₂}(1,2))`, and
  `OneSidedMFRadical.UnitGroupHeadline.unitsEquivHeadline : Rˣ ≃* H` is the
  identification; `manuscriptSentence_oaiGroupAndFFFConfiguration` records
  `Nonempty (Rˣ ≃* H)` from `UnitGroupHeadline.manuscriptUnitGroupHeadline`.
* **Fournier-Facio's configuration.**  The configuration of [FFF] is
  `NonMF.PrintedFournierFacioData` (a core `Γ`, a compressor `t` with
  `tΓt⁻¹ ≤ Γ`, and a nonabelian simple factor `J` centralizing `Γ` with
  `tJt⁻¹ ≤ Γ`).  `printedFournierFacioData_oaiConfiguration` proves that every
  such datum is an instance of the configuration of [OAI, Proposition 2.3]
  quoted at tex 336--339 (`L = Γ`, `u = t`, and `c ∈ J` with `ucu⁻¹` not
  commuting with `L`).  The endpoint also records
  `NonMF.manuscriptLemmaCommutatorInDefect`, the lemma by which
  `thm:torsion-free` consumes the configuration.

Proof route for the configuration: take noncommuting `x, y ∈ J`; `x`
centralizes `Γ`; `tyt⁻¹ ∈ Γ`, so if `txt⁻¹` centralized `Γ` it would commute
with `tyt⁻¹`, and conjugating back by `t` would make `x` and `y` commute.

Not claimed: the existence of the [FFF] group
(`NonMF.TorsionFreePrinted.FournierFacioParagraph`) and `thm:torsion-free`
itself (`NonMF.TorsionFreePrinted.PrintedTorsionFreeTheorem`) are not proved
unconditionally in the corpus; census row `0f22bdbc4184` is `partial`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace RelatedAttribution

/-- **A Fournier-Facio datum is an [OAI] configuration.**  The core is
conjugated into itself by the compressor, and some element of the simple
factor commutes with the core while its conjugate by the compressor does
not. -/
theorem printedFournierFacioData_oaiConfiguration {E : Type} [Group E]
    (F : PrintedFournierFacioData E) :
    (∀ l ∈ F.core, F.t * l * F.t⁻¹ ∈ F.core) ∧
      ∃ c ∈ F.simpleFactor, (∀ l ∈ F.core, Commute c l) ∧
        ¬ ∀ l ∈ F.core, Commute (F.t * c * F.t⁻¹) l := by
  obtain ⟨x, y, hxy⟩ := F.nonabelian
  refine ⟨F.conj_core_mem, (x : E), x.2,
    fun l hl => F.simpleFactor_centralizes (x : E) x.2 l hl, ?_⟩
  intro h
  have hc : Commute (F.t * (x : E) * F.t⁻¹) (F.t * (y : E) * F.t⁻¹) :=
    h (F.t * (y : E) * F.t⁻¹) (F.conj_simpleFactor_mem (y : E) y.2)
  have h2 : F.t⁻¹ * ((F.t * (x : E) * F.t⁻¹) * (F.t * (y : E) * F.t⁻¹)) * F.t =
      F.t⁻¹ * ((F.t * (y : E) * F.t⁻¹) * (F.t * (x : E) * F.t⁻¹)) * F.t := by
    rw [hc.eq]
  refine hxy (Commute.of_map (Subgroup.subtype_injective F.simpleFactor) ?_)
  show (x : E) * (y : E) = (y : E) * (x : E)
  simpa [mul_assoc] using h2

/-- **tex 349--351: the group of [OAI] and the configuration of [FFF].**
`H = EL₄(L_{𝔽₂}(1,2))` is isomorphic to the unit group of the binary Leavitt
algebra; every Fournier-Facio datum is an [OAI] configuration; and the
conjugated simple factor lies in the defect of every image of the core
(`lem:commutator-in-defect`). -/
theorem manuscriptSentence_oaiGroupAndFFFConfiguration :
    Nonempty ((OneSidedMFRadical.RankFourEndpoint.R)ˣ ≃*
        OneSidedMFRadical.RankFourEndpoint.H) ∧
      (∀ {E : Type} [Group E] (F : PrintedFournierFacioData E),
        (∀ l ∈ F.core, F.t * l * F.t⁻¹ ∈ F.core) ∧
          ∃ c ∈ F.simpleFactor, (∀ l ∈ F.core, Commute c l) ∧
            ¬ ∀ l ∈ F.core, Commute (F.t * c * F.t⁻¹) l) ∧
      PrintedCommutatorInDefect :=
  ⟨OneSidedMFRadical.UnitGroupHeadline.manuscriptUnitGroupHeadline.1,
    fun F => printedFournierFacioData_oaiConfiguration F,
    manuscriptLemmaCommutatorInDefect⟩

end RelatedAttribution
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedAttribution.printedFournierFacioData_oaiConfiguration
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedAttribution.manuscriptSentence_oaiGroupAndFFFConfiguration
