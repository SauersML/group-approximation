import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterHost
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralTheoremClosure
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralTheorem
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralRingPropertyT
import GroupApproximation.Kazhdan.KazhdanFiniteGeneration
import GroupApproximation.Meta.AxiomGuard

/-!
# A simple Kazhdan host for every infinite finitely generated group, without LEF

`simple_kazhdan_sofic_group.tex`, l.477–481:

> Without LEF, every countable group embeds in a finitely generated simple
> group~\cite{Gorjuskin,Schupp}, and even in a simple quotient of a torsion-free hyperbolic Kazhdan
> group~\cite[Theorem~1.5]{CoulonFournierFacio}, so one simple Kazhdan group contains Higman's
> universal finitely presented group~\cite{Higman}.

## Plan

For an infinite finitely generated group `Δ`, the lamplighter host
`G_Δ = EL_3(LC(F_2^Δ, F_2) ⋊ (⊕_Δ F_2 ⋊ Δ))` is infinite, finitely generated, simple and Kazhdan.
None of these four facts needs LEF (LEF is only used for the matricial approximations):

* simplicity: `printedGeneralSimplicityStatement` applied to the minimal, topologically free
  action `Lamplighter.isMinimal`, `Lamplighter.isTopologicallyFree` on the Cantor set `F_2^Δ`;
* property (T) and infiniteness: `printedGroupCrossedProductPropertyTInfinite` with the finite
  generating set `Lamplighter.lampGenerators_finite`;
* finite generation: `KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT`.

Together with `Lamplighter.exists_commutator_embedding` (no LEF either), `[Δ, Δ]` embeds in `G_Δ`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SimpleHosts

open Lamplighter

/-- **The lamplighter host without LEF.** For an infinite finitely generated group `Δ`, the group
`G_Δ = EL_3(R_Δ)` is infinite, finitely generated, simple and has property (T). -/
theorem simpleKazhdanHost (Δ : Type) [Group Δ] [Infinite Δ] (hΔ : Group.FG Δ) :
    Infinite ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
      Group.FG ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
      IsSimpleGroup ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
      HasKazhdanPropertyT.{0, 0} ↥(elementaryGroup (Fin 3) (LampRing Δ)) := by
  classical
  obtain ⟨T, hT, hTfin⟩ := Group.fg_iff.1 hΔ
  haveI : Countable Δ := Lamplighter.countable_of_fg Δ hΔ
  haveI : Group.FG (LampAffine Δ) := Lamplighter.fg_lampAffine Δ hΔ
  have hSgen : Subring.closure
      (((lampGenerators_finite hTfin).toFinset : Finset (LampRing Δ)) : Set (LampRing Δ)) = ⊤ := by
    rw [Set.Finite.coe_toFinset]
    exact Lamplighter.closure_lampGenerators hT
  haveI : Infinite (LampSpace Δ) := infinite_of_perfectSpace (LampSpace Δ)
  obtain ⟨hT3, hInf⟩ := printedGroupCrossedProductPropertyTInfinite (LampAffine Δ) (LampSpace Δ)
    (lampGenerators_finite hTfin).toFinset hSgen 3 le_rfl
  exact ⟨hInf, KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT _ hT3,
    printedGeneralSimplicityStatement (LampAffine Δ) (LampSpace Δ) (Lamplighter.isMinimal Δ)
      (Lamplighter.isTopologicallyFree Δ) 3 le_rfl, hT3⟩

/-- **Every commutator subgroup of an infinite finitely generated group lies in a simple Kazhdan
group**: `[Δ, Δ]` embeds in an infinite, finitely generated, simple group with property (T). -/
theorem exists_simpleKazhdan_commutator_embedding (Δ : Type) [Group Δ] [Infinite Δ]
    (hΔ : Group.FG Δ) :
    ∃ (G : Type) (_ : Group G), Infinite G ∧ Group.FG G ∧ IsSimpleGroup G ∧
      HasKazhdanPropertyT.{0, 0} G ∧ ∃ f : ↥(commutator Δ) →* G, Function.Injective f := by
  obtain ⟨hinf, hfg, hsimple, hT⟩ := simpleKazhdanHost Δ hΔ
  obtain ⟨e, he⟩ := Lamplighter.exists_commutator_embedding Δ
  exact ⟨↥(elementaryGroup (Fin 3) (LampRing Δ)), inferInstance, hinf, hfg, hsimple, hT, e, he⟩

end SimpleHosts
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimpleHosts.simpleKazhdanHost
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimpleHosts.exists_simpleKazhdan_commutator_embedding
