import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFLevelEmbedding
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCharacterizationClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFHostInstancesLamplighterClosed
import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Meta.AxiomGuard

/-!
# Audit repairs: finite models on initial segments, and simple LEF hosts without (T)

`simple_kazhdan_sofic_group.tex` at 1eefb3bbbf0eafe710276b85dbf87512c6ddc95a, section "LEF groups".

## Census key `8b9c8012260d` (tex l.495–499, proof of `lem:nn`)

> Let $\Gamma=\{\gamma_1,\gamma_2,\dots\}$ be a countable LEF group; [...] There are finite groups
> $Q_k$ and maps $\mu_k\colon\Gamma\to Q_k$ that are injective on $\{1,\gamma_1,\dots,\gamma_k\}$
> and preserve the products that stay in this set.

The existing `LEFLevelEmbedding.models_nonempty` chooses its own enumeration. The sentence fixes the
enumeration first. `manuscriptSentence_finiteModelsOnInitialSegments` takes an arbitrary sequence
`γ : ℕ → Γ` and gives models on `testSet γ k = {1, γ 1, …, γ k}`. The proof applies textbook LEF
(`isLEF_iff_textbook`) to each finite set.

## Census key `8212b1470040` (tex l.472–477, attribution)

> Without property~(T), Kionke and Schesler proved that every finitely generated residually finite
> group embeds in a finitely generated simple LEF group [KionkeSchesler, Theorem 1.2], so with
> Wilson's theorem [Wilson] one simple LEF group contains every finitely presented residually finite
> group.

The sentence credits the mathematics to others, but it does assert that mathematics, so both claims
are formalized here from the corpus. The route is different from the cited one: the hosts of
`cor:lef` and `cor:host` are finitely generated, simple and LEF (`isLEF_of_isLEFHost`).

* The first claim uses `printedLEFSubgroupCharacterization`. A residually finite group is LEF
  (`isLEF_of_residuallyFinite`).
* The second claim uses `printedRecursivelyPresentedLEFHostInstances`. One host contains every
  finitely presented residually finite group.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace Audit2

/-- **tex l.497–499.**  For an LEF group `Γ` and any enumeration `γ`, there are finite groups `Q k`
and maps `μ k : Γ → Q k`. Each `μ k` is injective on `{1, γ 1, …, γ k}` and preserves the products
that stay in this set. -/
theorem manuscriptSentence_finiteModelsOnInitialSegments {Γ : Type} [Group Γ] (hΓ : IsLEF Γ)
    (γ : ℕ → Γ) :
    ∃ (Q : ℕ → FiniteGroupModel) (μ : ∀ k, Γ → Q k),
      (∀ k, Set.InjOn (μ k) (LEFLevelEmbedding.testSet γ k : Set Γ)) ∧
        ∀ k, ∀ x ∈ LEFLevelEmbedding.testSet γ k, ∀ y ∈ LEFLevelEmbedding.testSet γ k,
          x * y ∈ LEFLevelEmbedding.testSet γ k → μ k (x * y) = μ k x * μ k y := by
  choose Q μ inj mul using fun k => (isLEF_iff_textbook Γ).1 hΓ (LEFLevelEmbedding.testSet γ k)
  exact ⟨Q, μ, inj, mul⟩

/-- **tex l.473–477.**  Every finitely generated residually finite group embeds in a finitely
generated simple LEF group. One finitely generated simple LEF group contains every finitely presented
residually finite group. -/
theorem manuscriptSentence_simpleLEFHostsWithoutT :
    (∀ (Γ : Type) [Group Γ], Group.FG Γ → Group.ResiduallyFinite Γ →
      ∃ (E : Type) (_ : Group E), Group.FG E ∧ IsSimpleGroup E ∧ IsLEF E ∧
        ∃ f : Γ →* E, Function.Injective f) ∧
      ∃ (E : Type) (_ : Group E), Group.FG E ∧ IsSimpleGroup E ∧ IsLEF E ∧
        ∀ (Γ : Type) [Group Γ], Group.IsFinitelyPresented Γ → Group.ResiduallyFinite Γ →
          ∃ f : Γ →* E, Function.Injective f := by
  refine ⟨fun Γ _ hfg _ => ?_, ?_⟩
  · obtain ⟨E, hgrp, hE, f, hf⟩ :=
      (printedLEFSubgroupCharacterization Γ hfg).1 (isLEF_of_residuallyFinite (G := Γ))
    exact ⟨E, hgrp, hE.2.1, hE.2.2.1, isLEF_of_isLEFHost hE, f, hf⟩
  · obtain ⟨E, hgrp, hE, -, hfp, -⟩ := printedRecursivelyPresentedLEFHostInstances
    exact ⟨E, hgrp, hE.2.1, hE.2.2.1, isLEF_of_isLEFHost hE, hfp⟩

end Audit2
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Audit2.manuscriptSentence_finiteModelsOnInitialSegments
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Audit2.manuscriptSentence_simpleLEFHostsWithoutT
