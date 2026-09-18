import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterWP.Sentences
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCharacterizationClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# Abstract, tex l.41–45: LEF groups are the subgroups of simple Kazhdan expander limits, with a host of the same
Turing degree

`simple_kazhdan_sofic_group.tex`, abstract, l.41–45 (census row `ea436a85317e`):

> A finitely generated group is LEF if and only if it is a subgroup of an infinite, finitely generated, simple
> Kazhdan group that is a limit of finite simple groups whose Cayley graphs form expanders, and the host can be
> chosen with a word problem of the same Turing degree as that of the group.

## Spelling

* "an infinite, finitely generated, simple Kazhdan group that is a limit of finite simple groups whose Cayley
  graphs form expanders" is `IsLEFHost E`: infinite, finitely generated, simple, property (T), and a marked limit of
  the finite simple groups `SL_{κ_ℓ}(F₂)` along generating families with uniform edge expansion.
* "a subgroup of" is an injective homomorphism `Γ →* E`.
* "a word problem of the same Turing degree as that of the group" is: for every finite generating family `t` of `Γ`
  and every finite generating family `s` of `E` (both with primcodable index types), the oracles
  `wordProblemOracle t` and `wordProblemOracle s` are Turing equivalent. Such families exist, as `Γ` and `E` are
  finitely generated (`exists_fin_generators`), so the clause is not vacuous; it does not depend on the choice.

## Proof route

* The equivalence is `cor:lef`, first statement (`printedLEFSubgroupCharacterization`).
* For the choice of host, fix a finite generating family `t₀ : Fin n → Γ`. `lem:halfline` (a)
  (`HalflineA.manuscriptSentence_halflineEmbedding`) gives an infinite finitely generated LEF group `Δ` with
  `Γ ↪ [Δ,Δ]`, a finite generating family `u` of `Δ`, and `WP(u) ≤_T WP(t₀)`. `lem:host`
  (`lamplighterHostStatement`) makes `G_Δ = EL_3(R_Δ)` an `IsLEFHost` with `[Δ,Δ] ↪ G_Δ`, so `Γ ↪ G_Δ`
  (`LamplighterWP.exists_host_embedding`).
* `WP(s) ≤_T WP(u)` for every finite family `s` of `G_Δ`: `lem:halfline` (b)
  (`LamplighterWP.manuscriptSentence_halflineHostWordProblemReduction`). Changing the generating family of `Γ` is
  free (`turingReducible_wordProblemOracle_of_generates`), so `WP(s) ≤_T WP(u) ≤_T WP(t₀) ≤_T WP(t)`.
* `WP(t) ≤_T WP(s)` is substitution along the embedding `Γ ↪ G_Δ` (`printedWordProblemReducesUnderEmbedding`).

This is the proof of `LamplighterWP.manuscriptSentence_lefHostWordProblemAbove`, keeping the edge-expansion host
`IsLEFHost` instead of weakening it to the neighbour-expansion host `LEFCorollaries.IsExpanderLimitHost`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.TuringHost

open GroupApproximation.SimpleKazhdanSofic

/-- **The host can be chosen with the Turing degree of the group** (tex l.43–45). Every finitely generated LEF
group `Γ` embeds in an infinite, finitely generated, simple Kazhdan group `E` that is a marked limit of finite
simple groups `SL_N(F₂)` whose Cayley graphs form expanders, such that the word problems of any finite generating
families of `Γ` and of `E` are Turing equivalent. -/
theorem exists_isLEFHost_sameTuringDegree (Γ : Type) [Group Γ] (hfg : Group.FG Γ) (hΓ : IsLEF Γ) :
    ∃ (E : Type) (_ : Group E), IsLEFHost E ∧ ∃ f : Γ →* E, Function.Injective f ∧
      ∀ (κ ι : Type) [Primcodable κ] [Primcodable ι] [Finite κ] [Finite ι] (t : κ → Γ) (s : ι → E),
        Subgroup.closure (Set.range t) = ⊤ → Subgroup.closure (Set.range s) = ⊤ →
          TuringEquivalent (wordProblemOracle t) (wordProblemOracle s) := by
  obtain ⟨n, t0, ht0⟩ := exists_fin_generators Γ hfg
  obtain ⟨Δ, _, hinf, hfgΔ, hlef, ⟨f, hf, hcomm⟩, ⟨μ, _, _, u, hu⟩, hΔ⟩ :=
    HalflineA.manuscriptSentence_halflineEmbedding Γ (Fin n) t0 ht0 hΓ
  obtain ⟨hhost, g, hg⟩ := lamplighterHostStatement Δ hinf hfgΔ hlef
  obtain ⟨e, he⟩ := LamplighterWP.exists_host_embedding f hf hcomm g hg
  refine ⟨↥(elementaryGroup (Fin 3) (Lamplighter.LampRing Δ)), inferInstance, hhost, e, he, ?_⟩
  intro κ ι _ _ _ _ t s ht hs
  exact ⟨printedWordProblemReducesUnderEmbedding Γ _ ι κ s t e he hs ht,
    (((LamplighterWP.manuscriptSentence_halflineHostWordProblemReduction Δ μ u hu).2 ι s).trans
      (hΔ μ u)).trans (turingReducible_wordProblemOracle_of_generates ht t0)⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.TuringHost.exists_isLEFHost_sameTuringDegree

/-- **Abstract, tex l.41–45.** A finitely generated group `Γ` is LEF if and only if it is a subgroup of an
infinite, finitely generated, simple Kazhdan group that is a marked limit of finite simple groups `SL_N(F₂)` whose
Cayley graphs form expanders (`IsLEFHost`); and when `Γ` is LEF, the host can be chosen so that its word problem
has the Turing degree of the word problem of `Γ`: the word problems of any finite generating families of `Γ` and of
the host are Turing equivalent (both reductions). -/
theorem manuscriptSentence_lefIffSubgroupOfSimpleKazhdanExpanderLimitSameTuringDegree (Γ : Type) [Group Γ]
    (hfg : Group.FG Γ) :
    (IsLEF Γ ↔ ∃ (E : Type) (_ : Group E), IsLEFHost E ∧ ∃ f : Γ →* E, Function.Injective f) ∧
      (IsLEF Γ → ∃ (E : Type) (_ : Group E), IsLEFHost E ∧ ∃ f : Γ →* E, Function.Injective f ∧
        ∀ (κ ι : Type) [Primcodable κ] [Primcodable ι] [Finite κ] [Finite ι] (t : κ → Γ) (s : ι → E),
          Subgroup.closure (Set.range t) = ⊤ → Subgroup.closure (Set.range s) = ⊤ →
            TuringEquivalent (wordProblemOracle t) (wordProblemOracle s)) :=
  ⟨printedLEFSubgroupCharacterization Γ hfg, exists_isLEFHost_sameTuringDegree Γ hfg⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.TuringHost.manuscriptSentence_lefIffSubgroupOfSimpleKazhdanExpanderLimitSameTuringDegree

/-- **Abstract, tex l.41–45, in one equivalence.** A finitely generated group is LEF if and only if it is a
subgroup of such a host whose word problem has the Turing degree of its own. -/
theorem lefIffSubgroupOfSameTuringDegreeHost (Γ : Type) [Group Γ] (hfg : Group.FG Γ) :
    IsLEF Γ ↔ ∃ (E : Type) (_ : Group E), IsLEFHost E ∧ ∃ f : Γ →* E, Function.Injective f ∧
      ∀ (κ ι : Type) [Primcodable κ] [Primcodable ι] [Finite κ] [Finite ι] (t : κ → Γ) (s : ι → E),
        Subgroup.closure (Set.range t) = ⊤ → Subgroup.closure (Set.range s) = ⊤ →
          TuringEquivalent (wordProblemOracle t) (wordProblemOracle s) := by
  refine ⟨exists_isLEFHost_sameTuringDegree Γ hfg, ?_⟩
  rintro ⟨E, _, hE, f, hf, -⟩
  exact (printedLEFSubgroupCharacterization Γ hfg).2 ⟨E, inferInstance, hE, f, hf⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.TuringHost.lefIffSubgroupOfSameTuringDegreeHost

end GroupApproximation.Manuscript.SimpleKazhdanSofic.TuringHost
