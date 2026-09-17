import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterWP.Host
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCorollaries.WordProblemHosts
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCharacterizationClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineA.Embedding
import GroupApproximation.Meta.AxiomGuard

/-!
# Word problems of the hosts: the Turing degree statements of `cor:lef` and `cor:host`

`simple_kazhdan_sofic_group.tex`, `cor:lef`, l.456–460:

> For every finitely generated LEF group $\Gamma$ there is such a group containing $\Gamma$ whose
> word problem has the Turing degree of the word problem of $\Gamma$. So $\Gamma$ has solvable word
> problem if and only if it is a subgroup of such a group with solvable word problem.

Section "LEF groups", l.486–487:

> Lemma~\ref{lem:halfline} keeps the Turing degree of the word problem in both steps.

## Proof route

Fix a finite generating family `s₀` of `Γ`. `lem:halfline` (a) (`HalflineA.manuscriptSentence_halflineEmbedding`)
gives an infinite finitely generated LEF group `Δ` with `Γ ↪ [Δ,Δ]` and `WP(t) ≤_T WP(s₀)` for every finite family
`t` of `Δ`. `lem:host` (`lamplighterHostStatement`) makes `G_Δ = EL_3(R_Δ)` a host with `[Δ,Δ] ↪ G_Δ`, and
`lem:halfline` (b) (`manuscriptSentence_halflineHostWordProblemReduction`) gives `WP(u) ≤_T WP(t)` for every finite
family `u` of `G_Δ` and generating `t` of `Δ`. The reverse inequalities are the substitution along the embeddings
(`printedWordProblemReducesUnderEmbedding`), and a change of generating family costs nothing
(`turingReducible_wordProblemOracle_of_generates`). So `WP(Γ) ≡_T WP(Δ) ≡_T WP(G_Δ)`.

Solvability: a group has solvable word problem iff its word problem is reducible to a computable oracle. A host
whose word problem has the degree of `WP(Γ)` has solvable word problem when `Γ` has; the converse half is
`LEFCorollaries.manuscriptSentence_solvableWordProblem_of_subgroupOfSolvableHost`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace LamplighterWP

open Lamplighter

/-- The embedding `Γ ↪ [Δ,Δ] ↪ G_Δ`. -/
theorem exists_host_embedding {Γ Δ : Type} [Group Γ] [Group Δ] (f : Γ →* Δ) (hf : Function.Injective f)
    (hcomm : ∀ γ, f γ ∈ commutator Δ) (g : ↥(commutator Δ) →* ↥(elementaryGroup (Fin 3) (LampRing Δ)))
    (hg : Function.Injective g) :
    ∃ e : Γ →* ↥(elementaryGroup (Fin 3) (LampRing Δ)), Function.Injective e :=
  ⟨g.comp (f.codRestrict (commutator Δ) hcomm), hg.comp fun _ _ hab => hf (congrArg Subtype.val hab)⟩

/-- **`cor:lef`, second statement** (tex l.456–458): every finitely generated LEF group `Γ` is a subgroup of an
infinite, finitely generated, simple Kazhdan expander limit of finite simple groups `SL_N(F₂)` whose word problem
has the Turing degree of the word problem of `Γ`, for any finite generating families. -/
theorem manuscriptSentence_lefHostWordProblemAbove (Γ : Type) [Group Γ] (hfg : Group.FG Γ)
    (hΓ : IsLEF Γ) :
    ∃ (E : Type) (_ : Group E), LEFCorollaries.IsExpanderLimitHost E ∧ ∃ f : Γ →* E, Function.Injective f ∧
      ∀ (κ ι : Type) [Primcodable κ] [Primcodable ι] [Finite κ] [Finite ι] (t : κ → Γ) (s : ι → E),
        Subgroup.closure (Set.range t) = ⊤ → Subgroup.closure (Set.range s) = ⊤ →
          TuringEquivalent (wordProblemOracle t) (wordProblemOracle s) := by
  obtain ⟨n, t0, ht0⟩ := exists_fin_generators Γ hfg
  obtain ⟨Δ, _, hinf, hfgΔ, hlef, ⟨f, hf, hcomm⟩, ⟨μ, _, _, u, hu⟩, hΔ⟩ :=
    HalflineA.manuscriptSentence_halflineEmbedding Γ (Fin n) t0 ht0 hΓ
  obtain ⟨hhost, g, hg⟩ := lamplighterHostStatement Δ hinf hfgΔ hlef
  obtain ⟨e, he⟩ := exists_host_embedding f hf hcomm g hg
  refine ⟨↥(elementaryGroup (Fin 3) (LampRing Δ)), inferInstance,
    LEFCorollaries.isExpanderLimitHost_of_isLEFHost hhost, e, he, ?_⟩
  intro κ ι _ _ _ _ t s ht hs
  exact ⟨printedWordProblemReducesUnderEmbedding Γ _ ι κ s t e he hs ht,
    (((manuscriptSentence_halflineHostWordProblemReduction Δ μ u hu).2 ι s).trans (hΔ μ u)).trans
      (turingReducible_wordProblemOracle_of_generates ht t0)⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.manuscriptSentence_lefHostWordProblemAbove

/-- **`cor:lef`, third statement** (tex l.458–460): a finitely generated group is LEF with solvable word problem if
and only if it is a subgroup of an infinite, finitely generated, simple Kazhdan expander limit of finite simple
groups `SL_N(F₂)` with solvable word problem. -/
theorem manuscriptSentence_solvableWordProblem_of_subgroupOfSolvableHost (Γ : Type) [Group Γ]
    (hfg : Group.FG Γ) :
    (IsLEF Γ ∧ HasSolvableWordProblem Γ) ↔
      ∃ (E : Type) (_ : Group E), LEFCorollaries.IsExpanderLimitHost E ∧ HasSolvableWordProblem E ∧
        ∃ f : Γ →* E, Function.Injective f := by
  constructor
  · rintro ⟨hΓ, ι, _, _, s, hs, hpart⟩
    obtain ⟨E, _, hE, f, hf, hdeg⟩ := manuscriptSentence_lefHostWordProblemAbove Γ hfg hΓ
    obtain ⟨n, u, hu⟩ := exists_fin_generators E hE.2.1
    exact ⟨E, inferInstance, hE, ⟨Fin n, inferInstance, inferInstance, u, hu,
      partrec_iff_forall_turingReducible.mpr fun o =>
        (hdeg ι (Fin n) s u hs hu).2.trans (partrec_iff_forall_turingReducible.mp hpart o)⟩, f, hf⟩
  · exact LEFCorollaries.manuscriptSentence_solvableWordProblem_of_subgroupOfSolvableHost Γ hfg

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.manuscriptSentence_solvableWordProblem_of_subgroupOfSolvableHost

/-- **`lem:halfline` keeps the Turing degree of the word problem in both steps** (tex l.486–487): for a finitely
generated LEF group `Γ`, the group `Δ` of `lem:halfline` (a), with `Γ ↪ [Δ,Δ]`, and the host `G_Δ` of `lem:host`,
with `[Δ,Δ] ↪ G_Δ`, satisfy `WP(Δ) ≡_T WP(Γ)` and `WP(G_Δ) ≡_T WP(Δ)`, for any finite generating families. -/
theorem manuscriptSentence_halflineKeepsTuringDegree (Γ : Type) [Group Γ] (hfg : Group.FG Γ)
    (hΓ : IsLEF Γ) :
    ∃ (Δ : Type) (_ : Group Δ), Infinite Δ ∧ Group.FG Δ ∧ IsLEF Δ ∧
      (∃ f : Γ →* Δ, Function.Injective f ∧ ∀ γ, f γ ∈ commutator Δ) ∧
      IsLEFHost ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
      (∃ g : ↥(commutator Δ) →* ↥(elementaryGroup (Fin 3) (LampRing Δ)), Function.Injective g) ∧
      ∀ (ι κ μ : Type) [Primcodable ι] [Primcodable κ] [Primcodable μ] [Finite ι] [Finite κ] [Finite μ]
        (s : ι → Γ) (t : κ → Δ) (u : μ → ↥(elementaryGroup (Fin 3) (LampRing Δ))),
        Subgroup.closure (Set.range s) = ⊤ → Subgroup.closure (Set.range t) = ⊤ →
          Subgroup.closure (Set.range u) = ⊤ →
            TuringEquivalent (wordProblemOracle t) (wordProblemOracle s) ∧
              TuringEquivalent (wordProblemOracle u) (wordProblemOracle t) := by
  obtain ⟨n, s0, hs0⟩ := exists_fin_generators Γ hfg
  obtain ⟨Δ, _, hinf, hfgΔ, hlef, ⟨f, hf, hcomm⟩, -, hΔ⟩ :=
    HalflineA.manuscriptSentence_halflineEmbedding Γ (Fin n) s0 hs0 hΓ
  obtain ⟨hhost, g, hg⟩ := lamplighterHostStatement Δ hinf hfgΔ hlef
  obtain ⟨e, he⟩ := exists_host_embedding f hf hcomm g hg
  refine ⟨Δ, inferInstance, hinf, hfgΔ, hlef, ⟨f, hf, hcomm⟩, hhost, ⟨g, hg⟩, ?_⟩
  intro ι κ μ _ _ _ _ _ _ s t u hs ht hu
  have htΓ : TuringReducible (wordProblemOracle t) (wordProblemOracle s) :=
    (hΔ κ t).trans (turingReducible_wordProblemOracle_of_generates hs s0)
  exact ⟨⟨htΓ, printedWordProblemReducesUnderEmbedding Γ Δ κ ι t s f hf ht hs⟩,
    ⟨(manuscriptSentence_halflineHostWordProblemReduction Δ κ t ht).2 μ u,
      htΓ.trans (printedWordProblemReducesUnderEmbedding Γ _ μ ι u s e he hu hs)⟩⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.manuscriptSentence_halflineKeepsTuringDegree

end LamplighterWP
end SimpleKazhdanSofic
end GroupApproximation
