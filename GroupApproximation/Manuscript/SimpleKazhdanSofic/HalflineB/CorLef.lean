import GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.Reduction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterHost
import GroupApproximation.Meta.AxiomGuard

/-!
# The second statement of `cor:lef` from `lem:halfline`

`simple_kazhdan_sofic_group.tex`, proof of the second statement of `cor:lef`:

* tex l.669, sentence 220c5bae8ae9:
  > Let Γ be a finitely generated LEF group.
* tex l.669–672, sentence 854c69bf6b59:
  > By Lemmas lem:halfline and lem:host, Γ is a subgroup of a group G_Δ as in Corollary cor:lef whose word problem
  > is Turing reducible to that of Γ.
* tex l.672–675, sentence edd233afbf7b:
  > Conversely, a word in the generators of Γ becomes a word in the generators of G_Δ by substitution, and it is
  > trivial in Γ if and only if its image is trivial in G_Δ, so the word problem of Γ reduces to that of G_Δ.
* tex l.676–678, sentence 2864647b9987:
  > The last statement follows, as finitely generated subgroups of groups with solvable word problem have solvable
  > word problem and LEF passes to subgroups.

## Proof route

* `lem:halfline` (a) (`HalflineA.manuscriptSentence_halflineEmbedding`) embeds `Γ` in `[Δ,Δ]` for an infinite
  finitely generated LEF group `Δ` whose word problem reduces to that of `Γ`; `lem:host`
  (`isLEFHost_lampRing`, `exists_commutator_embedding`) makes `G_Δ` a host containing `[Δ,Δ]`, and `lem:halfline` (b)
  (`manuscriptSentence_hostWordProblemReduction`) reduces the word problem of `G_Δ` to that of `Δ`.
* The converse reduction is substitution (`manuscriptSentence_corLefSubstitution`).
* The last statement: forward by the host above, whose word problem is then computable; backward by the two
  heredity facts (`manuscriptSentence_corLefHeredity`, `isLEF_of_embeds_isLEFHost`).
-/

namespace GroupApproximation
namespace Manuscript
namespace SimpleKazhdanSofic
namespace HalflineB

open GroupApproximation.SimpleKazhdanSofic GroupApproximation.SimpleKazhdanSofic.Lamplighter

/-- **`Γ` is a subgroup of a host `G_Δ` with mutually reducible word problems** (tex l.669–675). Let `Γ` be a finitely
generated LEF group with finite generating family `s`. There is a group `Δ` such that `G_Δ = EL_3(R_Δ)` is a group as
in `cor:lef`, `Γ` embeds in `G_Δ`, the word problem of `Γ` in `s` reduces to that of `G_Δ` in any finite generating
family, and the word problem of `G_Δ` in any finite family reduces to that of `Γ` in `s`. -/
theorem manuscriptSentence_corLefHostReduction (Γ : Type) [Group Γ] (ι : Type) [Primcodable ι] [Finite ι]
    (s : ι → Γ) (hs : Subgroup.closure (Set.range s) = ⊤) (hLEF : IsLEF Γ) :
    ∃ (Δ : Type) (_ : Group Δ), IsLEFHost ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
      (∃ f : Γ →* ↥(elementaryGroup (Fin 3) (LampRing Δ)), Function.Injective f ∧
        ∀ (κ : Type) [Primcodable κ] [Finite κ] (u : κ → ↥(elementaryGroup (Fin 3) (LampRing Δ))),
          Subgroup.closure (Set.range u) = ⊤ → TuringReducible (wordProblemOracle s) (wordProblemOracle u)) ∧
      ∀ (κ : Type) [Primcodable κ] [Finite κ] (u : κ → ↥(elementaryGroup (Fin 3) (LampRing Δ))),
        TuringReducible (wordProblemOracle u) (wordProblemOracle s) := by
  obtain ⟨Δ, _, _, hfg, hlef, ⟨f, hf, hcomm⟩, ⟨κ0, _, _, t, ht⟩, hred⟩ :=
    GroupApproximation.SimpleKazhdanSofic.HalflineA.manuscriptSentence_halflineEmbedding Γ ι s hs hLEF
  obtain ⟨g, hg⟩ := exists_commutator_embedding Δ
  have hemb : Function.Injective (g.comp (f.codRestrict (commutator Δ) hcomm)) := by
    intro x y hxy
    have h1 : g (f.codRestrict (commutator Δ) hcomm x) = g (f.codRestrict (commutator Δ) hcomm y) := hxy
    exact hf (congrArg Subtype.val (hg h1))
  refine ⟨Δ, inferInstance, isLEFHost_lampRing Δ hfg hlef,
    ⟨g.comp (f.codRestrict (commutator Δ) hcomm), hemb, ?_⟩, ?_⟩
  · intro κ _ _ u hu
    exact (manuscriptSentence_corLefSubstitution (g.comp (f.codRestrict (commutator Δ) hcomm)) hemb s hu).2
  · intro κ _ _ u
    exact TuringReducible.trans (manuscriptSentence_hostWordProblemReduction t ht u) (hred κ0 t)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_corLefHostReduction

/-- **The last statement of `cor:lef`** (tex l.676–678): a finitely generated group is LEF with solvable word problem
if and only if it is a subgroup of a group as in `cor:lef` with solvable word problem. -/
theorem manuscriptSentence_corLefLastStatement (Γ : Type) [Group Γ] (hfg : Group.FG Γ) :
    (IsLEF Γ ∧ HasSolvableWordProblem Γ) ↔
      ∃ (E : Type) (_ : Group E), IsLEFHost E ∧ HasSolvableWordProblem E ∧
        ∃ f : Γ →* E, Function.Injective f := by
  constructor
  · rintro ⟨hLEF, ι, _, _, s, hs, hpart⟩
    obtain ⟨Δ, _, hhost, ⟨f, hf, -⟩, hred⟩ := manuscriptSentence_corLefHostReduction Γ ι s hs hLEF
    have hEfg : Group.FG ↥(elementaryGroup (Fin 3) (LampRing Δ)) := by
      obtain ⟨-, h, -⟩ := hhost
      exact h
    obtain ⟨n, u, hu⟩ := exists_fin_generators _ hEfg
    refine ⟨↥(elementaryGroup (Fin 3) (LampRing Δ)), inferInstance, hhost,
      ⟨Fin n, inferInstance, inferInstance, u, hu, ?_⟩, f, hf⟩
    exact partrec_iff_forall_turingReducible.mpr fun o =>
      TuringReducible.trans (hred (Fin n) u) (partrec_iff_forall_turingReducible.mp hpart o)
  · rintro ⟨E, _, hE, hswpE, f, hf⟩
    exact ⟨isLEF_of_embeds_isLEFHost hE f hf, (manuscriptSentence_corLefHeredity Γ E f hf).1 hfg hswpE⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_corLefLastStatement

/-- The printed second statement of `cor:lef`, `PrintedLEFSolvableWordProblemCharacterization`. -/
theorem printedLEFSolvableWordProblemCharacterization_halflineB :
    PrintedLEFSolvableWordProblemCharacterization :=
  fun Γ _ hfg => manuscriptSentence_corLefLastStatement Γ hfg

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.printedLEFSolvableWordProblemCharacterization_halflineB

end HalflineB
end SimpleKazhdanSofic
end Manuscript
end GroupApproximation
