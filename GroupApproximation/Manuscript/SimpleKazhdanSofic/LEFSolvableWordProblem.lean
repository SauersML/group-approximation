import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCharacterization
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemDegreeInvariant
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Computability.TuringDegree

/-!
# The second statement of `cor:lef`: LEF groups with solvable word problem

`simple_kazhdan_sofic_group.tex` at origin/main 696c4b602.

> **Corollary (`cor:lef`), second statement** (tex l.317–319). It is LEF with solvable word
> problem if and only if it is a subgroup of such a group with solvable word problem.

The proof (tex l.439–459) takes the second choice of `Δ` and shows that `Δ` has solvable word
problem. The word problem of `Δ` decides equality in `Λ`, so `G_Δ` has solvable word problem, and:

> Conversely, finitely generated subgroups of groups with solvable word problem have solvable word
> problem, and LEF passes to subgroups.

## Spelling

* `HasSolvableWordProblem Γ`: some finite generating family `s` has a computable word problem,
  `Partrec (wordProblemOracle s)`, with skf-degrees' `wordProblemOracle`. This is the spelling
  agreed with skf-degrees.
* `PrintedLEFSolvableWordProblemCharacterization`: the second statement of `cor:lef`.
* `PrintedSolvableWordProblemHeredity`: tex l.456–457, proved as
  `printedSolvableWordProblemHeredity` through skf-degrees' `wordProblemOracle_comp_injective` and
  `turingReducible_wordProblemOracle_of_generates`.
* The pieces are `LEFSolvableWordProblemEmbeddingStatement` (the second choice of `Δ`, tex l.358–382
  and l.439–444) and `LEFLamplighterSolvableWordProblemStatement` (tex l.444–455).
  `printedLEFSolvableWordProblemCharacterization_of_pieces` assembles them.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

/-! ## Statements -/

/-- **Solvable word problem**: some finite generating family has a computable word problem. -/
def HasSolvableWordProblem (Γ : Type) [Group Γ] : Prop :=
  ∃ (ι : Type) (_ : Primcodable ι) (_ : Finite ι) (s : ι → Γ),
    Subgroup.closure (Set.range s) = ⊤ ∧ Partrec (wordProblemOracle s)

/-- **`cor:lef`, second statement** (tex l.317–319). -/
def PrintedLEFSolvableWordProblemCharacterization : Prop :=
  ∀ (Γ : Type) [Group Γ], Group.FG Γ →
    ((IsLEF Γ ∧ HasSolvableWordProblem Γ) ↔
      ∃ (E : Type) (_ : Group E), IsLEFHost E ∧ HasSolvableWordProblem E ∧
        ∃ f : Γ →* E, Function.Injective f)

/-- **Finitely generated subgroups of groups with solvable word problem have solvable word
problem** (tex l.456–457). -/
def PrintedSolvableWordProblemHeredity : Prop :=
  ∀ (Γ E : Type) [Group Γ] [Group E], Group.FG Γ → HasSolvableWordProblem E →
    ∀ f : Γ →* E, Function.Injective f → HasSolvableWordProblem Γ

/-! ## Pieces -/

/-- **The second choice of `Δ`** (tex l.358–382 and l.439–444): a finitely generated LEF group
with solvable word problem embeds in the commutator subgroup of an infinite finitely generated LEF
group with solvable word problem. -/
def LEFSolvableWordProblemEmbeddingStatement : Prop :=
  ∀ (Γ : Type) [Group Γ], Group.FG Γ → IsLEF Γ → HasSolvableWordProblem Γ →
    ∃ (Δ : Type) (_ : Group Δ), Infinite Δ ∧ Group.FG Δ ∧ IsLEF Δ ∧ HasSolvableWordProblem Δ ∧
      ∃ f : Γ →* Δ, Function.Injective f ∧ ∀ γ, f γ ∈ commutator Δ

/-- **`G_Δ` has solvable word problem** (tex l.444–455): for an infinite finitely generated LEF
group `Δ` with solvable word problem, the lamplighter host `G_Δ` has solvable word problem, and
`[Δ,Δ]` embeds in it. -/
def LEFLamplighterSolvableWordProblemStatement : Prop :=
  ∀ (Δ : Type) [Group Δ], Infinite Δ → Group.FG Δ → IsLEF Δ → HasSolvableWordProblem Δ →
    ∃ (E : Type) (_ : Group E), IsLEFHost E ∧ HasSolvableWordProblem E ∧
      ∃ f : ↥(commutator Δ) →* E, Function.Injective f

/-! ## Heredity -/

/-- A finitely generated group has a generating family indexed by some `Fin n`. -/
theorem exists_fin_generators (Γ : Type) [Group Γ] (h : Group.FG Γ) :
    ∃ (n : ℕ) (t : Fin n → Γ), Subgroup.closure (Set.range t) = ⊤ := by
  obtain ⟨S, hS⟩ := Group.fg_def.mp h
  refine ⟨Fintype.card ↥S, fun i => ((Fintype.equivFin ↥S).symm i : Γ), ?_⟩
  have hrange : Set.range (fun i => ((Fintype.equivFin ↥S).symm i : Γ)) = (S : Set Γ) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin ↥S).symm i).2
    · intro hx
      exact ⟨Fintype.equivFin ↥S ⟨x, hx⟩, by simp⟩
  rw [hrange]
  exact hS

/-- **Finitely generated subgroups of groups with solvable word problem have solvable word
problem** (tex l.456–457). -/
theorem printedSolvableWordProblemHeredity : PrintedSolvableWordProblemHeredity := by
  intro Γ E _ _ hfg hE f hf
  obtain ⟨ι, _, _, s, hs, hpart⟩ := hE
  obtain ⟨n, t, ht⟩ := exists_fin_generators Γ hfg
  have heq : wordProblemOracle (⇑f ∘ t) = wordProblemOracle t :=
    wordProblemOracle_comp_injective t f hf
  have hred : TuringReducible (wordProblemOracle (⇑f ∘ t)) (wordProblemOracle s) :=
    turingReducible_wordProblemOracle_of_generates hs (⇑f ∘ t)
  rw [heq] at hred
  refine ⟨Fin n, inferInstance, inferInstance, t, ht, ?_⟩
  exact partrec_iff_forall_turingReducible.mpr fun o =>
    TuringReducible.trans hred (partrec_iff_forall_turingReducible.mp hpart o)

/-! ## Assembly -/

/-- **The second statement of `cor:lef` from its pieces** (tex l.439–459). -/
theorem printedLEFSolvableWordProblemCharacterization_of_pieces
    (hultra : LEFSolvableWordProblemEmbeddingStatement)
    (hlamp : LEFLamplighterSolvableWordProblemStatement) :
    PrintedLEFSolvableWordProblemCharacterization := by
  intro Γ _ hfg
  constructor
  · rintro ⟨hΓ, hswp⟩
    obtain ⟨Δ, _, hinf, hfgΔ, hlefΔ, hswpΔ, φ, hφ, hmem⟩ := hultra Γ hfg hΓ hswp
    obtain ⟨E, _, hE, hswpE, ψ, hψ⟩ := hlamp Δ hinf hfgΔ hlefΔ hswpΔ
    refine ⟨E, inferInstance, hE, hswpE, ψ.comp (φ.codRestrict (commutator Δ) hmem), ?_⟩
    intro x y hxy
    have h1 : ψ (φ.codRestrict (commutator Δ) hmem x) =
        ψ (φ.codRestrict (commutator Δ) hmem y) := hxy
    exact hφ (congrArg Subtype.val (hψ h1))
  · rintro ⟨E, _, hE, hswpE, f, hf⟩
    exact ⟨isLEF_of_embeds_isLEFHost hE f hf,
      printedSolvableWordProblemHeredity Γ E hfg hswpE f hf⟩

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedSolvableWordProblemHeredity
#audit_axioms GroupApproximation.SimpleKazhdanSofic.exists_fin_generators
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedLEFSolvableWordProblemCharacterization_of_pieces

end SimpleKazhdanSofic
end GroupApproximation
