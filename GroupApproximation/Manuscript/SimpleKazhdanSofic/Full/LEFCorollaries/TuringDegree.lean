import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LEFCorollaries.PrintedHost
import GroupApproximation.Manuscript.SimpleKazhdanSofic.TuringHost.Sentence
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFSolvableWordProblem
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Computability.TuringDegree

/-!
# `cor:lef`, second and third statements: Turing degree and solvable word problem

`simple_kazhdan_sofic_group.tex`, Corollary `cor:lef` (l.453–461):

> For every finitely generated LEF group `Γ` there is such a group containing `Γ` whose word problem
> has the Turing degree of the word problem of `Γ`. So `Γ` has solvable word problem if and only if it
> is a subgroup of such a group with solvable word problem.

## Spelling

* "Such a group" is `IsPrintedHost` (`PrintedHost.lean`): an infinite, finitely generated, simple
  Kazhdan group that is an expander limit, in the printed sense of tex l.92–100, of finite simple
  groups `SL_N(F₂)`.
* "Its word problem has the Turing degree of the word problem of `Γ`": for all finite generating
  families `t` of `Γ` and `s` of the host, `wordProblemOracle t` and `wordProblemOracle s` are Turing
  equivalent. The degree of the word problem does not depend on the generating family, and the
  statement quantifies over all of them.
* "Solvable word problem" is `HasSolvableWordProblem`: some finite generating family has a partial
  recursive word problem.

## Proof route

The second statement is TuringHost's closed `exists_isLEFHost_sameTuringDegree`, with its corpus host
converted by `isPrintedHost_of_isLEFHost`. The third follows from it as printed ("So"): a word problem
Turing equivalent to a computable one is computable, and conversely finitely generated subgroups of
groups with solvable word problem have solvable word problem (`printedSolvableWordProblemHeredity`).
-/

namespace GroupApproximation.Full.SK12

open GroupApproximation.SimpleKazhdanSofic

/-- **`cor:lef`, second statement** (tex l.456–458): every finitely generated LEF group `Γ` is a
subgroup of such a group whose word problem has the Turing degree of the word problem of `Γ`. -/
theorem corLef_hostWithSameTuringDegree (Γ : Type) [Group Γ] (hfg : Group.FG Γ)
    (hΓ : IsTextbookLEF Γ) :
    ∃ (E : Type) (_ : Group E), IsPrintedHost E ∧ ∃ f : Γ →* E, Function.Injective f ∧
      ∀ (κ ι : Type) [Primcodable κ] [Primcodable ι] [Finite κ] [Finite ι] (t : κ → Γ)
        (s : ι → E), Subgroup.closure (Set.range t) = ⊤ → Subgroup.closure (Set.range s) = ⊤ →
          TuringEquivalent (wordProblemOracle t) (wordProblemOracle s) := by
  obtain ⟨E, _, hE, f, hf, hdeg⟩ :=
    GroupApproximation.Manuscript.SimpleKazhdanSofic.TuringHost.exists_isLEFHost_sameTuringDegree
      Γ hfg ((isLEF_iff_textbook Γ).2 hΓ)
  exact ⟨E, inferInstance, isPrintedHost_of_isLEFHost hE, f, hf, hdeg⟩

#audit_axioms GroupApproximation.Full.SK12.corLef_hostWithSameTuringDegree

/-- **`cor:lef`, first and second statements in one equivalence** (tex l.454–458): a finitely
generated group is LEF if and only if it is a subgroup of such a group whose word problem has the
Turing degree of its own. -/
theorem corLef_lefIffSubgroupOfSameTuringDegreeHost (Γ : Type) [Group Γ] (hfg : Group.FG Γ) :
    IsTextbookLEF Γ ↔
      ∃ (E : Type) (_ : Group E), IsPrintedHost E ∧ ∃ f : Γ →* E, Function.Injective f ∧
        ∀ (κ ι : Type) [Primcodable κ] [Primcodable ι] [Finite κ] [Finite ι] (t : κ → Γ)
          (s : ι → E), Subgroup.closure (Set.range t) = ⊤ → Subgroup.closure (Set.range s) = ⊤ →
            TuringEquivalent (wordProblemOracle t) (wordProblemOracle s) := by
  refine ⟨corLef_hostWithSameTuringDegree Γ hfg, ?_⟩
  rintro ⟨E, _, hE, f, hf, -⟩
  exact isTextbookLEF_of_injective f hf (isTextbookLEF_of_isPrintedHost hE)

#audit_axioms GroupApproximation.Full.SK12.corLef_lefIffSubgroupOfSameTuringDegreeHost

/-- **`cor:lef`, third statement** (tex l.458–460): a finitely generated LEF group `Γ` has solvable
word problem if and only if it is a subgroup of such a group with solvable word problem. -/
theorem corLef_solvableWordProblemIffSubgroupOfHost (Γ : Type) [Group Γ] (hfg : Group.FG Γ)
    (hΓ : IsTextbookLEF Γ) :
    HasSolvableWordProblem Γ ↔
      ∃ (E : Type) (_ : Group E), IsPrintedHost E ∧ HasSolvableWordProblem E ∧
        ∃ f : Γ →* E, Function.Injective f := by
  constructor
  · rintro ⟨ι, _, _, t, ht, hpart⟩
    obtain ⟨E, _, hE, f, hf, hdeg⟩ := corLef_hostWithSameTuringDegree Γ hfg hΓ
    have hEfg : Group.FG E := hE.2.1
    obtain ⟨n, u, hu⟩ := exists_fin_generators E hEfg
    obtain ⟨-, hred⟩ := hdeg ι (Fin n) t u ht hu
    refine ⟨E, inferInstance, hE, ⟨Fin n, inferInstance, inferInstance, u, hu, ?_⟩, f, hf⟩
    exact partrec_iff_forall_turingReducible.mpr fun o =>
      TuringReducible.trans hred (partrec_iff_forall_turingReducible.mp hpart o)
  · rintro ⟨E, _, -, hswpE, f, hf⟩
    exact printedSolvableWordProblemHeredity Γ E hfg hswpE f hf

#audit_axioms GroupApproximation.Full.SK12.corLef_solvableWordProblemIffSubgroupOfHost

/-- **`cor:lef`, third statement, without the standing hypothesis**: a finitely generated group is
LEF with solvable word problem if and only if it is a subgroup of such a group with solvable word
problem. -/
theorem corLef_lefSolvableWordProblemIffSubgroupOfHost (Γ : Type) [Group Γ] (hfg : Group.FG Γ) :
    (IsTextbookLEF Γ ∧ HasSolvableWordProblem Γ) ↔
      ∃ (E : Type) (_ : Group E), IsPrintedHost E ∧ HasSolvableWordProblem E ∧
        ∃ f : Γ →* E, Function.Injective f := by
  constructor
  · rintro ⟨hΓ, hswp⟩
    exact (corLef_solvableWordProblemIffSubgroupOfHost Γ hfg hΓ).1 hswp
  · rintro ⟨E, _, hE, hswpE, f, hf⟩
    have hΓ : IsTextbookLEF Γ := isTextbookLEF_of_injective f hf (isTextbookLEF_of_isPrintedHost hE)
    exact ⟨hΓ, (corLef_solvableWordProblemIffSubgroupOfHost Γ hfg hΓ).2
      ⟨E, inferInstance, hE, hswpE, f, hf⟩⟩

#audit_axioms GroupApproximation.Full.SK12.corLef_lefSolvableWordProblemIffSubgroupOfHost

end GroupApproximation.Full.SK12
