import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCorollaries.ExpanderLimitHosts
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemsCorollaryAssembly
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFSolvableWordProblem
import GroupApproximation.Meta.AxiomGuard

/-!
# Word problems of the hosts, and the Sacks antichain

`simple_kazhdan_sofic_group.tex` (current text, commit 1eefb3bbb), `cor:lef`, l.456–460:

> For every finitely generated LEF group $\Gamma$ there is such a group containing $\Gamma$ whose
> word problem has the Turing degree of the word problem of $\Gamma$. So $\Gamma$ has solvable word
> problem if and only if it is a subgroup of such a group with solvable word problem.

Section "LEF groups", l.483–487:

> We embed a countable LEF group in the derived subgroup of a $2$-generated LEF group $\Delta$
> (Lemma~\ref{lem:nn}), and then $[\Delta,\Delta]$ in a group of Theorem~\ref{thm:general}(b) built
> from a lamplighter action of $\Delta$ (Lemma~\ref{lem:host}). Lemma~\ref{lem:halfline} keeps the
> Turing degree of the word problem in both steps.

Proof of `cor:wp`, l.719–721:

> By a construction of Sacks, the Turing degrees contain an antichain of size continuum, and the
> groups $G_{X_\alpha}$ with $\alpha$ of these degrees are as claimed.

## What is proved here

* `manuscriptSentence_lefHostWordProblemAbove`: every finitely generated LEF `Γ` lies in a host `E`
  (as in `ExpanderLimitHosts`) whose word problem computes that of `Γ`, for all finite generating
  families of both groups. This is the lower-bound half of l.456–458. The upper bound, that `Γ`
  computes the word problem of the host, is not proved (see below).
* `manuscriptSentence_solvableWordProblem_of_subgroupOfSolvableHost`: the "if" half of l.458–460.
  A finitely generated subgroup of a host with solvable word problem is LEF and has solvable word
  problem.
* `manuscriptSentence_sacksAntichainGroups`: l.719–721, whole. There is an antichain `F` of Turing
  degrees of size continuum, and slopes `α B` of the degrees `B`. The subshifts `X_{α B}`,
  `B ∈ F`, are infinite and minimal, there are continuum many of them, and `G_{X_{α B}}` embeds in
  `G_{X_{α C}}` only if `B = C`.

## Proof route

* The lower bound substitutes words (`printedWordProblemReducesUnderEmbedding`, closed) into the host
  from `manuscriptSentence_lefIffSubgroupOfExpanderLimitHost`.
* Heredity is `printedSolvableWordProblemHeredity` (closed), and LEF passes to subgroups.
* Sacks: `printedTuringAntichainContinuum` (closed). Each set `B` is the degree of the continued fraction
  `[0; 1 + χ_B(0), …]` (`printedContinuedFractionRepresentative`, closed), which lies in `(0,1)`.
  The Sturmian subshift of that slope is infinite and minimal (`printedSturmianSubshiftInfiniteIsMinimal`),
  `WP(G_X) ≡_T L(X)` (`printedWordProblemDegreeEqLanguage`, closed), and `L(X_α) ≡_T α`
  (`SturmianComputability`). An embedding reduces word problems, so it forces `B ≤_T C`, hence `B = C`.

## Remaining gap

The upper bound `WP(G_Δ) ≤_T WP(Δ)` for the lamplighter host (`lem:halfline`(b), the named Prop
`Lamplighter.PrintedLamplighterHostSolvableWordProblem`) is not proved in the corpus. Without it
neither the Turing-degree statement nor the "only if" half of the solvable word problem statement
closes.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace LEFCorollaries

open SymbolicDynamics.FullShift Set SturmianComputability

/-! ## `cor:lef`, second and third statements: the closed halves -/

/-- **`cor:lef`, second statement, lower bound** (tex l.456–458): every finitely generated LEF group
`Γ` is a subgroup of an infinite, finitely generated, simple Kazhdan expander limit of finite simple
groups `SL_N(F₂)` whose word problem computes the word problem of `Γ`, for any finite generating
families. -/
theorem manuscriptSentence_lefHostWordProblemAbove (Γ : Type) [Group Γ] (hfg : Group.FG Γ)
    (hΓ : IsLEF Γ) :
    ∃ (E : Type) (_ : Group E), IsExpanderLimitHost E ∧ ∃ f : Γ →* E, Function.Injective f ∧
      ∀ (κ ι : Type) [Primcodable κ] [Primcodable ι] [Finite κ] [Finite ι] (t : κ → Γ) (s : ι → E),
        Subgroup.closure (range t) = ⊤ → Subgroup.closure (range s) = ⊤ →
          TuringReducible (wordProblemOracle t) (wordProblemOracle s) := by
  obtain ⟨E, _, hE, f, hf⟩ := (manuscriptSentence_lefIffSubgroupOfExpanderLimitHost Γ hfg).1 hΓ
  refine ⟨E, inferInstance, hE, f, hf, ?_⟩
  intro κ ι _ _ _ _ t s ht hs
  exact printedWordProblemReducesUnderEmbedding Γ E ι κ s t f hf hs ht

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFCorollaries.manuscriptSentence_lefHostWordProblemAbove

/-- **`cor:lef`, third statement, "if" half** (tex l.458–460): a finitely generated subgroup of an
infinite, finitely generated, simple Kazhdan expander limit of finite simple groups `SL_N(F₂)` with
solvable word problem is LEF and has solvable word problem. -/
theorem manuscriptSentence_solvableWordProblem_of_subgroupOfSolvableHost (Γ : Type) [Group Γ]
    (hfg : Group.FG Γ)
    (h : ∃ (E : Type) (_ : Group E), IsExpanderLimitHost E ∧ HasSolvableWordProblem E ∧
      ∃ f : Γ →* E, Function.Injective f) :
    IsLEF Γ ∧ HasSolvableWordProblem Γ := by
  obtain ⟨E, _, hE, hswp, f, hf⟩ := h
  exact ⟨isLEF_of_injective f hf (isLEF_of_isExpanderLimitHost hE),
    printedSolvableWordProblemHeredity Γ E hfg hswp f hf⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFCorollaries.manuscriptSentence_solvableWordProblem_of_subgroupOfSolvableHost

/-! ## Proof of `cor:wp`: the Sacks antichain -/

/-- **Proof of `cor:wp`, last sentence** (tex l.719–721): the Turing degrees contain an antichain `F`
of size continuum. Choose slopes `α B ∈ (0,1)` of the degrees `B ∈ F`. Then the groups
`G_{X_{α B}}` are as claimed: the subshifts are infinite and minimal, there are continuum many of
them, and none of the groups embeds in another. -/
theorem manuscriptSentence_sacksAntichainGroups :
    ∃ F : Set (Set ℕ), Cardinal.mk F = Cardinal.continuum ∧
      (∀ B ∈ F, ∀ C ∈ F, TuringReducible (charOracle B) (charOracle C) → B = C) ∧
      ∃ α : Set ℕ → ℝ,
        (∀ B, Irrational (α B) ∧ 0 < α B ∧ α B < 1 ∧
          TuringEquivalent (slopeOracle (α B)) (charOracle B)) ∧
        Cardinal.mk ((fun B => sturmianSubshift (α B)) '' F) = Cardinal.continuum ∧
        (∀ B ∈ F, Infinite (sturmianSubshift (α B)).carrier ∧ IsMinimal (sturmianSubshift (α B))) ∧
        ∀ B ∈ F, ∀ C ∈ F,
          (∃ ψ : G (sturmianSubshift (α B)) →* G (sturmianSubshift (α C)),
            Function.Injective ψ) → B = C := by
  classical
  haveI : Finite (Coeff Bool) := Finite.of_equiv _ (Coeff.equivOption Bool).symm
  obtain ⟨F, hF, hanti⟩ := printedTuringAntichainContinuum
  have hdeg : ∀ B : Set ℕ, ∃ α : ℝ, Irrational α ∧ 0 < α ∧ α < 1 ∧
      TuringEquivalent (slopeOracle α) (charOracle B) := fun B => by
    obtain ⟨α, hcf, hirr, heq⟩ := printedContinuedFractionRepresentative B
    have hfl : ⌊α⌋ = 0 := by
      have h := hcf.1
      rw [GenContFract.of_h_eq_floor] at h
      exact_mod_cast h
    obtain ⟨h0, h1⟩ := Int.floor_eq_zero_iff.1 hfl
    exact ⟨α, hirr, lt_of_le_of_ne h0 (Ne.symm hirr.ne_zero), h1, heq⟩
  choose α hα using hdeg
  have hmin : ∀ B, (sturmianSubshift (α B)).carrier.Infinite ∧ IsMinimal (sturmianSubshift (α B)) :=
    fun B => printedSturmianSubshiftInfiniteIsMinimal (α B) (hα B).1 (hα B).2.1 (hα B).2.2.1
  have hWP : ∀ B, TuringEquivalent (wordProblemOracle (genValue (sturmianSubshift (α B))))
      (charOracle B) := fun B => by
    obtain ⟨hirr, hpos, hlt, hχ⟩ := hα B
    have hWL := printedWordProblemDegreeEqLanguage Bool (sturmianSubshift (α B))
      (hmin B).1.to_subtype (hmin B).2
    have hLα : TuringEquivalent (languageOracle (sturmianSubshift (α B))) (slopeOracle (α B)) :=
      ⟨printedSlopeComputesSturmianLanguage (α B) hirr hpos hlt,
        printedSturmianLanguageComputesSlope (α B) hirr hpos hlt⟩
    exact TuringEquivalent.trans _ _ _ (TuringEquivalent.trans _ _ _ hWL hLα) hχ
  have hinj : InjOn (fun B => sturmianSubshift (α B)) F := by
    intro B hB C hC hBC
    have hBC' : sturmianSubshift (α B) = sturmianSubshift (α C) := hBC
    have e : wordProblemOracle (genValue (sturmianSubshift (α B))) =
        wordProblemOracle (genValue (sturmianSubshift (α C))) :=
      congrArg (fun S : Subshift Bool ℤ => wordProblemOracle (genValue S)) hBC'
    exact hanti B hB C hC ((hWP B).2.trans (by rw [e]; exact (hWP C).1))
  refine ⟨F, hF, hanti, α, hα, ?_, fun B _ => ⟨(hmin B).1.to_subtype, (hmin B).2⟩, ?_⟩
  · rw [Cardinal.mk_image_eq_of_injOn _ _ hinj, hF]
  · rintro B hB C hC ⟨ψ, hψ⟩
    have hred := printedWordProblemReducesUnderEmbedding (G (sturmianSubshift (α B)))
      (G (sturmianSubshift (α C))) (Gen Bool) (Gen Bool) (genValue (sturmianSubshift (α C)))
      (genValue (sturmianSubshift (α B))) ψ hψ (closure_range_genValue _) (closure_range_genValue _)
    exact hanti B hB C hC ((hWP B).2.trans (hred.trans (hWP C).1))

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LEFCorollaries.manuscriptSentence_sacksAntichainGroups

end LEFCorollaries
end SimpleKazhdanSofic
end GroupApproximation
