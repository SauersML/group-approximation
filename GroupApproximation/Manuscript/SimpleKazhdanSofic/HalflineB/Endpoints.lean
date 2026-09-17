import GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineA.Embedding
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterAffineWordProblemPrimrec
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFSolvableWordProblem
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:halfline`: the end of (a), the `Λ` step of (b), and the ingredients of `cor:lef`

`simple_kazhdan_sofic_group.tex`, proof of `lem:halfline` and of the second statement of `cor:lef`:

* tex l.645, sentence 12a3a964a4e0:
  > Therefore Δ is LEF.
* tex l.647–652, sentence 0b12bb409f63:
  > From a word in the β^{±1} and h_γ^{±1} one computes the exponent sum ℓ of β, the levels where f changes, namely
  > the exponent sums of β before the letters h_γ^{±1}, and the values of f there as words in E. It is trivial if
  > and only if ℓ=0 and these values are trivial in Γ, so the word problem of Δ is Turing reducible to that of Γ.
* tex l.654–657, sentence 3c71f1b21217:
  > For (b), an element x ↦ δx+c of Λ is given by a word for δ and words for the points of supp c, so an oracle for
  > the word problem of Δ decides equality in Λ and computes the values of c.
* tex l.672–675, sentence edd233afbf7b:
  > Conversely, a word in the generators of Γ becomes a word in the generators of G_Δ by substitution, and it is
  > trivial in Γ if and only if its image is trivial in G_Δ, so the word problem of Γ reduces to that of G_Δ.
* tex l.676–678, sentence 2864647b9987 (ingredients; the assembled last statement is in `HalflineB.CorLef`):
  > The last statement follows, as finitely generated subgroups of groups with solvable word problem have solvable
  > word problem and LEF passes to subgroups.

## Proof route

* `Δ = levelDelta Γ E` is LEF: `LevelShiftDelta.isTextbookLEF_levelDelta` and `isLEF_iff_textbook`.
* A word `w` in `β^{±1}`, `h_γ^{±1}` is trivial iff its exponent sums of `β` agree (`shiftPair`) and the value words
  `valueWord w (tagLevel p)` at the tags of its `h`-letters are trivial in `Γ` (`gValue_eq_one_iff_tags`). The
  truth-table reduction is `HalflineA.turingReducible_wordProblemOracle_levelGen`.
* An element of `Λ` given by a word `w` is `inl c · inr δ` with `δ` the value of `deltaWord w` and `c` the parity of the
  prefix values (`wordValue_lampGen`, `lampSum_apply`). The truth-table reduction is `affineOracle_eq` with
  `primrec_affineQueries` and `primrec_affineDecide`.
* Substitution: `wordValue_map`, `wordProblemOracle_comp_injective`, `turingReducible_wordProblemOracle_of_generates`.
* Heredity: `printedSolvableWordProblemHeredity` and `isLEF_of_injective`.
-/

namespace GroupApproximation
namespace Manuscript
namespace SimpleKazhdanSofic
namespace HalflineB

open GroupApproximation.SimpleKazhdanSofic GroupApproximation.SimpleKazhdanSofic.Lamplighter
open GroupApproximation.LevelShiftDelta Multiplicative

/-- **Therefore `Δ` is LEF** (tex l.645): for a LEF group `Γ` and a finite set `E ⊆ Γ`, the group
`Δ = ⟨β, h_γ : γ ∈ E⟩` is LEF. -/
theorem manuscriptSentence_halflineDeltaIsLEF {Γ : Type*} [Group Γ] (hLEF : IsLEF Γ) (E : Finset Γ) :
    IsLEF ↥(levelDelta Γ E) :=
  (isLEF_iff_textbook _).2 (isTextbookLEF_levelDelta ((isLEF_iff_textbook Γ).1 hLEF) E)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_halflineDeltaIsLEF

/-- **The word problem of `Δ` reduces to that of `Γ`** (tex l.647–652). A word `w` in `β^{±1}` (`none`) and
`h_{s i}^{±1}` (`some i`) is trivial iff the exponent sum of `β` is `0` (the raises equal the lowers) and the value
of `f` at every level where it changes, as a word in `E`, is trivial in `Γ`. The word problem of these generators of
`Δ` is Turing reducible to the word problem of `Γ` in `s`. -/
theorem manuscriptSentence_halflineDeltaWordProblem {Γ : Type*} [Group Γ] {ι : Type*} [Primcodable ι]
    (s : ι → Γ) :
    (∀ w : List (Option ι × Bool), wordValue (levelGen s) w = 1 ↔
      (shiftPair w).1 = (shiftPair w).2 ∧
        ∀ p ∈ hLetters w, wordValue s (valueWord w (tagLevel p.1)) = 1) ∧
      TuringReducible (wordProblemOracle (levelGen s)) (wordProblemOracle s) := by
  refine ⟨fun w => ?_,
    GroupApproximation.SimpleKazhdanSofic.HalflineA.turingReducible_wordProblemOracle_levelGen s⟩
  rw [GroupApproximation.SimpleKazhdanSofic.LevelShiftDeltaWordProblem.wordValue_levelGen,
    gValue_eq_one_iff_tags]
  simp only [GroupApproximation.SimpleKazhdanSofic.LevelShiftDeltaWordProblem.wordValue_eq_lValue]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_halflineDeltaWordProblem

/-- **The reduction for `Λ`** (tex l.654–657), for any finite family `t` of `Δ`. The element of `Λ` given by a word
`w` in `z` (`none`) and `t` is `x ↦ δx + c`: `inl c · inr δ`, with `δ` the value of the `Δ`-letters of `w` and
`c(a)` the parity of the prefixes in front of the `z`-letters with value `a`. So the word problem of `Λ` in these
generators is Turing reducible to that of `Δ` in `t`. -/
theorem manuscriptSentence_halflineLambdaWordProblem {Δ : Type} [Group Δ] {ι : Type} [Primcodable ι] [Finite ι]
    (t : ι → Δ) :
    (∀ w : List (Option ι × Bool), wordValue (lampGen t) w =
      SemidirectProduct.inl (ofAdd (lampSum t w)) * SemidirectProduct.inr (wordValue t (deltaWord w))) ∧
    (∀ [DecidableEq Δ] (w : List (Option ι × Bool)) (a : Δ),
      lampSum t w a = (((lampPrefixes w).filter fun p => wordValue t p = a).length : ZMod 2)) ∧
      TuringReducible (wordProblemOracle (lampGen t)) (wordProblemOracle t) := by
  refine ⟨wordValue_lampGen t, fun w a => lampSum_apply t w a, ?_⟩
  classical
  exact OracleTruthTable.turingReducible_of_truthTable (gt := deltaAnswer t) (fun _ => rfl)
    primrec_affineQueries primrec_affineDecide (affineOracle_eq t)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_halflineLambdaWordProblem

/-- **Substitution** (tex l.672–675). Let `f : Γ →* G` be injective, `s` a finite family of `Γ` and `u` a finite
generating family of `G`. A word in `s` is trivial in `Γ` iff its image under substitution (a word in `f ∘ s`) is
trivial in `G`, and the word problem of `Γ` in `s` is Turing reducible to that of `G` in `u`. -/
theorem manuscriptSentence_corLefSubstitution {Γ G : Type*} [Group Γ] [Group G] (f : Γ →* G)
    (hf : Function.Injective f) {ι : Type*} [Primcodable ι] [Finite ι] (s : ι → Γ) {κ : Type*} [Primcodable κ]
    {u : κ → G} (hu : Subgroup.closure (Set.range u) = ⊤) :
    (∀ w : List (ι × Bool), wordValue s w = 1 ↔ wordValue (f ∘ s) w = 1) ∧
      TuringReducible (wordProblemOracle s) (wordProblemOracle u) := by
  refine ⟨fun w => ?_, ?_⟩
  · rw [wordValue_map, ← map_one f]
    exact hf.eq_iff.symm
  · rw [← wordProblemOracle_comp_injective s f hf]
    exact turingReducible_wordProblemOracle_of_generates hu (f ∘ s)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_corLefSubstitution

/-- **The two heredity facts** (tex l.676–678): a finitely generated group `Γ` embedded in a group with solvable word
problem has solvable word problem, and a group embedded in a LEF group is LEF. -/
theorem manuscriptSentence_corLefHeredity (Γ E : Type) [Group Γ] [Group E] (f : Γ →* E)
    (hf : Function.Injective f) :
    (Group.FG Γ → HasSolvableWordProblem E → HasSolvableWordProblem Γ) ∧ (IsLEF E → IsLEF Γ) :=
  ⟨fun hfg hE => printedSolvableWordProblemHeredity Γ E hfg hE f hf, fun hE => isLEF_of_injective f hf hE⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_corLefHeredity

end HalflineB
end SimpleKazhdanSofic
end Manuscript
end GroupApproximation
