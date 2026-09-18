import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemsCorollaryAssembly
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordMultipliesOut
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:wp`: word problems of the groups `G_X`

Sentences of `simple_kazhdan_sofic_group.tex`, corollary `cor:wp` and its proof (l.683–726).

* l.684–687: "The word problem of `G_X` has the Turing degree of the language `L(X)` of `X`, the
  set of words occurring in points of `X`, so `G_X` has solvable word problem if and only if `L(X)`
  is recursive, as for the Fibonacci subshift `X_{(3-√5)/2}` below."
* l.687–689: "Every Turing degree is the degree of the word problem of some `G_X`, and there is a
  family of continuum many groups `G_X`, none of which embeds in another."
* l.693–696: "Multiplying out a word in the generators over `LC(A^ℤ,F₂)⋊ℤ`, which maps onto `R`,
  with the rule `uf=(f∘T⁻¹)u` gives a matrix with entries `∑_j f_j u^j`, where each `f_j` is given
  by a table on the words of some length."
* l.716–719: "If a finitely generated group `H` embeds in a finitely generated group `G`, a word
  for `H` becomes a word for `G` by substituting words in the generators of `G` for the generators
  of `H`, so the word problem of `H` reduces to that of `G`."
* l.724–726 (attribution, no declaration): "For derived topological full groups, Grigorchuk and
  Medynets proved that the word problem is solvable if and only if `L(X)` is recursive."

All computability notions are Mathlib's: `TuringEquivalent`, `TuringReducible` and `Partrec` on
the repository's oracles `wordProblemOracle` (characteristic function of the set of codes of words
in the generators `e_ij(s)` that are trivial in `G_X`), `languageOracle` (of `L(X)`) and
`charOracle` (of a set `B ⊆ ℕ`, which represents an arbitrary Turing degree).

Proof route.  Every statement below is written out in full (no `Printed…` abbreviation appears in
a statement) and proved from the closed upstream theorems of the corpus, which carry no hypotheses:
`printedWordProblemDegreeEqLanguage`, `printedSolvableWordProblemIffRecursiveLanguage`,
`printedFibonacciSolvableWordProblem`, `printedWordProblemsCorollary`,
`printedWordMultipliesOutToTables`, `printedWordProblemReducesUnderEmbedding`, together with
`printedSturmianSubshiftInfiniteIsMinimal`, `irrational_fibonacci_slope` and
`fibonacci_slope_mem` for the Fibonacci subshift.  Their statements unfold definitionally to the
statements here.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace NNWordProblem

open SymbolicDynamics.FullShift CylinderTables

/-- **`cor:wp`, l.684–687.**  For every infinite minimal subshift `X` over a finite alphabet, the
word problem of `G_X` is Turing equivalent to the language `L(X)`; hence `G_X` has solvable word
problem iff `L(X)` is recursive; and the Fibonacci subshift `X_{(3-√5)/2}` is infinite, minimal,
with solvable word problem and recursive language. -/
theorem manuscriptSentence_wordProblemDegreeOfLanguage :
    (∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [DecidableEq A]
      [Primcodable A] (S : Subshift A ℤ), Infinite S.carrier → IsMinimal S →
        TuringEquivalent (wordProblemOracle (genValue S)) (languageOracle S)) ∧
    (∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [DecidableEq A]
      [Primcodable A] (S : Subshift A ℤ), Infinite S.carrier → IsMinimal S →
        (Partrec (wordProblemOracle (genValue S)) ↔ Partrec (languageOracle S))) ∧
    ((sturmianSubshift ((3 - Real.sqrt 5) / 2)).carrier.Infinite ∧
      IsMinimal (sturmianSubshift ((3 - Real.sqrt 5) / 2)) ∧
      Partrec (wordProblemOracle (genValue (sturmianSubshift ((3 - Real.sqrt 5) / 2)))) ∧
      Partrec (languageOracle (sturmianSubshift ((3 - Real.sqrt 5) / 2)))) := by
  have hmin := printedSturmianSubshiftInfiniteIsMinimal ((3 - Real.sqrt 5) / 2)
    irrational_fibonacci_slope fibonacci_slope_mem.1 fibonacci_slope_mem.2
  have hwp := printedFibonacciSolvableWordProblem
  exact ⟨printedWordProblemDegreeEqLanguage, printedSolvableWordProblemIffRecursiveLanguage,
    hmin.1, hmin.2, hwp,
    (printedSolvableWordProblemIffRecursiveLanguage Bool (sturmianSubshift ((3 - Real.sqrt 5) / 2))
      hmin.1.to_subtype hmin.2).1 hwp⟩

#audit_axioms manuscriptSentence_wordProblemDegreeOfLanguage

/-- **`cor:wp`, l.687–689.**  Every Turing degree (the degree of an arbitrary `B ⊆ ℕ`) is the degree
of the word problem of some `G_X`, `X` infinite minimal; and there is a family of continuum many
infinite minimal subshifts `X` such that `G_X` embeds in `G_{X'}` only when `X = X'`. -/
theorem manuscriptSentence_everyDegreeAndContinuumAntichain :
    (∀ B : Set ℕ, ∃ S : Subshift Bool ℤ, Infinite S.carrier ∧ IsMinimal S ∧
      TuringEquivalent (wordProblemOracle (genValue S)) (charOracle B)) ∧
    ∃ F : Set (Subshift Bool ℤ), Cardinal.mk F = Cardinal.continuum ∧
      (∀ S ∈ F, Infinite S.carrier ∧ IsMinimal S) ∧
      ∀ S ∈ F, ∀ S' ∈ F, (∃ ψ : G S →* G S', Function.Injective ψ) → S = S' := by
  obtain ⟨-, -, -, hdeg, hanti⟩ := printedWordProblemsCorollary
  exact ⟨hdeg, hanti⟩

#audit_axioms manuscriptSentence_everyDegreeAndContinuumAntichain

/-- **`cor:wp`, proof, l.693–696.**  For every word `w` in the generators `e_ij(s)` there are a
radius `K`, a finite exponent set `E` and tables `F` on words of length `2K+1` such that for every
subshift `X` the matrix of `w` in `G_X ≤ GL_3(R)` has entries `∑_{j∈E} f_j u^j`, with `f_j`
locally constant and `f_j(x) = F(x_{[-K,K]})`. -/
theorem manuscriptSentence_wordMultipliesOutToTables :
    ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [DecidableEq A]
      (w : List (Gen A × Bool)),
      ∃ (K : ℕ) (E : Finset ℤ) (F : Fin 3 → Fin 3 → ℤ → List A → Bool),
        ∀ S : Subshift A ℤ, ∃ f : Fin 3 → Fin 3 → ℤ → LocallyConstant S.carrier (ZMod 2),
          (∀ p q : Fin 3,
            (((wordValue (genValue S) w : G S) : (Matrix (Fin 3) (Fin 3) (R S))ˣ) :
                Matrix (Fin 3) (Fin 3) (R S)) p q =
              ∑ j ∈ E, ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2) (f p q j) *
                ((ClopenCrossedProduct.unit (subshiftHomeo S) (ZMod 2) ^ j : (R S)ˣ) : R S)) ∧
          ∀ (p q : Fin 3) (j : ℤ) (x : S.carrier),
            f p q j x = if F p q j (window x.1 K) = true then 1 else 0 :=
  printedWordMultipliesOutToTables

#audit_axioms manuscriptSentence_wordMultipliesOutToTables

/-- **`cor:wp`, proof, l.716–719.**  If `H` and `G'` are generated by finite families `t` and `s`
and `ψ : H →* G'` is injective, then the word problem of `H` with respect to `t` Turing reduces to
the word problem of `G'` with respect to `s`. -/
theorem manuscriptSentence_wordProblemReducesUnderEmbedding :
    ∀ (H G' : Type) [Group H] [Group G'] (ι κ : Type) [Primcodable ι] [Primcodable κ] [Finite ι]
      [Finite κ] (s : ι → G') (t : κ → H) (ψ : H →* G'), Function.Injective ψ →
        Subgroup.closure (Set.range s) = ⊤ → Subgroup.closure (Set.range t) = ⊤ →
          TuringReducible (wordProblemOracle t) (wordProblemOracle s) :=
  printedWordProblemReducesUnderEmbedding

#audit_axioms manuscriptSentence_wordProblemReducesUnderEmbedding

end NNWordProblem
end SimpleKazhdanSofic
end GroupApproximation
