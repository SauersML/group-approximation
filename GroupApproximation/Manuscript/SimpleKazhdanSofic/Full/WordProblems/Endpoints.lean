import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemsCorollaryAssembly
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordMultipliesOut
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:wp`: word problems of the groups `G_X`

Endpoints of lane SK13 for `simple_kazhdan_sofic_group.tex`, section `sec:wp`, corollary `cor:wp`
and its proof (l.683–721), and the row "word problem | has the Turing degree of `L(X)`" of the
table `tab:props` (l.198–213).

Corollary `cor:wp` (l.683–689):

> The word problem of `G_X` has the Turing degree of the language `L(X)` of `X`, the set of words
> occurring in points of `X`, so `G_X` has solvable word problem if and only if `L(X)` is
> recursive, as for the Fibonacci subshift `X_{(3-√5)/2}` below. Every Turing degree is the degree
> of the word problem of some `G_X`, and there is a family of continuum many groups `G_X`, none of
> which embeds in another.

Every endpoint is stated in full, with no `Printed…` proposition as a hypothesis, and proved
unconditionally from the corpus theorems of the `cor:wp` closure:
`printedWordProblemReducesToLanguage`, `printedLanguageReducesToWordProblem`,
`printedWordMultipliesOutToTables`, `printedWordProblemReducesUnderEmbedding`,
`printedSlopeComputesSturmianLanguage`, `printedSturmianLanguageComputesSlope`,
`printedSturmianSubshiftInfiniteIsMinimal`, `printedContinuedFractionRepresentative`,
`printedTuringAntichainContinuum` (Sacks' antichain, proved in the corpus by a perfect-tree
construction) and the assembly `printedWordProblemsCorollary`.

Computability notions are Mathlib's `TuringReducible`, `TuringEquivalent` and `Partrec`, applied
to the corpus oracles `wordProblemOracle` (the characteristic function of the codes of words in the
generators `e_ij(s)` that are trivial in `G_X`), `languageOracle` (of `L(X)`), `slopeOracle` (the
cut `a < bα`) and `charOracle` (of a set `B ⊆ ℕ`, which represents an arbitrary Turing degree).

The attribution l.724–726 (Grigorchuk–Medynets, for derived topological full groups) is a citation
of another theorem and has no declaration here.
-/

namespace GroupApproximation.Full.SK13

open GroupApproximation.SimpleKazhdanSofic
open GroupApproximation.SimpleKazhdanSofic.SturmianComputability
open SymbolicDynamics.FullShift

/-! ## The word problem and the language (`cor:wp`, first sentence, and proof l.693–703) -/

/-- **`cor:wp`, proof, l.693–696.**  Multiplying out a word `w` in the generators `e_ij(s)` gives a
matrix with entries `∑_{j∈E} f_j u^j`, where each `f_j` is given by a table `F` on the words
`x_{[-K,K]}`; the radius `K`, the exponents `E` and the tables `F` depend only on `w`. -/
theorem word_multiplies_out (A : Type) [TopologicalSpace A] [DiscreteTopology A] [DecidableEq A]
    (w : List (Gen A × Bool)) :
    ∃ (K : ℕ) (E : Finset ℤ) (F : Fin 3 → Fin 3 → ℤ → List A → Bool),
      ∀ S : Subshift A ℤ, ∃ f : Fin 3 → Fin 3 → ℤ → LocallyConstant S.carrier (ZMod 2),
        (∀ p q : Fin 3,
          (((wordValue (genValue S) w : G S) : (Matrix (Fin 3) (Fin 3) (R S))ˣ) :
              Matrix (Fin 3) (Fin 3) (R S)) p q =
            ∑ j ∈ E, ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2) (f p q j) *
              ((ClopenCrossedProduct.unit (subshiftHomeo S) (ZMod 2) ^ j : (R S)ˣ) : R S)) ∧
        ∀ (p q : Fin 3) (j : ℤ) (x : S.carrier),
          f p q j x = if F p q j (CylinderTables.window x.1 K) = true then 1 else 0 :=
  printedWordMultipliesOutToTables A w

#audit_axioms word_multiplies_out

/-- **`cor:wp`, proof, l.696–698.**  The word is trivial in `G_X` if and only if the tables of its
difference from `I_3` vanish on `L(X)`, so `L(X)` computes the word problem. -/
theorem wp_reduces_to_language (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
    [DecidableEq A] [Primcodable A] (S : Subshift A ℤ) :
    TuringReducible (wordProblemOracle (genValue S)) (languageOracle S) :=
  printedWordProblemReducesToLanguage A S

#audit_axioms wp_reduces_to_language

/-- **`cor:wp`, proof, l.698–701.**  A word for `e_12(∏_{t<m} u^{-t} e_{v_t} u^t)` is computable
from `v`, and it is trivial if and only if `v ∉ L(X)`, so the word problem computes `L(X)`. -/
theorem language_reduces_to_wp (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
    [DecidableEq A] [Primcodable A] (S : Subshift A ℤ) :
    TuringReducible (languageOracle S) (wordProblemOracle (genValue S)) :=
  printedLanguageReducesToWordProblem A S

#audit_axioms language_reduces_to_wp

/-- **`cor:wp`, first sentence (l.684–686).**  For an infinite minimal subshift `X` over a finite
alphabet, the word problem of `G_X` has the Turing degree of the language `L(X)`. -/
theorem wp_degree_eq_language (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
    [DecidableEq A] [Primcodable A] (S : Subshift A ℤ) (hinf : Infinite S.carrier)
    (hmin : IsMinimal S) :
    TuringEquivalent (wordProblemOracle (genValue S)) (languageOracle S) :=
  printedWordProblemDegreeEqLanguage A S hinf hmin

#audit_axioms wp_degree_eq_language

/-- **`cor:wp`, first sentence (l.686–687).**  `G_X` has solvable word problem if and only if
`L(X)` is recursive.  Also the `tab:props` row "word problem: has the Turing degree of `L(X)`". -/
theorem wp_solvable_iff_recursive (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
    [DecidableEq A] [Primcodable A] (S : Subshift A ℤ) (hinf : Infinite S.carrier)
    (hmin : IsMinimal S) :
    Partrec (wordProblemOracle (genValue S)) ↔ Partrec (languageOracle S) :=
  printedSolvableWordProblemIffRecursiveLanguage A S hinf hmin

#audit_axioms wp_solvable_iff_recursive

/-! ## Sturmian subshifts (`cor:wp`, proof l.703–714) -/

/-- **`cor:wp`, proof, l.703–704.**  For irrational `α ∈ (0,1)` the Sturmian subshift `X_α` is
infinite and minimal. -/
theorem sturmian_infinite_minimal (α : ℝ) (hα : Irrational α) (h0 : 0 < α) (h1 : α < 1) :
    (sturmianSubshift α).carrier.Infinite ∧ IsMinimal (sturmianSubshift α) :=
  printedSturmianSubshiftInfiniteIsMinimal α hα h0 h1

#audit_axioms sturmian_infinite_minimal

/-- **`cor:wp`, proof, l.709–712.**  "`α` computes `L(X_α)`". -/
theorem sturmian_language_reduces_to_slope (α : ℝ) (hα : Irrational α) (h0 : 0 < α)
    (h1 : α < 1) : TuringReducible (languageOracle (sturmianSubshift α)) (slopeOracle α) :=
  printedSlopeComputesSturmianLanguage α hα h0 h1

#audit_axioms sturmian_language_reduces_to_slope

/-- **`cor:wp`, proof, l.712–714.**  A word of length `m` of `X_α` has `⌊θ+mα⌋` ones, within `1`
of `mα`, so `L(X_α)` computes `α`. -/
theorem slope_reduces_to_sturmian_language (α : ℝ) (hα : Irrational α) (h0 : 0 < α)
    (h1 : α < 1) : TuringReducible (slopeOracle α) (languageOracle (sturmianSubshift α)) :=
  printedSturmianLanguageComputesSlope α hα h0 h1

#audit_axioms slope_reduces_to_sturmian_language

/-- **`cor:wp`, proof, l.709–714.**  `L(X_α)` and `α` have the same Turing degree. -/
theorem sturmian_language_equiv_slope (α : ℝ) (hα : Irrational α) (h0 : 0 < α) (h1 : α < 1) :
    TuringEquivalent (languageOracle (sturmianSubshift α)) (slopeOracle α) :=
  ⟨printedSlopeComputesSturmianLanguage α hα h0 h1,
    printedSturmianLanguageComputesSlope α hα h0 h1⟩

#audit_axioms sturmian_language_equiv_slope

/-- **`cor:wp`, first sentence, "as for the Fibonacci subshift `X_{(3-√5)/2}`" (l.687).**  The
Fibonacci subshift is infinite and minimal, its group has solvable word problem, and its language
is recursive. -/
theorem fibonacci_wp_solvable :
    (sturmianSubshift ((3 - Real.sqrt 5) / 2)).carrier.Infinite ∧
      IsMinimal (sturmianSubshift ((3 - Real.sqrt 5) / 2)) ∧
      Partrec (wordProblemOracle (genValue (sturmianSubshift ((3 - Real.sqrt 5) / 2)))) ∧
      Partrec (languageOracle (sturmianSubshift ((3 - Real.sqrt 5) / 2))) := by
  have hmin := printedSturmianSubshiftInfiniteIsMinimal ((3 - Real.sqrt 5) / 2)
    irrational_fibonacci_slope fibonacci_slope_mem.1 fibonacci_slope_mem.2
  have hwp := printedFibonacciSolvableWordProblem
  exact ⟨hmin.1, hmin.2, hwp,
    (printedSolvableWordProblemIffRecursiveLanguage Bool (sturmianSubshift ((3 - Real.sqrt 5) / 2))
      hmin.1.to_subtype hmin.2).1 hwp⟩

#audit_closed_axioms GroupApproximation.Full.SK13.fibonacci_wp_solvable

/-! ## Every degree, and the antichain (`cor:wp`, second sentence, proof l.714–721) -/

open Classical in
/-- **`cor:wp`, proof, l.714–716.**  Every `D ⊆ ℕ` has the degree of the irrational number
`[0; 1+χ_D(0), 1+χ_D(1), …]`. -/
theorem continued_fraction_representative (B : Set ℕ) :
    ∃ α : ℝ, IsContinuedFractionOf α (fun k => 1 + if k ∈ B then 1 else 0) ∧ Irrational α ∧
      TuringEquivalent (slopeOracle α) (charOracle B) :=
  printedContinuedFractionRepresentative B

#audit_axioms continued_fraction_representative

/-- **`cor:wp`, proof, l.716–719.**  If a finitely generated group `H` embeds in a finitely
generated group `G'`, the word problem of `H` reduces to that of `G'`. -/
theorem wp_reduces_under_embedding (H G' : Type) [Group H] [Group G'] (ι κ : Type)
    [Primcodable ι] [Primcodable κ] [Finite ι] [Finite κ] (s : ι → G') (t : κ → H) (ψ : H →* G')
    (hψ : Function.Injective ψ) (hs : Subgroup.closure (Set.range s) = ⊤)
    (ht : Subgroup.closure (Set.range t) = ⊤) :
    TuringReducible (wordProblemOracle t) (wordProblemOracle s) :=
  printedWordProblemReducesUnderEmbedding H G' ι κ s t ψ hψ hs ht

#audit_axioms wp_reduces_under_embedding

/-- The generators `e_ij(s)`, `s ∈ {u, u⁻¹} ∪ {e_a : a ∈ A}`, generate `G_X`, so the word problem
of `G_X` in these generators is the word problem of a finitely generated group (`cor:wp`). -/
theorem generators_generate {A : Type} [TopologicalSpace A] [DiscreteTopology A] [DecidableEq A]
    [Finite A] (S : Subshift A ℤ) : Subgroup.closure (Set.range (genValue S)) = ⊤ :=
  closure_range_genValue S

#audit_axioms generators_generate

/-- **`cor:wp`, proof, l.719–721.**  By a construction of Sacks, the Turing degrees contain an
antichain of size continuum. -/
theorem turing_antichain_continuum :
    ∃ F : Set (Set ℕ), Cardinal.mk F = Cardinal.continuum ∧
      ∀ B ∈ F, ∀ C ∈ F, TuringReducible (charOracle B) (charOracle C) → B = C :=
  printedTuringAntichainContinuum

#audit_closed_axioms GroupApproximation.Full.SK13.turing_antichain_continuum

open Classical in
/-- **`cor:wp`, second sentence (l.687–688), with the representative of its proof (l.703–721).**
Every Turing degree, the degree of an arbitrary `B ⊆ ℕ`, is the degree of the word problem of
`G_{X_α}` for the Sturmian subshift of `α = [0; 1+χ_B(0), 1+χ_B(1), …]`, which is irrational in
`(0,1)`, so `X_α` is infinite and minimal. -/
theorem every_degree_sturmian (B : Set ℕ) :
    ∃ α : ℝ, IsContinuedFractionOf α (fun k => 1 + if k ∈ B then 1 else 0) ∧ Irrational α ∧
      0 < α ∧ α < 1 ∧ (sturmianSubshift α).carrier.Infinite ∧ IsMinimal (sturmianSubshift α) ∧
      TuringEquivalent (wordProblemOracle (genValue (sturmianSubshift α))) (charOracle B) := by
  obtain ⟨α, hcf, hirr, heq⟩ := printedContinuedFractionRepresentative B
  have hfl : ⌊α⌋ = 0 := by
    have h := hcf.1
    rw [GenContFract.of_h_eq_floor] at h
    exact_mod_cast h
  obtain ⟨h0, h1⟩ := Int.floor_eq_zero_iff.1 hfl
  have hpos : 0 < α := lt_of_le_of_ne h0 (Ne.symm hirr.ne_zero)
  have hmin := printedSturmianSubshiftInfiniteIsMinimal α hirr hpos h1
  have hWL := printedWordProblemDegreeEqLanguage Bool (sturmianSubshift α) hmin.1.to_subtype hmin.2
  have hLα : TuringEquivalent (languageOracle (sturmianSubshift α)) (slopeOracle α) :=
    ⟨printedSlopeComputesSturmianLanguage α hirr hpos h1,
      printedSturmianLanguageComputesSlope α hirr hpos h1⟩
  exact ⟨α, hcf, hirr, hpos, h1, hmin.1, hmin.2,
    TuringEquivalent.trans _ _ _ (TuringEquivalent.trans _ _ _ hWL hLα) heq⟩

#audit_axioms every_degree_sturmian

/-- **`cor:wp`, second sentence (l.687–688).**  Every Turing degree is the degree of the word
problem of some `G_X`, `X` infinite and minimal. -/
theorem every_degree (B : Set ℕ) :
    ∃ S : Subshift Bool ℤ, Infinite S.carrier ∧ IsMinimal S ∧
      TuringEquivalent (wordProblemOracle (genValue S)) (charOracle B) := by
  obtain ⟨-, -, -, hdeg, -⟩ := printedWordProblemsCorollary
  exact hdeg B

#audit_axioms every_degree

/-- **`cor:wp`, second sentence (l.688–689).**  There is a family of continuum many infinite minimal
subshifts `X` whose groups `G_X` do not embed in one another: `G_X` embeds in `G_{X'}` only when
`X = X'`. -/
theorem continuum_antichain :
    ∃ F : Set (Subshift Bool ℤ), Cardinal.mk F = Cardinal.continuum ∧
      (∀ S ∈ F, Infinite S.carrier ∧ IsMinimal S) ∧
      ∀ S ∈ F, ∀ S' ∈ F, (∃ ψ : G S →* G S', Function.Injective ψ) → S = S' := by
  obtain ⟨-, -, -, -, hanti⟩ := printedWordProblemsCorollary
  exact hanti

#audit_closed_axioms GroupApproximation.Full.SK13.continuum_antichain

/-- **Corollary `cor:wp`** (l.683–689), the corpus conjunction `PrintedWordProblemsCorollary`:
degree of the word problem equals degree of `L(X)`; solvable iff `L(X)` recursive; the Fibonacci
case; every degree occurs; continuum many groups `G_X`, none embedding in another. -/
theorem corollary : PrintedWordProblemsCorollary :=
  printedWordProblemsCorollary

#audit_closed_axioms GroupApproximation.Full.SK13.corollary

/-- **Corollary `cor:wp`** (l.683–689), written out in full. -/
theorem corollary_explicit :
    (∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [DecidableEq A]
      [Primcodable A] (S : Subshift A ℤ), Infinite S.carrier → IsMinimal S →
        TuringEquivalent (wordProblemOracle (genValue S)) (languageOracle S)) ∧
    (∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [DecidableEq A]
      [Primcodable A] (S : Subshift A ℤ), Infinite S.carrier → IsMinimal S →
        (Partrec (wordProblemOracle (genValue S)) ↔ Partrec (languageOracle S))) ∧
    Partrec (wordProblemOracle (genValue (sturmianSubshift ((3 - Real.sqrt 5) / 2)))) ∧
    (∀ B : Set ℕ, ∃ S : Subshift Bool ℤ, Infinite S.carrier ∧ IsMinimal S ∧
      TuringEquivalent (wordProblemOracle (genValue S)) (charOracle B)) ∧
    ∃ F : Set (Subshift Bool ℤ), Cardinal.mk F = Cardinal.continuum ∧
      (∀ S ∈ F, Infinite S.carrier ∧ IsMinimal S) ∧
      ∀ S ∈ F, ∀ S' ∈ F, (∃ ψ : G S →* G S', Function.Injective ψ) → S = S' := by
  exact printedWordProblemsCorollary

#audit_closed_axioms GroupApproximation.Full.SK13.corollary_explicit

end GroupApproximation.Full.SK13
