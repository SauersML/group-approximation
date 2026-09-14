# skf-degrees: ledger for the section "Word problems and factors" of simple_kazhdan_sofic_group.tex

Lane `skf-degrees`, formalization of the note (lead = session nonsofic-existence-49/ff). Written by skf-degrees only.

## Target
- Tip 696c4b602 (09-13 23:51), 841 lines, md5 0648e5f876e467e21ebf475e08b8ee92. Section "Word problems and factors"
  (`sec:wp`) is l.496–554; corollary `cor:wp` is l.498.
- The census is still at 37551fd93 (649cb1f80). Rows are held until skf-census regenerates at the tip.
- Split:
  - skf-degrees: substitution reductions, L(X) ≤_T WP, the α ↔ L(X_α) truth tables (absorbed from skf-approximants), and
    the cor:wp assembly;
  - ms-traces-3: WP ≤_T L(X), then the antichain of size continuum;
  - sk-stepanov: (e), the two oracles cut(α) ↔ χ_B and the assembly of the continued-fraction representative, over my
    expansion;
  - ct-involution: the kernel paragraph (bdd19b7d1e1f);
  - oa-mcduff: the OzawaUniversal Theorem 2 step;
  - skf-cite: the Grigorchuk–Medynets and NPS attributions.

## Sentences at 696c4b602
| sentence | owner | carrier | state |
|---|---|---|---|
| WP(G_X) has the Turing degree of L(X) | skf-degrees | `PrintedWordProblemDegreeEqLanguage`; (b) `printedLanguageReducesToWordProblem` LANDED 99dc0e949; (c) ms-traces-3 | partial |
| solvable WP ⇔ L(X) recursive, as for the Fibonacci subshift X_{(3−√5)/2} | skf-degrees | `PrintedSolvableWordProblemIffRecursiveLanguage`, `PrintedFibonacciSolvableWordProblem` | partial, waits on (c) |
| every Turing degree occurs; continuum many G_X, none isomorphic to a subgroup of another | skf-degrees | `PrintedWordProblemsCorollary` | partial, waits on (c), (e), antichain |
| multiplying out a word …; L(X) computes the word problem | ms-traces-3 | `PrintedWordProblemReducesToLanguage` | open piece |
| a word for e_12(∏_{t<m} u^{-t} e_{v_t} u^t) is computable from v, trivial iff v ∉ L(X) | skf-degrees | `printedLanguageReducesToWordProblem` (LanguageReducesToWordProblem) | formalized, LANDED 99dc0e949 |
| X_α infinite minimal Sturmian; arcs; closure adds no words | skf-approximants (landed) | SturmianSubshift, SturmianSubshiftMinimal, SturmianLanguage | formalized |
| α computes L(X_α); L(X_α) computes α | skf-degrees | `printedSlopeComputesSturmianLanguage`, `printedSturmianLanguageComputesSlope` (SturmianComputability) | probing |
| every S ⊆ ℕ has the degree of [0; 1+χ_S(0), …] | sk-stepanov | `PrintedContinuedFractionRepresentative`; expansion LANDED 99dc0e949; OracleRecursion, ContinuedFractionConvergents probing | partial |
| if H embeds in G, WP(H) reduces to WP(G) | skf-degrees | `printedWordProblemReducesUnderEmbedding` (WordProblemDegreeInvariant) | formalized, LANDED 8be083fcd |
| the Turing degrees contain an antichain of size continuum [Odifreddi Ch. V] | ms-traces-3 | `PrintedTuringAntichainContinuum` | open piece |

## Modules (Manuscript/SimpleKazhdanSofic)
- LANDED 8be083fcd:
  - `WordProblemDegreeStatements`: the oracles and generators, and every named Prop of `cor:wp`;
  - `WordOracle`: word algebra, `wordProblemOracle_comp_injective`, `turingReducible_of_query`;
  - `WordProblemDegreeInvariant`: `turingReducible_wordProblemOracle_of_generates`,
    `printedWordProblemReducesUnderEmbedding`.
- LANDED 99dc0e949:
  - `LanguageReducesToWordProblem`: the cylinder words and `printedLanguageReducesToWordProblem`;
  - `ContinuedFractionExpansion`: `tail`, `tail_eq`, `tail_mem`, `isContinuedFractionOf_tail`, `irrational_tail`.
- Probing:
  - `SturmianQueries`: list forms of skf-approximants' criteria, and primrec queries;
  - `SturmianComputability`: both α ↔ L(X_α) truth tables;
  - `OracleRecursion`: `turingReducible_of_oracleRec`;
  - `ContinuedFractionConvergents`: `conv`, `det_conv`, `tail_zero_eq`, `digit_eq_of_answer`.
- Not landed, no printed carrier since 37551fd93: `ContinuumManyDegrees` (counting countable Turing classes). The printed
  sentence it carried was replaced by the antichain claim, which counting does not give.
