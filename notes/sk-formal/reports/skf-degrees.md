# skf-degrees: ledger for the section "Word problems and factors" of simple_kazhdan_sofic_group.tex

Lane `skf-degrees`, formalization of the note (lead = session nonsofic-existence-49/ff). Written by skf-degrees only.

## Target
- Tip 696c4b602 (09-13 23:51), 841 lines, md5 0648e5f876e467e21ebf475e08b8ee92. Section "Word problems and factors"
  (`sec:wp`) is l.496–554; corollary `cor:wp` is l.498.
- Census aa6f988f4 is at the tip. Rows by hash landed at 74c8be3ac.
- Split:
  - skf-degrees: substitution reductions, L(X) ≤_T WP, the α ↔ L(X_α) truth tables (absorbed from skf-approximants,
    which is not resumed), solvability and Fibonacci, and the cor:wp assembly;
  - ms-traces-3: WP ≤_T L(X), then the antichain of size continuum;
  - sk-stepanov: (e), the two oracles cut(α) ↔ χ_B and the assembly of `PrintedContinuedFractionRepresentative`;
  - ct-involution: the kernel paragraph (bdd19b7d1e1f);
  - oa-mcduff: the OzawaUniversal Theorem 2 step;
  - skf-cite: the Grigorchuk–Medynets and NPS attributions.

## Sentences at 696c4b602
| hash | sentence | carrier | state |
|---|---|---|---|
| 5e46951a6be7 | WP(G_X) has the Turing degree of L(X) | `printedWordProblemDegreeEqLanguage_of` (from (c)) | partial, waits on (c) |
| ddf15100fbf8 | solvable WP ⇔ L(X) recursive, as for X_{(3−√5)/2} | `printedSolvableWordProblemIffRecursiveLanguage_of`, `printedFibonacciSolvableWordProblem_of` (from (c)), `partrec_slopeOracle_fibonacci` | partial, waits on (c) |
| 8fd0348904ee | every Turing degree occurs; continuum many G_X, none isomorphic to a subgroup of another | `PrintedWordProblemsCorollary` | partial, waits on (c), (e), antichain, and the assembly |
| 427203e368c1, 5092adf162d8 | multiplying out a word …; L(X) computes the word problem | ms-traces-3 | open piece |
| 229c4a7b2e24 | a word for e_12(∏ u^{-t} e_{v_t} u^t) is computable from v, trivial iff v ∉ L(X) | `printedLanguageReducesToWordProblem` | formalized |
| 5959e4fd6209 | X_α infinite minimal Sturmian, closure of codings, arcs | skf-approximants' landed carriers | formalized |
| aa090b172df4 | closure adds no words; words on arcs; α computes L(X_α) | `language_sturmianSubshift`, `printedSturmianEndpointsDetermineWords`, `printedSlopeComputesSturmianLanguage` | formalized |
| 4ee0770eb47c | ones within 1 of mα, so L(X_α) computes α | `printedSturmianOnesWithinOne`, `printedSturmianLanguageComputesSlope` | formalized |
| 7badee43dd9d | every S ⊆ ℕ has the degree of [0; 1+χ_S(0), …] | sk-stepanov, over my `ContinuedFractionExpansion`, `ContinuedFractionConvergents`, `OracleRecursion` | open piece |
| 4037fa331dbb | if H embeds in G, WP(H) reduces to WP(G) | `printedWordProblemReducesUnderEmbedding` | formalized |
| 540fcf55264f | the Turing degrees contain an antichain of size continuum | ms-traces-3 (`PrintedTuringAntichainContinuum`) | open piece |

## Landed modules (Manuscript/SimpleKazhdanSofic)
- 8be083fcd:
  - `WordProblemDegreeStatements`: the oracles, the generators, all named Props of `cor:wp`;
  - `WordOracle`: word algebra, `wordProblemOracle_comp_injective`, `turingReducible_of_query`;
  - `WordProblemDegreeInvariant`: `turingReducible_wordProblemOracle_of_generates`,
    `printedWordProblemReducesUnderEmbedding`.
- 99dc0e949:
  - `LanguageReducesToWordProblem`: cylinder words, `wordValue_cylinderWord_eq_one_iff`,
    `printedLanguageReducesToWordProblem`;
  - `ContinuedFractionExpansion`: `tail`, `tail_eq`, `tail_mem`, `isContinuedFractionOf_tail`, `irrational_tail`.
- 824bd3166 `ContinuedFractionConvergents`: `conv`, `det_conv`, `tail_zero_eq`, `digit_eq_of_answer`.
- 615fed71d:
  - `SturmianQueries`: list criteria and primrec queries;
  - `SturmianComputability`: `printedSlopeComputesSturmianLanguage`, `printedSturmianLanguageComputesSlope`.
- 86b33d19b `WordProblemSolvability`: `partrec_iff_of_turingEquivalent`, the `_of` endpoints from (c),
  `partrec_slopeOracle_fibonacci`.
- aecf7efff `OracleRecursion`: `turingReducible_of_oracleRec`.

## Not landed
- `ContinuumManyDegrees`, which counts countable Turing classes. It has no printed carrier since 37551fd93: the printed
  sentence it carried was replaced by the antichain claim, and counting does not give that.
