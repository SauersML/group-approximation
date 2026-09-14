# skf-degrees: ledger for the section "Word problems" of simple_kazhdan_sofic_group.tex

Lane `skf-degrees`, formalization of the note (lead = session nonsofic-existence-49/ff). Written by skf-degrees only.

## Target
- Tip 8b36733d7 (09-14 09:17), 775 lines, md5 29d63f7944bccccbf9a91b0b2714c0b4. Section "Word problems" (`sec:wp`) is
  l.462–510; corollary `cor:wp` is l.464. The census 9cb80166d is at this tip, and all my row hashes survive.
- f34e9c0b1 removed the factors paragraph (kernels, OzawaUniversal Theorem 2, NPS) from this section. Those items
  (ct-involution, oa-mcduff) no longer have printed sentences here.
- Split:
  - skf-degrees: substitution along embeddings, L(X) ≤_T WP, the α ↔ L(X_α) truth tables (absorbed from
    skf-approximants), solvability and Fibonacci, and the assembly;
  - ms-traces-3: WP ≤_T L(X) and the antichain;
  - sk-stepanov: the continued-fraction representative;
  - skf-cite: the Grigorchuk–Medynets attribution.

## cor:wp: every sentence carried
| hash | sentence | carrier | state |
|---|---|---|---|
| 5e46951a6be7 | WP(G_X) has the Turing degree of L(X) | `printedWordProblemDegreeEqLanguage` | formalized |
| ddf15100fbf8 | solvable WP ⇔ L(X) recursive, as for X_{(3−√5)/2} | `printedSolvableWordProblemIffRecursiveLanguage`, `printedFibonacciSolvableWordProblem` | formalized |
| 8fd0348904ee | every Turing degree occurs; continuum many G_X, none isomorphic to a subgroup of another | `printedWordProblemsCorollary` | formalized |
| 427203e368c1, 5092adf162d8 | L(X) computes the word problem | ms-traces-3 `printedWordProblemReducesToLanguage` | ms-traces-3's rows |
| 229c4a7b2e24 | a word for e_12(∏ u^{-t} e_{v_t} u^t) is computable from v, trivial iff v ∉ L(X) | `printedLanguageReducesToWordProblem` | formalized |
| 5959e4fd6209 | X_α infinite minimal Sturmian, closure of codings, arcs | skf-approximants' landed carriers | formalized |
| aa090b172df4 | closure adds no words; α computes L(X_α) | `printedSturmianEndpointsDetermineWords`, `printedSlopeComputesSturmianLanguage` | formalized |
| 4ee0770eb47c | ones within 1 of mα, so L(X_α) computes α | `printedSturmianOnesWithinOne`, `printedSturmianLanguageComputesSlope` | formalized |
| a686ac809830 | every D ⊆ ℕ has the degree of [0; 1+χ_D(0), …] | sk-stepanov `printedContinuedFractionRepresentative` | sk-stepanov's row |
| 4037fa331dbb | if H embeds in G, WP(H) reduces to WP(G) | `printedWordProblemReducesUnderEmbedding` | formalized |
| af3a1cf3d48e | Sacks: an antichain of size continuum [Odifreddi Ch. V] | ms-traces-3 `printedTuringAntichainContinuum` | ms-traces-3's row |

## Landed modules (Manuscript/SimpleKazhdanSofic)
- 8be083fcd:
  - `WordProblemDegreeStatements`: the oracles, the generators, all named Props of `cor:wp`;
  - `WordOracle`: word algebra, `turingReducible_of_query`;
  - `WordProblemDegreeInvariant`: `printedWordProblemReducesUnderEmbedding`.
- 99dc0e949:
  - `LanguageReducesToWordProblem`: `printedLanguageReducesToWordProblem`;
  - `ContinuedFractionExpansion`: `isContinuedFractionOf_tail`, `irrational_tail`.
- 824bd3166 `ContinuedFractionConvergents`: `digit_eq_of_answer`.
- 615fed71d `SturmianQueries`, `SturmianComputability`: both truth tables.
- 86b33d19b `WordProblemSolvability`: `partrec_slopeOracle_fibonacci`, and the `_of` endpoints from (c).
- aecf7efff `OracleRecursion`: `turingReducible_of_oracleRec`.
- `WordProblemsCorollaryAssembly`: `closure_range_genValue`, `printedWordProblemsCorollary_of`, and the closed
  `printedWordProblemDegreeEqLanguage`, `printedSolvableWordProblemIffRecursiveLanguage`,
  `printedFibonacciSolvableWordProblem`, `printedWordProblemsCorollary`.

## Not landed
- `ContinuumManyDegrees`, which counts countable Turing classes. It has no printed carrier; the antichain claim replaced
  the sentence it carried.
