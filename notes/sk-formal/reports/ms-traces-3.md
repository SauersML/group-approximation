# ms-traces-3: word-problem reduction and Turing antichain in simple_kazhdan_sofic_group.tex

Lane `ms-traces-3`, reassigned by main (09-13 ~19:40; antichain item added 09-14). This file is written by ms-traces-3 only.

## Target at the tip
- Census `metadata/SK_SENTENCE_CENSUS.tsv` is recorded at 696c4b602 (md5 0648e5f876e467e21ebf475e08b8ee92). The keys below are from it.
- The tip moved to f34e9c0b1 (09-14 09:05, md5 c909343ec38f3d3e7976342073509639). The section is now "Word problems" and `cor:wp` is at l.461.
- The (c) sentences survive at the tip. The antichain sentence was rewritten: "By a construction of Sacks, the Turing degrees contain an antichain of size continuum [Odifreddi, Chapter V], and the groups G_{X_α} with α of these degrees are as claimed."
  - Its row waits for skf-census to regenerate at the tip.
  - The carried content is unchanged; "By a construction of Sacks" is attribution, and the route is the perfect-tree finite-extension construction.
- (c), l.507–512, keys `427203e368c1` and `5092adf162d8`:
  > Multiplying out a word in the generators in LC(A^ℤ,F₂)⋊ℤ, which maps onto R, gives a matrix with entries Σ_j f_j u^j, each f_j given by a table on the words of some length, using uf = (f∘T⁻¹)u. The word is trivial in G_X if and only if the tables of its difference from I₃ vanish on L(X), so L(X) computes the word problem.
- Antichain, l.532–534, key `540fcf55264f`:
  > The Turing degrees contain an antichain of size continuum [Odifreddi, Chapter V], and the groups G_{X_α} with α of these degrees are as claimed.
- Prop spellings are owned by skf-degrees, in `SimpleKazhdanSofic/WordProblemDegreeStatements` (on origin at 8be083fcd): `PrintedWordProblemReducesToLanguage` and `PrintedTuringAntichainContinuum`.

## Route
- (c):
  - A table is a finite list of cylinder monomials `1_c·u^j`. It is an element of LC(A^ℤ,F₂)⋊ℤ in cylinder coordinates, and `eval` reads it in LC(X,F₂)⋊ℤ, which is the map onto R.
  - Table products are ring products, through uf = (f∘T⁻¹)u on cylinders.
  - A word multiplies out to a 3×3 matrix of tables. In characteristic 2, e_ij(s)⁻¹ = e_ij(s).
  - The word is trivial iff, at every position, the coefficient parities of the table of M − I₃ vanish at every word of L(X) of length 2K+1, where K bounds the table coordinates.
  - The reduction is a truth-table reduction: it queries those words and decides primitive recursively.
- Antichain, proved with no literature input:
  - oracle programs mirroring `Nat.RecursiveIn`, and the use principle;
  - the Kleene–Post finite-extension step;
  - a perfect tree whose stages apply the step to every requirement (ρ, ρ', e) with ρ ≠ ρ' and e ≤ s;
  - distinct branches give Turing-incomparable sets, and branches indexed by Set ℕ give continuum many.

## Modules
| module | content | state |
|---|---|---|
| `Computability/OracleTruthTable` | `turingReducible_of_truthTable` | LANDED cc80bf23b |
| `SimpleKazhdanSofic/CylinderTables` | `eval_tableMul`, `cylInd_mul_comap`, `coeff_eval`, `eval_eq_zero_iff` | LANDED cc80bf23b |
| `SimpleKazhdanSofic/WordNormalForm` | `matEval_matMul`, `matEval_elemMat`, `matEval_wordMat` | LANDED e2d31c60a |
| `SimpleKazhdanSofic/WordProblemCriterion` | windows of X are the words of L(X); `eval_eq_zero_iff_language`, `matEval_eq_one_iff_language` | LANDED e81f21d8c |
| `SimpleKazhdanSofic/WordTablePrimrec` | primrec integer `natAbs`/`toNat`, table and matrix products, `wordMat` | LANDED 42d83a366 |
| `SimpleKazhdanSofic/WordProblemDecision` | `wordQueries`, `wordDecide`, `allWords` and their primrec proofs | LANDED 723c0e2b7 |
| `SimpleKazhdanSofic/WordProblemReducesToLanguage` | `turingReducible_of_wordTables` over any primrec letter tables | LANDED b3c6724cf |
| `SimpleKazhdanSofic/WordProblemReducesToLanguageInstance` | `printedWordProblemReducesToLanguage : PrintedWordProblemReducesToLanguage` | LANDED 4e8b0ae09 (probe 0914-091446-34286 BUILT, closed audit) |
| `Computability/OracleUse` | `OCode`, `exists_eval_eq`, `setOracle`, `mem_eval_of_agreeBelow` (the use principle) | LANDED 7a4df2737 |
| `Computability/FiniteExtensionStep` | `Extends`, `Diag`, `Diag.mono`, `exists_diag` | LANDED 7a4df2737 |
| `Computability/PerfectTreeAntichain` | `stage_diag`, `extends_branchSet`, `not_turingReducible_branchSet`, `branchSet_injective`, `exists_turing_antichain_continuum` | LANDED ca619e4d8 (same probe) |
| `SimpleKazhdanSofic/TuringAntichain` | `printedTuringAntichainContinuum : PrintedTuringAntichainContinuum` | LANDED ca619e4d8 (same probe, closed audit) |

All twelve modules are LANDED and queued in `wire-queue.txt`, about 2000 lines in total, within the estimate.

## Census rows (`metadata/sk-census-rows/ms-traces-3.tsv`)
- `427203e368c1` and `5092adf162d8` are formalized. Both sentences are verbatim at the tip f34e9c0b1.
- `540fcf55264f` (antichain) waits: the tip rewrote the sentence, so its key is stale. The row lands once skf-census regenerates at the tip.

## Notes for the owner of the statements
- The tip's generating set is S = {1, u, u⁻¹} ∪ {e_a} (l.243 at 37551fd93, unchanged in wording at the tip). The statements' `Coeff` omits 1.
  - The degree of the word problem does not depend on the finite generating set.
  - The tables handle 1 as `[(0, [])]`.
- `OracleUse.OCode` duplicates the oracle codes in skf-degrees' unlanded `ContinuumManyDegrees`. It has the same constructors and semantics, and is now on origin; `ContinuumManyDegrees` can consume it.
- Key `540fcf55264f` covers two clauses. This lane carries only the first (the antichain); the second ("the groups G_{X_α} … are as claimed") is skf-degrees' corollary assembly. Graded `partial` accordingly.

## Item 3 (main, 09-14 ~09:30): the Questions block
- Census 9cb80166d at tip 8b36733d7 (md5 29d63f7944bccccbf9a91b0b2714c0b4), l.510–529. Keys `25f820cbd165`, `1c40d21401f6`, `dc73886fdc13`, `85fe62a789f3`, `60be9d39afa5`, `7d13cf4208bc`, `7f61e23f0bee`.
- Existing carriers (ct-involution, at retired keys `44b4aa4489ab` and `3606856b9a07`):
  - `printedFinitelyPresentedLEFResiduallyFinite` and `printedNotFinitelyPresentedOfLEFSimpleInfinite`, closed (`QuestionsNotFinitelyPresented`, 04ba48c58);
  - `printedGXNotFinitelyPresented_of_main`, conditional on `PrintedSimpleKazhdanSoficMain`;
  - `printedConjugacyIsomorphism`, closed (`CrossedProductConjugacy`, 730da5240).
- `printedSimpleKazhdanSoficMain` is closed on origin (b972efc71).
- CLAIM `GroupApproximation/Manuscript/SimpleKazhdanSofic/QuestionsClosed.lean`:
  - the closed discharge `printedGXNotFinitelyPresented`;
  - `PrintedSoficKazhdanExampleNotLEF`: a finitely presented infinite simple group is not LEF, and a finitely presented infinite simple sofic Kazhdan group is a finitely presented sofic Kazhdan group that is not residually finite (the printed reason: finitely presented LEF groups are residually finite, infinite simple groups are not).
- CLAIM the seven new rows, naming ct-involution's carriers with credit. The split was sent to ct-involution in one message.
