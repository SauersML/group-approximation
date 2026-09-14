# skf-approximants: ledger

Lane brief: `ct/ROSTER-sk.md` (session nonsofic-existence-49). Only skf-approximants writes this file.

## History
- Item 1 was tex 459–514 of b965d63ba (subsec:approximants: prop:marked, rem:fibonacci). The shortened note at bf961c128
  has no counterpart for that range. No Lean was built and no rows were landed.
- Item 2: the Sturmian subshift and the Morse–Hedlund input of "Word problems". CLOSED (c04293088, 5d4049163,
  505979ccf).
- Item 3 (main, ~20:35): the computability half of the Sturmian material. OPEN, see below.

## Target
- `simple_kazhdan_sofic_group.tex` at origin/main 9047d0d3c (618 lines, md5 274f19367f7f706b05c017af721c3884),
  "Word problems" at l.363; census d11e91f6e. Rows keyed by hash in `metadata/sk-census-rows/skf-approximants.tsv`.

## Sentences (proof of the corollary)
| key | tex | sentence | status | carriers |
|---|---|---|---|---|
| 0ef60d94b97a | 382–386 | X_α is the infinite minimal Sturmian subshift, the closure of the set of codings c(θ), θ ∈ [0,1), c(θ)_t = 1 iff θ+tα mod 1 ≥ 1−α [MorseHedlund, Hedlund44, Lothaire] | formalized | `sturmianCoding`, `sturmianSubshift`, `printedSturmianSubshiftInfiniteIsMinimal` (via `Setting.IsMinimal`), `printedSturmianSubshiftClosureOfCodings` |
| f3c0a7f07e87 | 386–387 | c(θ)_t = 1 iff θ ∈ [−(t+1)α, −tα) mod 1 | formalized | `printedSturmianCodingArc` |
| fecc651a6372 | 387–391 | passing to the closure adds no words; words of length m are the constant values on the arcs between the distinct points −jα mod 1 | formalized | `language_sturmianSubshift`, `printedSturmianEndpointsDetermineWords` |
| 031aa6399d94 | 391 | so α computes L(X_α) | open, claimed | criterion `mem_language_sturmianSubshift_iff_compare`; reduction in `SturmianComputability` |
| d2348c2e37ec | 391–394 | c(θ)_t = ⌊θ+(t+1)α⌋ − ⌊θ+tα⌋; c(θ)_{[0,m)} has ⌊θ+mα⌋ ones, within 1 of mα, so L(X_α) computes α | partial | `printedSturmianOnesWithinOne`; criterion `intCast_lt_mul_iff_forall_mem_language`; reduction in `SturmianComputability` |

skf-degrees keeps the continued-fraction representative and the continuum/isomorphism-invariance sentence.

## Modules (`GroupApproximation/Manuscript/SimpleKazhdanSofic/`)
| module | content | state |
|---|---|---|
| `SturmianSubshift` | codings, `sturmianSubshift α : Subshift Bool ℤ`, floor telescoping, printed statement Props | LANDED c04293088, wire-queued |
| `SturmianSubshiftMinimal` | bounded returns (Dirichlet), occurrence, minimality, infinite, closure of codings | LANDED c04293088, wire-queued |
| `SturmianLanguage` | arc lemma, distinct endpoints, constant words, language = coding words, count of ones | LANDED 5d4049163, wire-queued |
| `SturmianSubshiftSetting` | `isMinimalSubshift_iff_isMinimal`, printed minimality through `Setting.IsMinimal` | LANDED 505979ccf, wire-queued |
| `SturmianLanguageCriterion` | `wordOnes`; `mem_language_sturmianSubshift_iff_compare`: w ∈ L_m iff s_k − s_l − 1 < (k−l)α for all k, l ≤ m, with s the prefix counts; `intCast_lt_mul_iff_forall_mem_language`: for irrational α and b ≥ 1, a < bα iff every word of length b has ≥ a ones | GREEN 0913-204029-93554; landing with this ledger |
| `SturmianComputability` | truth-table reductions in both directions between L(X_α) and α | CLAIM (d8ba0ac04); waiting on the spellings below |

## Dependencies of `SturmianComputability`
- The oracle spelling of α and L(X): skf-degrees' unlanded `WordProblemDegreeStatements` defines `languageOracle S` (0/1
  on codes of `List A`, through `WordGraph.language`) and `slopeOracle α n = ⌊2ⁿα⌋₊ % 2` (binary digits). I've proposed the
  strict Dedekind cut instead. With the cut both reductions are bounded truth tables; binary digits need an unbounded search
  for α ⇒ L(X_α). No reply yet.
- ms-traces-3's unlanded `GroupApproximation/Computability/OracleTruthTable.lean`, for `turingReducible_of_truthTable`.

## For skf-degrees (consume these names)
- `SimpleKazhdanSofic.sturmianSubshift α : Subshift Bool ℤ` instantiates thm:main's X, through
  `printedSturmianSubshiftInfiniteIsMinimal`.
- Words of length m: `WordGraph.language (sturmianSubshift α).carrier m` equals
  `{w | ∃ θ, WordGraph.word (sturmianCoding α θ) 0 m = w}` (`language_sturmianSubshift`). Your `language S` unfolds to it.
- Census: the rows for 031aa6399d94 and d2348c2e37ec are mine. `sk_sentence_census.py --merge` rejects a second lane's row
  on a key if its status differs.
