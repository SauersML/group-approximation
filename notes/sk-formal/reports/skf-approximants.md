# skf-approximants: ledger

Lane brief: `ct/ROSTER-sk.md` (session nonsofic-existence-49). Only skf-approximants writes this file.

## History
- Item 1 was tex 459–514 of b965d63ba (subsec:approximants: prop:marked, rem:fibonacci). At bf961c128 the note was replaced
  by its shortened version, and that range has no counterpart. No Lean was built for it and no rows were landed.
- Item 2 (main, ~19:05, re-scoped 19:45 and 20:15): help skf-degrees on "Word problems", covering the Sturmian subshift and
  the Morse–Hedlund input. skf-degrees keeps the computability and Turing-degree sentences; ms-traces-3 has (c)
  WP ≤_T L(X).

## Target
- `simple_kazhdan_sofic_group.tex` at origin/main e80dcf20a (386 lines, md5 4ad4921253626a4f858866c716a13385); census
  09e580c38. Rows are keyed by 12-hex hash and live in `metadata/sk-census-rows/skf-approximants.tsv`.

## Sentences (proof of the corollary, "Word problems")
| key | tex | sentence | status | carriers |
|---|---|---|---|---|
| 35b84b78c130 | 261–264 | X_α is the infinite minimal Sturmian subshift, the closure of the codings c(θ), θ ∈ [0,1), with c(θ)_t = 1 iff θ+tα mod 1 ≥ 1−α [MorseHedlund] | formalized | `sturmianCoding`, `sturmianSubshift`, `printedSturmianSubshiftInfiniteIsMinimal` (through `Setting.IsMinimal`), `printedSturmianSubshiftClosureOfCodings` |
| 11d7d47b8ab0 | 264–268 | c(θ)_t = 1 iff θ ∈ [−(t+1)α, −tα) mod 1; words of length n are the constant values on the arcs between −jα mod 1 | formalized | `printedSturmianCodingArc`, `printedSturmianEndpointsDetermineWords` |
| 031aa6399d94 | 268 | so α computes L(X_α) | skf-degrees | — |
| 6f639125d339 | 268–271 | c(θ)_t = ⌊θ+(t+1)α⌋ − ⌊θ+tα⌋; c(θ)_{[0,n)} has ⌊θ+nα⌋ ones, within 1 of nα, so L(X_α) computes α | partial | `printedSturmianOnesWithinOne`; the "computes α" clause is skf-degrees' |

The Morse–Hedlund input is proved, not cited. The proof goes: bounded returns of an irrational rotation, from Mathlib's
Dirichlet approximation (`exists_bounded_return`); right windows of codings; every coding word occurs in every point;
minimality; non-periodic codings, hence infinite. Every endpoint carries `#audit_closed_axioms`.

## Modules (`GroupApproximation/Manuscript/SimpleKazhdanSofic/`)
| module | content | state |
|---|---|---|
| `SturmianSubshift` | codings, `sturmianSubshift α : Subshift Bool ℤ`, floor telescoping, printed statement Props | LANDED c04293088, wire-queued |
| `SturmianSubshiftMinimal` | bounded returns, occurrence, minimality, infinite, closure of codings | LANDED c04293088, wire-queued |
| `SturmianLanguage` | arc lemma, distinct endpoints, words constant between endpoints, language = coding words, count of ones | LANDED 5d4049163, wire-queued |
| `SturmianSubshiftSetting` | `isMinimalSubshift_iff_isMinimal`; the printed infinite-and-minimal Prop through `Setting.IsMinimal` | GREEN 0913-202452-61135; landed with this ledger |

## For skf-degrees (consume these names)
- Census: the row for 6f639125d339 is mine, as `partial`, for the combinatorial clause. `sk_sentence_census.py --merge` rejects
  a second lane's row on the same key if its status differs, and keeps the first. When your "so L(X_α) computes α" carrier
  lands, message skf-approximants: I'll drop my row, and you land one row with both sets of decls.
- `SimpleKazhdanSofic.sturmianSubshift α : Subshift Bool ℤ` instantiates thm:main's X, through
  `printedSturmianSubshiftInfiniteIsMinimal`.
- Words of length n: `WordGraph.language (sturmianSubshift α).carrier n : Set (Fin n → Bool)` equals
  `{w | ∃ θ, WordGraph.word (sturmianCoding α θ) 0 n = w}` (`language_sturmianSubshift`).
- Membership through the endpoints: `sturmianCoding_eq_true_iff` and `sturmianCoding_word_eq_of_endpoints`. Counting:
  `count_word_sturmianCoding`, giving ⌊θ+nα⌋ − ⌊θ⌋ ones.

## Item 3 (main, ~20:35): computability half of the Sturmian material
Split with skf-degrees:
- mine: 031aa6399d94 ("so α computes L(X_α)"), and the clause "so L(X_α) computes α" of 6f639125d339 (my row goes to
  `formalized` when it closes);
- skf-degrees': cf009a26e807 (continued-fraction representative) and 34a4980e33db (continuum many degrees, isomorphism
  invariance).

CLAIM SturmianLanguageCriterion `GroupApproximation/Manuscript/SimpleKazhdanSofic/SturmianLanguageCriterion.lean`: with
prefix sums s_k of v, v ∈ L_n(X_α) iff (s_k − s_l − 1)/(k − l) < α for all l < k ≤ n and α < (s_l − s_k + 1)/(l − k) for
all k < l ≤ n. That's finitely many strict comparisons of α with rationals. Also: ⌊nα⌋ is the least number of ones of a word
of length n of X_α.
CLAIM SturmianComputability `GroupApproximation/Manuscript/SimpleKazhdanSofic/SturmianComputability.lean`: for irrational
α ∈ (0,1), truth-table reductions in both directions between L(X_α) and α (as an oracle, the spelling agreed with
skf-degrees), over `Nat.RecursiveIn` / `TuringReducible`.
