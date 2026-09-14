# skf-approximants — ledger for tex 459–514 of simple_kazhdan_sofic_group.tex

Lane brief: `ct/ROSTER-sk.md` (session nonsofic-existence-49), range tex 459–514 at origin/main b965d63ba (subsec:approximants:
prop:marked, rem:fibonacci).

## Blocker: the committed note changed underneath the range

- At 18:54 origin/main landed bf961c128, "Replace the sofic simple Kazhdan note with its shortened version". The committed
  `simple_kazhdan_sofic_group.tex` is now 340 lines, md5 7b3dc4ec92b4581553bc0dc2b0edcb99. The roster target b965d63ba was
  970 lines, md5 3a11a03d23cb580bd629d313a6b7a1c1.
- The new text has no subsection "Finite simple approximants", no `prop:marked` and no `rem:fibonacci`. The
  PSL_{3N}(F_q) → S marked-group convergence and the Fibonacci first model (SL_15(F_p)) are not in the committed note.
- Nothing in the current note corresponds to tex 459–514:
  - its "Finite models" subsection (current tex 118–153) carries the LEF models, which were b965d63ba's sec:lef material;
  - Morse–Hedlund is cited only in the word-problem section (current tex 252), for Sturmian complexity.
- So there is no sentence to formalize in this range at the current tip. I built no Lean and appended no census rows.

## Structure of the committed note (bf961c128, 340 lines), for a re-split

| current tex | content |
|---|---|
| 1–66 | title, abstract, introduction, `thm:main` (l.44) |
| 67–117 | "Proof of Theorem 1": the ring and property (T), `eq:elementary` (l.88) |
| 118–153 | "Finite models": LEF models over F_2, entrywise; sofic and hyperlinear models |
| 154–228 | "A finite tower detects every normal subgroup", `eq:absorb` (l.168); includes GL_d(F_2) = SL_d(F_2) = PSL_d(F_2) (l.217) |
| 229–263 | "Every word-problem degree", the corollary (l.231); Morse–Hedlund for Sturmian complexity (l.252) |
| 264–340 | "Origin and authorship", bibliography |

The roster's label table (thm:degrees, lem:subshift, prop:simple-ring, lem:windows, prop:ultraproduct, lem:level, thm:root,
cor:consequences, prop:degree, ...) refers to b965d63ba and is obsolete at the tip.

## Item 2 (main, ~19:05): help skf-degrees on tex 229–263 at bf961c128

Split proposed to skf-degrees in one message:
- mine: the Morse–Hedlund input and the Sturmian combinatorics, rows l.250–256;
- skf-degrees': WP(G_X) ≡_T L(X), computability wrappers, Turing representatives, continuum many, isomorphism invariance.

Sentences (keys `LINE:<l>@bf961c128`):
| key | sentence | owner |
|---|---|---|
| LINE:250–251 | "the infinite minimal Sturmian subshift of an irrational slope α ∈ (0,1)" [MorseHedlund] | skf-approximants |
| LINE:251–253 | "words of length n are determined by the cyclic order of the distinct rotation endpoints −jα mod 1, 0 ≤ j ≤ n" (combinatorics; "computable from α" is skf-degrees') | skf-approximants |
| LINE:254–255 | "the minimum number of 1's in a word of length n is ⌊nα⌋" ("so the language computes α" is skf-degrees') | skf-approximants |

CLAIM SturmianSubshift `GroupApproximation/Manuscript/SimpleKazhdanSofic/SturmianSubshift.lean` (definitions of the codings
and X_α, named statement Props M1–M3)
CLAIM SturmianSubshiftMinimal `GroupApproximation/Manuscript/SimpleKazhdanSofic/SturmianSubshiftMinimal.lean` (M1: X_α
closed, shift-invariant, infinite, minimal; proved by bounded-gap density of irrational rotation, no literature input)
CLAIM SturmianLanguage `GroupApproximation/Manuscript/SimpleKazhdanSofic/SturmianLanguage.lean` (M2: words are constant
between consecutive endpoints, and the endpoints are distinct; M3: the minimum number of 1's is ⌊nα⌋)
