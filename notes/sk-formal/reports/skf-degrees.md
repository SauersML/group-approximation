# skf-degrees: ledger for the word-problem degree section of simple_kazhdan_sofic_group.tex

Lane `skf-degrees` (formalization of the note, lead = session nonsofic-existence-49/ff). This file is written by
skf-degrees only.

## Target
- The briefed version was b965d63ba (970 lines, sec:degrees l.744–835: prop:degree, lem:sturmian, the proof of
  thm:degrees, remark).
- origin/main replaced the note at bf961c128 (09-13 18:54, 340 lines, md5 7b3dc4ec92b4581553bc0dc2b0edcb99). The range
  is now the section "Every word-problem degree", tex l.229–263: one unlabeled corollary and its proof. All keys below
  are `LINE:<n>@bf961c128`.
- Main theorem at bf961c128 (l.44): G_X = EL_3(LC(X,F₂)⋊_T Z) is infinite, finitely generated, simple, Kazhdan and LEF,
  for every infinite minimal subshift X over a finite alphabet. The word problem in the section is WP(G_X) in "the finite
  generators above".

## Sentences (bf961c128 l.229–263)
| key | sentence | status | carrier | note |
|---|---|---|---|---|
| LINE:229 | section heading "Every word-problem degree" | structural | — | |
| LINE:231–235 | Corollary: every Turing degree is the word-problem degree of an infinite simple Kazhdan LEF group; continuum many isomorphism classes | open | none on main | endpoint over thm:main for Sturmian X_α |
| LINE:238–239 | WP(G_X) in the finite generators has the Turing degree of L(X) | open | none | printed route: normal forms with window tables, and cylinder roots |
| LINE:240–241 | an L(X) oracle decides whether a matrix word equals I_3, by checking coefficient tables on allowed windows | open | none | WP ≤_T L(X) |
| LINE:242–246 | cylinder indicator e_[v] = ∏ u^{-t} e_{v_t} u^t, converted effectively via eq:elementary to a word for e_12(e_[v]) | open | none | L(X) ≤_T WP; commutator identities on main (Pestov91 SimpleModCentre `elGen`) |
| LINE:247–248 | that word equals 1 exactly when v ∉ L(X) | open | none | via e_12(f) = 1 ⇔ f = 0 (no centre quotient at bf961c128) |
| LINE:250–251 | the Sturmian subshift of irrational slope α ∈ (0,1) is infinite and minimal [MorseHedlund] | open | none | Morse–Hedlund must be PROVED if used as a step |
| LINE:251–253 | its language is computable from α, via the cyclic order of the endpoints −jα mod 1 | open | none | |
| LINE:254–255 | the minimum number of 1's in a word of length n is ⌊nα⌋, so the language computes α | open | none | needs the Sturmian balance property |
| LINE:256–258 | every degree has an irrational representative (√2−1; interleaving a noncomputable set with 1's) | open | none | |
| LINE:259–261 | continuum many degrees; the word-problem degree of a f.g. group is an isomorphism invariant | open | none | independence of the generating set |

## Available infrastructure (origin/main, pin 81a5d257)
- Mathlib: `Mathlib/Computability/TuringDegree.lean` (`TuringReducible`, `TuringEquivalent` for ℕ →. ℕ, `TuringDegree`), `Reduce.lean`.
- Repo: `GroupApproximation/Computability/*` (word problems of presentation codes, Adian–Rabin, Boone), `Dynamics/SubshiftWordGraph.language`.
- Pestov91 (root-imported): `X` is one concrete Toeplitz carrier, not a general subshift; `Centre.elementaryUnit_mem_center_iff`; `SimpleModCentre` commutator calculus.
- Cairn proof source, not a carrier: `research/subshift-elementary-group-word-problem-degree{,-proof}.md`.

## Status
- CLAIM: statements module `GroupApproximation/Manuscript/SimpleKazhdanSofic/WordProblemDegreeStatements.lean` (named Props
  for the corollary and its steps, over Mathlib's `TuringEquivalent`). Development size is reported to main before large
  infrastructure is built.
