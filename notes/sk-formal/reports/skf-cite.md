# skf-cite: citation ledger for `simple_kazhdan_sofic_group.tex`

Lane skf-cite, 2026-09-13 ~19:00 CDT. Scope: every `\cite` used as a proof step, plus the origin/authorship section and
the bibliography.

## Target text

- origin/main at bf961c128 (18:54, "Replace the sofic simple Kazhdan note with its shortened version"): 340 lines, md5
  7b3dc4ec92b4581553bc0dc2b0edcb99.
- ROSTER-sk targeted b965d63ba (970 lines, md5 3a11a03d…); that version is superseded on main. All line numbers below are
  at bf961c128.
- The current note: abstract and introduction 1–65 (thm:main at 44); §1 proof 67–227 ("The ring and property (T)" 69–116,
  "Finite models" 118–152, "A finite tower detects every normal subgroup" 154–227); §2 word-problem-degree corollary
  229–262; origin and authorship 264–269; bibliography 271–339.
- Citations of the b965d63ba version that no longer occur: Kirchberg, Dadarlat, CDE, Gromov, Caprace–Rémy, Weiss,
  Vershik–Gordon, Elek–Szabó, NonMF.

## Ledger

| line | cite | use | Lean carrier (origin/main) | verdict |
|---|---|---|---|---|
| 39 | Brown §11 Q7 | attribution (the question) | none needed | attribution |
| 40 | Ozawa p. 527 | attribution (hyperlinear form of the question) | none needed | attribution |
| 41 | Pestov | attribution (Open question 9.1, sofic form) | none needed | attribution |
| 55 | Nekrashevych | credit ("the subshift algebra is classical") | none needed | attribution |
| 56 | EJZ | credit in the introduction | step at 97–99 | attribution |
| 58 | Grigorchuk–Medynets | credit for the periodic-approximation mechanism; the note proves the finite models directly at 118–149 | the finite-models carriers belong to the range lane for 118–152 | attribution |
| 62 | Stepanov | credit (normal-structure tradition) | none needed | attribution |
| 64 | Thom Thm 1.4 | context (a Kazhdan LEF non-RF group, not simple) | none needed | attribution |
| 97–99 | EJZ Thm 1.1 | STEP: EL_n(R) has (T) for every finitely generated unital associative ring R, n ≥ 3 | `ejz : FinitelyGeneratedRingGeneralRankElementaryPropertyT` (Manuscript/OneSidedMFRadical/FullDefectRingEJZUnconditional.lean:46, `#audit_closed_axioms ejz` at l.154), through `IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT` (PropertyT/IntegralColumnPlaneClosure.lean:486). Both modules are root-direct. ms-inverses-3 and ms-inverses-4 verified this carrier as closed at the printed generality in the non-MF audit. | PROVED |
| 103 | BCFS, Clark–Edie-Michell, Steinberg | credit ("standard groupoid-algebra facts; here is the direct argument") | the direct argument at 104–116 belongs to the range lane for 69–116; candidates are Pestov91/RingSimple and Centre | attribution |
| 150–152 | Pestov | STEP: regular permutation actions of the finite models give sofic models, and permutation matrices give hyperlinear models (LEF ⇒ sofic ⇒ hyperlinear) | `isSofic_of_isLEF` (Sofic/LEFSofic.lean:85), `isHyperlinear_of_isSofic` (Sofic/Hyperlinear.lean:175), `isHyperlinear_of_isLEF` (Pestov91/LEFHyperlinear.lean:44); all three modules are root-direct | PROVED, provisionally. None of the three modules has an `#audit` line, so the axiom audit is owed; the check that the proof follows the printed route is owed to the range lane for 118–152 |
| 252 | Morse–Hedlund | STEP: the infinite minimal Sturmian subshift of an irrational slope α exists; its language is computable from α; the minimum number of 1s in a word of length n is ⌊nα⌋ | NONE on origin: `git grep -i sturmian` over GroupApproximation is empty | ASSUMED, GAP; owner is the range lane for 229–262 (ROSTER-sk's skf-degrees) |

## Results in the range with no carrier at all

These are not citations, but they block the §2 rows.

- **Word problem ≡_T L(X), both directions (tex 238–249):** no Lean carrier on origin. The Cairn node
  `subshift-elementary-group-word-problem-degree` (artifact `research/artifacts/subshift-elementary-group-turing-degrees-2026-09-12.md`)
  is paper-level only.
- **Every Turing degree has an irrational representative, and continuum many isomorphism classes (tex 257–261):** no
  Lean carrier.

## Origin, authorship and bibliography (tex 264–339)

- 264–269: attribution rows (who found, wrote, shortened; responsibility; repository pointer).
- 271–339: thirteen bibliography entries, graded structural.

## Cited results still assumed in the proof

1. Morse–Hedlund (tex 252): Sturmian subshift existence, minimality and complexity, the language computable from α, and
   the ⌊nα⌋ count.
2. Provisional only: Pestov's LEF ⇒ sofic ⇒ hyperlinear (tex 150–152) has carriers, but their axiom audit and route check
   are owed.

EJZ Theorem 1.1 is proved. Every other citation in the note is credit or attribution.
