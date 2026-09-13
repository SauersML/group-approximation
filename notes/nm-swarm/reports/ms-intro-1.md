# Lane ms-intro-1: tex 1–165 (abstract, Introduction opening)

Lead: session nonsofic-existence-49, wave 2 (range audit and fix). Manuscript at origin/main 68481e4d7; tex 1–165 is
unchanged since the census extraction, so census line numbers match here.

## CLAIM

- CLAIM carrier of tex 162–164 (general clause "c ∈ C_G(L) ⇒ ucu⁻¹ commutes with uLu⁻¹", plus "need not commute with
  the rest of L") — `GroupApproximation/Manuscript/NonMFSentences/IntroCompressorCentralizerSentence.lean`
- CLAIM Korchagin sentence (tex 99–102) at the literal printed definition — `GroupApproximation/Manuscript/NonMFSentences/KorchaginLiteralSentence.lean`
- CLAIM (17:20, raised by ms-core-1 through main) closed bridge between the corona form `IsOperatorMF`, which
  `isOperatorMF_of_isLEF` and others produce, and the printed MF definition of tex 87–98 —
  `GroupApproximation/Manuscript/NonMFSentences/IntroMFDefinitionCoronaBridge.lean`. On main before this lane:
  `PrintedMFDefinitionLiteral` (IsCDEOperatorMF ⟺ printed models), `PrintedMFUnitaryModels` (IsCDEOperatorMF ⟺
  pairwise-uniform models, no V_n(1)=1) and the lemma `isCDEOperatorMF_iff_isOperatorMF` (`#audit_axioms` only). No closed
  Prop states IsOperatorMF ⟺ the printed definition.

Both paths are free on disk, on origin and in every `lanes/*.files`; the planned names have no hit on origin or in the
shared tree (checked 2026-09-13 ~17:05).

## Ledger (31 census rows, every sentence of tex 59–165 has a row)

Verdict `OK` means: carriers exist on origin/main, are root-reachable (through `Manuscript/NonMF/Audit/Intro.lean`,
root-imported at `GroupApproximation.lean:4868`, or directly), the endpoint has `#audit_closed_axioms`, and the
statement matches the printed sentence at the printed generality.

| key | tex | status | verdict |
|---|---|---|---|
| 7b8f14aa4de8 | 59 | structural | OK (`\frenchspacing`) |
| 3393c0cf411c | 68 | formalized | OK: `manuscriptNotEveryCountableGroupIsMF` |
| 113e60b5f202 | 69 | formalized | OK: `manuscriptOneSidedCompressionCriterion` (normal (T) K ≤ printedDefect L ⇒ K ≤ Rad_MF) |
| e82d3011b6cb | 72 | formalized | DEFECT, fixed in rows: named only `manuscriptNotEveryCountableGroupIsMF`, which carries none of FG, simple, (T), trivial MF homs, C*_r separable, stably finite, not MF. Carrier is `UnitGroupHeadline.manuscriptUnitGroupHeadline` |
| a16637da7249 | 76 | partial | W1 (torsion-free clause, hgreendlinger); owner: the other swarm |
| cff73e6439ba | 83 | structural | OK |
| 88e8012cb87e | 87 | formalized | OK: `manuscriptIntroductionMFDefinition` (literal V_n(1)=1, multiplicativity, limsup separation ⟺ IsCDEOperatorMF) |
| 6201111b83a0 | 94 | definition | OK: `manuscriptNormalizedMFModelSeparation` |
| b1b04e376fe7 | 99 | formalized | DEFECT, fixed in rows: named the strong-convergence carriers of the next sentence. Carrier is `KorchaginSentence.manuscriptSentence_korchaginFullSequenceSeparation` (IsOperatorMF ⟺ WeakMFApproximation). Literal-shape upgrade CLAIMED above |
| 837b7cffa562 | 102 | formalized | OK: `IsStronglyOperatorMF`, `not_isStronglyOperatorMF_of_not_isOperatorMF` |
| 8d0b87a46a51 | 106 | definition | DEFECT, fixed in rows: "Equivalently, G embeds in U(Q_d)" asserts an equivalence; regraded `formalized` with `manuscriptIntroductionMFDefinition` + `isCDEOperatorMF_iff_isOperatorMF` (arbitrary positive d_n) |
| be1769283b2f | 112 | definition | OK: `PrintedBoundedProductsNullIdeal` |
| d31180a98ce2 | 114 | definition | OK: `CoronaHomomorphism` |
| ad33e493e32f | 116 | formalized | OK: `IsMFAlgebra A ↔ Separable ∧ HasMFEmbedding A` |
| 3f00927a7193 | 117 | structural | OK ("Write") |
| 10e027681ba5 | 122 | definition | OK: `manuscriptSentence_mfRadicalFormula` |
| f2a05ccf5990 | 122 | formalized | OK: `PrintedMFRadicalQuotientIsMFAndLargest` (kernel = Rad_MF, surjective, quotient MF, unique factorization) |
| 5c93c70edc4c | 126 | formalized | OK |
| 5a7e84235409 | 126 | structural | Preview sentence. Its plural "groups" includes the torsion-free Q (W1-partial). Kept structural: the previewed theorems carry their own rows (thm:headline, thm:amenable-trace, thm:torsion-free) |
| 0f8b4d96c68f | 130 | structural | OK |
| 651e122a919e | 134 | definition | OK: `PrintedCliffordWitnessGroup` (audit-intro, 798be51a3) |
| 9930600167a4 | 140 | formalized | OK: `manuscriptSentence_witnessMFHomKillsSign`, root-imported (`GroupApproximation.lean:4938`); the footnote is provenance inside the same sentence |
| 23e47f0da468 | 144 | structural | OK |
| 8766dc520cfb | 146 | formalized | OK: `PrintedIntroUnitGroup` carries simple, trivial MF homs, R_R ≅ R_R ⊕ R_R, H ≅ Aut(R_R), H ≅ GL_n(R), GL_n = EL_n for all n ≥ 2, all proved (Khanh–Thanh is attribution) |
| 374637bc6ac7 | 153 | attribution | OK |
| ec81a8c16b64 | 156 | definition | OK: `PrintedCommutatorConvention` |
| f355d5f61dd8 | 157 | formalized | OK: compression criterion |
| effc40395f2b | 160 | definition | OK: `compressionSet`, `mem_compressionSet_iff` |
| b671ae1aab2b | 162 | formalized | GAP: the general clause "so ucu⁻¹ commutes with uLu⁻¹" is carried only by rank-twelve instances. Carrier CLAIMED above |
| 56d73653208a | 164 | definition | OK: `printedDefect` (the display at 166+ belongs to ms-intro-2) |

## Literature inputs in range

- `\cite{CDE}` (MF definition): definition, literal (`IsCDEOperatorMF`).
- `\cite[Props 2, 7]{Korchagin}`: proved (`exists_weakMFApproximation` plus the local-model converse); no binder.
- `\cite{GaoEtAl,Schafhauser}`: definition of the convention plus a proved contrapositive.
- `\cite{BK}`: definition.
- `\cite{KhanhThanh}`: attribution; every clause proved (`PrintedIntroUnitGroup`).
- `\cite{OAI}`: attribution.

## Progress log

- 17:05 ledger landed with census row corrections for e82d3011b6cb, b1b04e376fe7, 8d0b87a46a51
  (`metadata/nm-census-rows/ms-intro-1.tsv`), db35aee00.
- 17:15 LANDED c28a60924 (probe 0913-170314-63885 GREEN, both modules BUILT):
  - `Manuscript/NonMFSentences/KorchaginLiteralSentence.lean`: `PrintedKorchaginLiteral`,
    `manuscriptSentence_korchaginLiteral`. This is tex 99–102 between the printed model conditions: limsup separation ⟺
    one constant along the full sequence, with V_n(1)=1 kept on both sides. Row b1b04e376fe7 now names it.
  - `Manuscript/NonMFSentences/IntroCompressorCentralizerSentence.lean`: `PrintedCentralizerConjugateCommutes`
    (general), `PrintedConjugateNeedNotCommute` (rank-twelve witness, defect ≠ 1),
    `manuscriptSentence_compressorCentralizer`. Row b671ae1aab2b now names them.
  - Both modules are queued for wiring in `wire-queue.txt`.

- 17:20 LANDED 0f5189f9a (probe 0913-171351-8828 GREEN, BUILT): `Manuscript/NonMFSentences/IntroMFDefinitionCoronaBridge.lean`,
  `PrintedMFDefinitionCoronaForm` and `manuscriptSentence_mfDefinitionCoronaForm`. For every countable G, IsOperatorMF G ⟺
  the printed definition of tex 87–98. Corona-form producers such as `isOperatorMF_of_isLEF` (tex "countable LEF groups
  are MF", raised by ms-core-1) now reach the printed notion by `.mp`. Rows 88e8012cb87e and 8d0b87a46a51 name it; the
  module is queued for wiring.

## State

Every sentence of tex 1–165 is carried by a closed declaration or honestly classified. The exceptions:
- a16637da7249 (abstract, torsion-free clause) stays partial on W1;
- the three new modules (KorchaginLiteralSentence, IntroCompressorCentralizerSentence, IntroMFDefinitionCoronaBridge) await
  root wiring.
Residual statements owned by this lane: none.
