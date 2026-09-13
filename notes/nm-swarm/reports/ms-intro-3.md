# Lane ms-intro-3: tex 233–294 (thm:headline, thm:amenable-trace), except 249–259 (ct lanes)

Lead: session nonsofic-existence-49 (wave 2). Snapshot: origin/main 62471b165; tex last changed at 73a84cd9c, and this
range is textually unchanged since the census extraction. Keys and grades come from `metadata/NON_MF_SENTENCE_CENSUS.tsv`
and `metadata/NON_MF_SENTENCE_MAP.tsv`.

## Ledger

| tex | sentence (abridged) | key | grade on main | carriers | verdict |
|---|---|---|---|---|---|
| 234 | Let R=L_F2(1,2) and let H=R^× be its unit group. | fa08e9082236 | definition | `UnitGroupHeadline.manuscriptUnitGroupHeadline` (R = `UniversalLeavitt.BinaryLeavittAlgebra`) | OK |
| 234–236 | Then H≅EL_4(R), and H is nontrivial, f.g., simple, and has (T). | 63c2a4ca81c4 | formalized | `manuscriptUnitGroupHeadline : PrintedUnitGroupHeadline`, closed; `#audit_closed_axioms` in the module and in Audit/Intro.lean:229; root-imported | OK: clauses `Nonempty (Rˣ ≃* H)` with H = `BinaryLeavittSteinberg.ElementaryBase 4`, `Group.FG`, `Nontrivial`, `IsSimpleGroup`, `HasKazhdanPropertyT`; the Khanh–Thanh identification is proved (`BinaryLeavitt.elementaryGroup_eq_top`) |
| 236–237 | Every homomorphism from H to an MF group is trivial. So H is not MF, | 664f4f34b841 (joint) | formalized | same | OK: `∀ M countable, IsCDEOperatorMF M → f trivial`, `¬ IsCDEOperatorMF Rˣ` |
| 237–239 | C*_r(H) is separable and stably finite but not MF, while C*_max(H) is not finite: it contains a proper isometry. | 664f4f34b841 | formalized | same | GAP (literal clause): the carrier gives the strict projection configuration `P < vPv*` and `¬IsDedekindFiniteMonoid`/`¬IsStablyFiniteRing` of C*_max(Rˣ), but no proper isometry `∃ s, star s * s = 1 ∧ ¬IsUnit s`. CLAIM P1 below. |
| 243–246 | For a countable PIS ring R and n≥1, thm:mf-quotient-units identifies Rad_MF(GL_n(R)) with the commutator subgroup, and the largest MF quotient with K_1(R). | 0e0ede2715c4 | formalized | `MFQuotientUnitsKOne.manuscriptMFQuotientUnitsKOneAtBaseRing` (closed, audited at Audit/Intro.lean:233) | OK |
| 246–247 | For the unit group of L_k(1,d) the quotient is k^×/(k^×)^{d−1}. | 2d6ab84875e0 | formalized | `LeavittKOneFormulaSentences.manuscriptSentence_unitGroupQuotient` (binders: countable field k, d≥2, which is the generality of cor:leavitt-mf-quotient; `#audit_axioms`) | OK. The closed endpoint `manuscriptLeavittMFQuotientFull : PrintedLeavittMFQuotientFull` also carries it; add it to the row |
| 263–264 | There is a sofic group W=W_0⋊Z, with W_0 locally RF, that is not MF. | d4c878a7ac22 | formalized | `AmenableTraceTheorem.manuscriptAmenableNonquasidiagonalTrace` (closed, audited) | OK: `∃ W K φ, W ≃* K ⋊[φ] ℤ ∧ IsLocallyResiduallyFinite K ∧ IsSofic W ∧ ¬IsOperatorMF W` |
| 264–266 | The canonical trace on C*_max(W_0) is QD; on C*_max(W) it is amenable and not QD. | cd72291264e4 | formalized | same | OK |
| 270–271 | sec:amenable-nonqd constructs W from Z^3⋊SL_3(Z) and Clifford lamps. | a3db1a0910d5 | structural | — | OK (roadmap) |
| 271–274 | W is sofic because locally RF groups are sofic and soficity passes to extensions with amenable quotient [ElekSzabo Thm 1]. | f969236a73d8 | formalized | `manuscriptWSoficFromLocallyRFExtension` (closed, audited) via `isSofic_of_locallyResiduallyFinite` and `SoficByAmenablePermanence.isSofic_int_semidirectProduct` | OK. The general permanence is also proved: `SoficByAmenablePermanence.isSofic_of_isSofic_ker_of_isAmenable`; add it to the row |
| 274–277 | The trace answers the question of Brown and of STW Problem X(1), whether every amenable trace is QD. | a96c09324a87 (the splitter joins it with 279–282) | formalized (note: "attribution") | none for this clause | The negative answer is mathematics. `NinetyNineProblems.not_problemX1Statement : ¬ ProblemX1Statement.{1}` is closed, audited and root-imported, but its witness is the marked group E, not W. Checking for a W-witness form; otherwise CLAIM P2 |
| 279–282 | TWW proved ...; here C*_max(W) is not nuclear, since W is not amenable. | a96c09324a87 | formalized | `manuscriptSentence_maximalCStarWNotNuclear` (+ Lance at the maximal algebra, `witnessGroup_not_isAmenable`) | TWW clause is attribution (used in no proof); second clause OK |
| 282–284 | The canonical trace of C*_max(W_0) is QD, so the crossed product by Z destroys QD of the canonical trace. | c4870fed3d2b | formalized | `manuscriptAmenableNonquasidiagonalTrace` | OK |
| 284–286 | W_0 is a direct limit of RF groups, so it is MF [Korchagin]. | 2a97fb901bad | formalized | `manuscriptShiftKernelIsOperatorMF : IsOperatorMF ShiftKernel` (closed, audited) via locally RF ⇒ LEF ⇒ operator MF | OK; the Korchagin input is proved in Lean |
| 286–288 | So MF groups are not closed under semidirect products with Z (Korchagin's question). | cd3ea932e46a | formalized | `manuscriptMFNotClosedUnderIntSemidirect` (closed, audited) | OK |
| 292–293 | Every example above has torsion, and in the lamp construction the obstruction is itself a torsion element. | 80279f06992b | structural | — | GAP: a checkable mathematical claim graded structural. CLAIM P3 below |
| 293 | The last group has none. | abb56744db26 | structural | `TorsionFreePrinted.PrintedTorsionFreeTheorem` (a def) | RE-GRADE to partial: this is the torsion-free clause of thm:torsion-free, over hgreendlinger (W1, owned by the other swarm) |

## Claims

- CLAIM P1: the headline C*_max clause as a literal proper isometry. Module
  `GroupApproximation/Manuscript/NonMFSentences/HeadlineMaximalProperIsometry.lean`.
- CLAIM P3: torsion in the introduction's examples, and the lamp obstruction ε is a nontrivial involution. Module
  `GroupApproximation/Manuscript/NonMFSentences/IntroExamplesTorsion.lean`; a generic swap-involution lemma possibly
  goes in its own module.

## Closed

- P1 LANDED f168ac24e (probe 0913-171403-10145 GREEN, BUILT). Module `Manuscript/NonMFSentences/HeadlineMaximalProperIsometry`,
  endpoint `manuscriptSentence_headlineMaximalProperIsometry : PrintedHeadlineMaximalProperIsometry` (closed, audited).
  It is `¬IsDedekindFiniteMonoid (MaximalGroupCStar Rˣ) ∧ ∃ v, star v * v = 1 ∧ ¬IsUnit v`, via
  `FullDefectRing.properIsometry_of_strictCompression unitCorner unitCompressor`. Queued for wiring.
- P2 LANDED a236f65c4 (probe 0913-172932-66219 compiled). Module `Manuscript/NonMFSentences/AmenableTraceAnswersProblemX`,
  endpoint `manuscriptSentence_amenableTraceAnswersProblemX1 : PrintedAmenableTraceAnswersProblemX1` (closed, audited).
  It gives the W of thm:amenable-trace with its canonical maximal tracial state amenable and not quasidiagonal, and
  `¬ NinetyNineProblems.ProblemX1Statement.{1}` through that W. Queued for wiring.
- Census rows 773d78e20: 664f4f34b841 and a96c09324a87.

- P3 LANDED 68559b320 (probe 0913-174325-21575 GREEN, both BUILT).
  - `Algebra/IdempotentSwapInvolution`: `IdempotentSwap.SwapData` (the swap `1 - e - f + a + b` squares to 1 and is
    not 1 when `e ≠ 0`), with producers `ofIsometry` and `ofOrthogonalIsometries`, and
    `exists_isOfFinOrder_ne_one_of_isometry` / `_of_orthogonalIsometries`.
  - `Manuscript/NonMFSentences/IntroExamplesTorsion`: `manuscriptIntroExamplesTorsion : PrintedIntroExamplesTorsion`
    (closed, audited). Torsion in L_F2(1,2)^×, GL_n(R) for PIS R, L_k(1,d)^×, EL_n over nontrivial rings with p·1 = 0
    (the R_X examples), and W; the Clifford sign of every lamp witness is a nontrivial central involution killed by
    every hom to an operator-MF group.
  - Queued for wiring. Census rows d9800fe3b: 80279f06992b formalized, abb56744db26 regraded to partial.

## Verification notes

- The headline's MF clause quantifies over countable targets `M`. That matches the printed definition: tex 87–88,
  "A countable group G is MF".
- Root reachability: UnitGroupHeadline, AmenableTraceTheorem, MFQuotientCanonicalKOne, LeavittKOneFormulaSentences and
  MaximalCStarWNotNuclearUnconditional are directly imported by GroupApproximation.lean.
- No literature binder in the chains: the Khanh–Thanh identification is proved (`BinaryLeavitt.elementaryGroup_eq_top`);
  the K_1 endpoint has no AGP or Morita input; the amenable-trace chain discharges
  `PrintedLocallyRFCanonicalTraceQuasidiagonal` by `AmenableExtensionTrace.manuscriptPrintedLocallyRFCanonicalTraceQuasidiagonal`;
  Korchagin's input is `isOperatorMF_of_isLEF ∘ isLEF_of_locallyResiduallyFinite`; Elek–Szabó's permanence is proved in
  `SoficByAmenablePermanence`.

## Range status

Every sentence of tex 233–294 (except 249–259) is carried by a closed, root-reachable declaration or honestly
classified. The one remaining partial row (abb56744db26) waits on hgreendlinger, owned by the other swarm.

## Notes for the census lane (no landing of mine needed)

- 2d6ab84875e0: add the closed endpoint `LeavittKOneFormulaSentences.manuscriptLeavittMFQuotientFull` next to
  `manuscriptSentence_unitGroupQuotient` (the latter is `#audit_axioms` with binders at the printed generality).
- f969236a73d8: the general permanence the sentence asserts is proved too
  (`SoficByAmenablePermanence.isSofic_of_isSofic_ker_of_isAmenable`); worth naming in the row.
- abb56744db26 ("The last group has none."): regrade `structural` to `partial`. It is the torsion-free clause of
  thm:torsion-free, whose carriers are over hgreendlinger (the W1 wall, other swarm).
- 80279f06992b: to be regraded `formalized` when P3 lands.

## Item 2 (main ~18:30): the Y-pocket twin of the Case 1 X-pocket reduction (W1 binder 3)

CLAIM the Y-pocket statement of Lemma 9.4 Case 1 across one relator cell, the connector-pair swap, and the Y reduction to
the five X shape statements — `GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94SameCellYPocket.lean`. Path and names
are free on origin, in the shared tree and in every `lanes/*.files` (checked ~18:35).

Definition audit (the symmetry is real, no Y-only premise):
- `WordConnectorPair` (UnboundWordConnectors:23) swaps source and target with `a := b'`, `a' := b`, `b := a'`, `b' := a`,
  `startConnector := endConnector` and `endConnector := startConnector`. `start_geodesic` and `end_geodesic` swap literally,
  `source_forward` is the backward hypothesis `b' < b`, and the `_long` fields hold by `wordDist_comm`.
- The side sets are the only asymmetry: `source_mem : source ∈ relatorSides k = {i | ∃ j, kind k i = .cell j}`,
  `target_mem : target ∈ longSides k = {i | kind k i ≠ .short}`. In the same-cell case `kind source = kind target = .cell j`, so
  the old target is a relator side and the old source is a long side.
- Face walk `X q⁻¹ Y p⁻¹` rotated by `(X ++ q⁻¹).length` is `Y p⁻¹ X q⁻¹`; carrier `q B p A` rotated by `(q ++ B).length` is
  `p A q B`. The value equations `hsource`/`htarget` and `hX`/`hY` trade places.
- So the Y-pocket for `C` is the X-pocket for the swapped pair with `X := Y`, `B := A`, for every shape.

## Progress log

- 16:5x ledger v1.
- 17:19 lead restart; resumed. P1, P2 landed; rows landed; P3 re-probing.
