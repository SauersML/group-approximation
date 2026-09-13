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

## Progress log

- 16:5x ledger v1.
