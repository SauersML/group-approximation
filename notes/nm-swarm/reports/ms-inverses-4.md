# Lane ms-inverses-4: tex 1050–1174 (cor:one-sided-ring-maximal, prop:torsion-defect-ring, the Toeplitz–Jacobson remark)

Wave-2 range lane of session nonsofic-existence-49; brief "Brief R" in that session's `ct/ROSTER-wave2.md`.
Snapshot: origin/main 61363f1b9 (tex 1050–1174 byte-identical to 68481e4d7). Census rows come from
`metadata/NON_MF_SENTENCE_CENSUS.tsv`, matched by sentence text; every census sentence of the range is present verbatim
in the current tex.

## Status (2026-09-13 ~17:10)

The range is clean. Every sentence is carried by a closed, root-reachable declaration or honestly classified, and one
fidelity gap was closed by f797a21d6. The new module is queued for wiring.

## Ledger (45 rows; tex lines at 61363f1b9)

| key | tex | status | carriers (short) | verdict |
|---|---|---|---|---|
| 18fd64bafd97 | 1051 | definition | FullDefectRing.PrintedOneSidedRingMaximalIsometry | ok |
| 7b383805ef7a | 1051–1053 | formalized | FullDefectRingEJZUnconditional.manuscriptOneSidedRingMaximalIsometryAllCharacteristics | ok: countable unital, not directly finite, n ≥ 4; closed audit |
| fa3d9aa8ce2c | 1053–1056 | formalized | …ReducedCStarRankTwoAllCharacteristics, …UnitGroupNotMFAllCharacteristics (+ IsometryRankTwo) | ok: fullness spelled ∃ m a b, Σ a_k e b_k = 1; R ≠ 0 as Nontrivial; closed audits |
| 27586e96ecfe | 1063 | formalized | OneSidedSentences.manuscriptSentence_oneSidedMaximalChooseSubring | ok |
| b45891d88426 | 1065–1068 | formalized | strictCompressionWitness, oneSidedMaximalStrictCompression, pairSubringElementaryPropertyT | ok; [EJZ] closed (IntegralColumnPlaneClosure) |
| 900689d5c4ac | 1068–1070 | formalized | oneSidedMaximalProperIsometry | ok |
| 2ff745dd7064 | 1072–1075 | formalized | PrintedElementaryGroupNotMF, manuscriptElementaryGroupNotMFAllCharacteristics | ok |
| 518cbfd6417d | 1076–1077 | formalized | reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra | ok: stable finiteness from the canonical faithful trace; not MF through the MF embedding |
| 88cdb5eaabb4 | 1078–1081 | formalized | oneSidedMaximalJInjective, UnitGroupRankDescent.isOperatorMF_of_injective | ok |
| 06d71da2d355 | 1081 | formalized | oneSidedMaximalUnitGroupNotMF | ok |
| 5970e738b4d9 | 1085–1086 | formalized | PrintedTorsionComplementaryIdempotents, manuscriptTorsionComplementaryIdempotents | ok: printed generality (countable unital R, ts = 1, ∃ m ≥ 1, m•e = 0); closed audit |
| ed1dd8699cf4 | 1086–1089 | formalized | manuscriptTorsionComplementaryIdempotents, relativeElementary_le_mfHomKernel | ok (the display is carried) |
| 7774b0de0638 | 1090 | definition | relativeElementary (normal closure in EL_n(R) of e_ij(a), a ∈ I) | ok |
| ef7c374310ee | 1091–1092 | formalized | not_isCDEOperatorMF_of_pair, manuscriptPositiveCharacteristicDirectFiniteness | ok |
| cb0f08ae60a3 | 1096 | formalized | manuscriptSentence_zeroIdempotentCase | ok |
| 057fe08fb3bb | 1097–1099 | formalized | pairSubringCoreKazhdan, pairSubringElementaryPropertyT | ok; [EJZ] closed |
| 1538c6bcbbec | 1099–1101 | formalized | centralFiniteOrderInDefect | ok |
| 1246801a6fc6 | 1101 | definition | fUnit | ok |
| 647f63b250b2 | 1102 | formalized | manuscriptSentence_matrixUnits | ok |
| 6efe099d7fdb | 1103–1104 | formalized | lastDiag, diagonalCommutators | ok: [e_41(f_ii), e_14(±f_ij)] = D(1 ± f_ij) |
| 8113a9d8c968 | 1105–1106 | formalized | compressorWeylAndV | ok: w_ij, r = w_14 w_25, v = u D(r) |
| 84ce319a4f15 | 1107 | formalized | vCompressesCore | ok |
| 7eeed19cdc69 | 1107–1113 | definition | printedCell, printedB (the unnumbered display) | ok |
| ee85d796d83a | 1114–1116 | formalized | conjugationsByV | ok: all four identities, v c v⁻¹ = e_14(f_02), v z v⁻¹ = z |
| aeeaaeadaad3 | 1117–1119 | formalized | defectElementAndZ | ok: d = e_24(−f_02) (printedDefectElt), [y,d] = D(1 − f_12) = z⁻¹ |
| bc99235426ad | 1119–1121 | formalized | zCentral | ok |
| 5b7bdf2351a7 | 1121–1122 | formalized | zOrderAndNontrivial | ok |
| 9627d330af8b | 1123–1126 | formalized | criterionKillsCentralElement | ok |
| 7634d6cc067b | 1126–1129 | formalized | twoCommutatorsKilled (the display identities, and the kills along the pair subring) | ok |
| f40da910f45b | 1130–1131 | formalized | sandwichesAndRelativeElementaryKilled, relativeElementary_span_le_of_elGen_mem | ok |
| bbf924af98ec | 1131 | formalized | rootNeOne | ok |
| 885d8e36762a | 1132–1133 | formalized | manuscriptSentence_positiveCharacteristic | ok |
| b47d06c5c362 | 1136–1140 | formalized | JacobsonSymbol.jacobsonQuotientLaurent; JacobsonPresented.PrintedToeplitzJacobsonAlgebra | ok (presented J) |
| 0a08ffd095d6 | 1140–1141 | formalized | JacobsonPresented.PrintedToeplitzJacobsonRadicalEquality | ok (presented J) |
| 11137e57b26d | 1142–1145 | formalized | JacobsonPresented.PrintedToeplitzJacobsonShiftAction | ok (presented J) |
| 76588fb18d3b | 1145–1147 | formalized | FinitaryLinear.binaryGLfs, finiteSupportStrongerThanFiniteRank | ok |
| d5e56b196927 | 1148 | formalized | JacobsonPresented.PrintedToeplitzJacobsonKernelFinitary | ok (presented J) |
| 7c69447e3d41 | 1149–1152 | formalized | binaryGLfsProductOfTransvections, blockAct_elGen_matUnit, blockAct_commutator_matUnit | ok |
| 754a868fc8f5 | 1152–1158 | formalized | JacobsonPresented.PrintedToeplitzJacobsonRadicalSLUnion (NEW, f797a21d6); JacobsonLaurent.*, JacobsonSymbol.jacobsonRadical, radicalEquivSLUnion | FIXED: the clause ≅ ⋃_N SL_N(F_2) was carried only for the operator model `jacobsonAlgebra`. It is now stated and proved for the presented J (kernel, residually finite MF target, radical equality, isomorphism, infinite simple locally finite). |
| 6ba4fb85570c | 1159 | formalized | binarySLUnionInfiniteSimpleLocallyFinite | ok |
| 61b6abd03b91 | 1159–1160 | formalized | JacobsonRankFour.fourthCoordinateMakesCompressionInvertible | ok |
| b6d1590be7ab | 1160–1165 | formalized | GHW.printedGHWTheoremFour (closed at every field, GHWTheoremFourClosed), PrintedPresentedJacobsonRankTwoKazhdanFiniteField | ok; [GHW] closed |
| a8ceb0650975 | 1165–1168 | formalized | JacobsonRankTwo.finiteSubgroupAdmitsNoProperCompression | ok |
| 3009704fef89 | 1169–1171 | formalized | EJZCitationSentences.jacobsonThreeCoordinatesCarryPropertyT, PrintedThreePlusOneGeneral | ok |
| c149d33e8f7e | 1171–1173 | formalized | PrintedTwoResultsComplementaryPresented | ok |

## Checks run

- Root reachability: all 97 carrier declarations resolve to modules in the import closure of `GroupApproximation.lean` at origin/main.
- Closed audits observed:
  - TorsionComplementaryIdempotents (both endpoints);
  - FullDefectRingEJZUnconditional (every AllCharacteristics form);
  - JacobsonPresentedSentences (4 endpoints);
  - GHWTheoremFourClosed;
  - IntegralColumnPlaneClosure (EJZ).
- Literature inputs in the range: [EJZ, Theorem 1.1] three times, carried by
  `IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT`, which is closed; [GHW, Theorem 4],
  carried by `GHW.printedGHWTheoremFour`, which is closed at every field. No binder stands for a cited result.
- Baseline: `metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt` names no declaration of this range.

## Landed

- c20ed3ab9: this ledger.
- f797a21d6: `GroupApproximation/Manuscript/OneSidedMFRadical/JacobsonPresentedRadicalSLUnion.lean`, probe
  0913-170344-66064 GREEN. Declarations: `JacobsonPresented.presRadicalEquivSLUnion`,
  `JacobsonPresented.PrintedToeplitzJacobsonRadicalSLUnion`,
  `JacobsonPresented.manuscriptSentence_toeplitzJacobsonRadicalSLUnion` (closed audit). Queued in `wire-queue.txt`.
- Census row: `metadata/nm-census-rows/ms-inverses-4.tsv` (row 754a868fc8f5).

## Claims

- CLOSED: tex 1156 display for the presented J (f797a21d6).
- CLAIM (main's 17:2x item, helping ct-bilateral-cell): prop:bilateral-three, tex 1585–1587, "So ⟨z⟩ is a nontrivial
  finite central subgroup of B, of order char(k)" — GroupApproximation/Algebra/BilateralThreeCellZOrder.lean (new
  module). It proves z^m = 1 ↔ m•d = 0 for every cell, and for the R_X cell with x ∈ P∖T(P) over a finite field
  z^m = 1 ↔ char k ∣ m, orderOf z = char k, z ≠ 1, and ⟨z⟩ finite and central in `Cell.B S`. It imports only the
  landed BilateralThreeCellMatrices and BilateralThreeCellClopen. Names are in namespace `BilateralThreeCell.ZOrder`
  and `ClopenCrossedProduct.bilateralCell_*_z`, so nothing collides with ct-bilateral-cell's Corner draft
  (`one_add_pow_of_mul_self_eq_zero`, `z_pow_eq_one_of_natCast_mul_d`, `isOfFinOrder_z`). Proposed to
  ct-bilateral-cell at 17:3x.
- CLOSED 17:5x: tex 1585–1587 LANDED 1982b6aa4 (probe 0913-174741-34426 GREEN, closed audit; the first probe
  0913-174305-20653 failed on elaborating `add_left_cancel` inside `congrFun`, fixed by naming the step).
  Declarations: `ClopenCrossedProduct.PrintedBilateralThreeZCentralOfOrderChar`,
  `ClopenCrossedProduct.manuscriptSentence_bilateralThreeZCentralOfOrderChar` (closed audit),
  `ClopenCrossedProduct.bilateralCell_orderOf_z`, `ClopenCrossedProduct.bilateralCell_z_ne_one`,
  `ClopenCrossedProduct.bilateralCell_z_pow_eq_one_iff`, `ClopenCrossedProduct.nsmul_defectD_eq_zero_iff`,
  `BilateralThreeCell.ZOrder.z_pow_val`, `BilateralThreeCell.ZOrder.z_pow_eq_one_iff`. Census row `e94a87793eb1`
  (ct-sentences had graded it partial); module queued in wire-queue.txt.
