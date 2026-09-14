# Lane ct-two-ended: thm:general and thm:main of `simple_kazhdan_sofic_group.tex` — CLOSED

Target: the note at origin/main; last checked at tip f34e9c0b1 (09-14 09:05).
- `thm:main` (tex 57–71) is textually unchanged since 37551fd93.
- `thm:general` (tex 109–126) is only reworded since 37551fd93: the name "matricial" is dropped, and the hypotheses and conclusion are identical.

This lane owns both statements and their assemblies. Everything is additive. The crossed product is sk-lef-action's
`ClopenGroupCrossedProduct Λ Z k`, and freeness is stated as printed (definitionally sk-lef-action's `IsTopologicallyFreeAction`).

This file is written by ct-two-ended only.

## Closed endpoints (probe-built, #audit_closed_axioms: propext, Classical.choice, Quot.sound; wire queued)

| endpoint | module (SHA) |
|---|---|
| `printedSimpleKazhdanSoficMain : PrintedSimpleKazhdanSoficMain` (thm:main, every n ≥ 3) | `SimpleKazhdanSoficMainClosed` (b972efc71) |
| `printedSimpleKazhdanGeneral : PrintedSimpleKazhdanGeneral` (thm:general, every n ≥ 3) | `SimpleKazhdanGeneralClosed` (11fb4e4dd) |

## Landed carriers

Namespace `GroupApproximation.SimpleKazhdanSofic`, modules under `Manuscript/SimpleKazhdanSofic/`.

| module (SHA) | declarations |
|---|---|
| `MainAssembly` (bf15b32cf, 52da29fb3) | `IsMarkedLimit`, `IsExpanderFamily`, `PrintedMarkedLimitExpanders S n`, `PrintedSimpleKazhdanSoficMain`, `infinite_elementaryGroup` |
| `MarkedLimitLEF` (52da29fb3) | `isLEF_of_isMarkedLimit`, `printedMarkedLimitLEFStatement` |
| `MainAssemblyPieces` (52da29fb3) | `printedSubshiftRingFGStatement` |
| `MarkedLimitTransport` (14ee44a37) | `IsMarkedLimit.map_source`/`map_target`, `IsExpanderFamily.map_target`, `elementaryBlockEquivSL`, `isSimpleGroup_elementaryBlock`, `elementaryGroupEquivOfRingEquiv` |
| `GeneralTheorem` (40cf3ae5b) | `IsMatricialVia` (N_k ≥ 1), `MarkingIndex`, `elementaryMarking`, `matricialMarking`, `PrintedSimpleKazhdanGeneral`, pieces, `printedMatricialExpandersStatement`, `infinite_of_perfectSpace`, `tendsto_card_of_isMarkedLimit`, `printedSimpleKazhdanGeneral_of_pieces` |
| `MainFromGeneral` (8811c88c5) | `shiftMulAction`, `ringEquiv`, `isMinimal_shift`, `isTopologicallyFree_shift`, `perfectSpace_carrier`, `printedGenerators`, `PrintedPeriodicMatricialStatement`, `printedSimpleKazhdanSoficMain_of_general`, `printedBlockElementarySimple` |
| `GeneralTheoremClosure` (b5ffafdd4) | `printedGeneralSimplicityStatement` |

Peer carriers consumed:
- sk-lef-action: `printedGroupCrossedProductPropertyTInfinite`, `ClopenGroupCrossedProduct`;
- skf-consequences: `General.isSimpleGroup_clopenGroupCrossedProduct_of_isOpen` (81ae4081d);
- ms-core-3: `printedMatricialMarkedLimitStatement` (4d1ec38cf), `printedPeriodicMatricialStatement` (a1c4c8ca5), `printedBlockElementarySpecialLinear`;
- oa-expanders: `isExpanderFamily_matricialMarking`;
- ms-compress-4: `infinite_locallyConstant_zmodTwo`;
- ct-involution: `zpow_apply_ne_self`, `printedSubshiftRingFinitelyGenerated`;
- ms-intro-3: `Setting`, `minimalSubshift_dense_orbits`.

## Printed-claim note

thm:general literally allows N_k = 0. The zero ring satisfies every hypothesis on φ_k, so interleaving size-zero models
breaks the marked convergence, and the printed proof needs M_{N_k}(F₂) ≠ 0. ms-core-3 found this and reported it to main.
`IsMatricialVia` requires N_k ≥ 1; subshift models have N_ℓ = least period ≥ 1. The wording at f34e9c0b1 keeps the gap.
