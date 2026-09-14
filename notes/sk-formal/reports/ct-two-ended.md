# Lane ct-two-ended: thm:general and thm:main of `simple_kazhdan_sofic_group.tex`

Target: origin/main tip 37551fd93 (restructured at c8b6021ca).
- `thm:general` (tex 109–127): a finitely generated Λ acting minimally and topologically freely on a Cantor set Z, with
  R = LC(Z,F₂) ⋊ Λ matricial via φ_k. Then EL_n(R) is infinite, finitely generated, simple and Kazhdan, and a marked limit
  of SL_{nN_k}(F₂) with expander Cayley graphs.
- `thm:main` (tex 55–69) follows through periodic approximations (tex 238–271).

This lane owns both statements and their assemblies. Everything is additive. Per main's ruling, the crossed product is
sk-lef-action's `ClopenGroupCrossedProduct Λ Z k`; freeness is stated as printed, definitionally sk-lef-action's
`IsTopologicallyFreeAction`.

This file is written by ct-two-ended only.

## Landed (probe-built, #audit clean, wire queued)

Namespace `GroupApproximation.SimpleKazhdanSofic`, modules under `Manuscript/SimpleKazhdanSofic/`.

| module (SHA) | declarations |
|---|---|
| `MainAssembly` (bf15b32cf, 52da29fb3) | `IsMarkedLimit`, `IsExpanderFamily`, `PrintedMarkedLimitExpanders S n`, `PrintedSimpleKazhdanSoficMain` (every n ≥ 3), `infinite_elementaryGroup`, `printedSimpleKazhdanSoficMain_of_pieces` |
| `MarkedLimitLEF` (52da29fb3) | `isLEF_of_isMarkedLimit`, closed `printedMarkedLimitLEFStatement` |
| `MainAssemblyPieces` (52da29fb3) | closed `printedSubshiftRingFGStatement` |
| `MarkedLimitTransport` (14ee44a37) | `IsMarkedLimit.map_source`/`map_target`, `IsExpanderFamily.map_target`, `elementaryBlockEquivUnits`, `elementaryBlockEquivSL`, `isSimpleGroup_elementaryBlock`, `elementaryGroupEquivOfRingEquiv` |
| `GeneralTheorem` (40cf3ae5b) | `IsMatricialVia` (N_k ≥ 1), `MarkingIndex`, `elementaryMarking`, `matricialMarking`, `PrintedSimpleKazhdanGeneral`, pieces, closed `printedMatricialExpandersStatement`, `infinite_of_perfectSpace`, `tendsto_card_of_isMarkedLimit`, `printedSimpleKazhdanGeneral_of_pieces` |
| `MainFromGeneral` (8811c88c5) | `shiftMulAction`, `ringEquiv`, `isMinimal_shift`, `isTopologicallyFree_shift`, `perfectSpace_carrier`, `printedGenerators`, `PrintedPeriodicMatricialStatement`, `printedSimpleKazhdanSoficMain_of_general`, closed `printedBlockElementarySimple`, `printedSimpleKazhdanGeneral_of_open_pieces`, `printedSimpleKazhdanSoficMain_of_open_pieces` |

## In probe

- `GeneralTheoremClosure`: closed `printedGeneralSimplicityStatement` (skf-consequences' `General.isSimpleGroup_clopenGroupCrossedProduct_of_isOpen`, 81ae4081d); `printedSimpleKazhdanGeneral_of_marked_limit`; `printedSimpleKazhdanSoficMain_of_matricial_pieces`.

## Residual (ms-core-3, drafted in `MatricialEndpoints`)

- `PrintedMatricialMarkedLimitStatement : ∀ (R : Type) [Ring R] (S : Finset R), 1 ∈ S → Subring.closure ↑S = ⊤ → ∀ N φ, IsMatricialVia S N φ → ∀ n, 3 ≤ n → IsSimpleGroup ↥(elementaryGroup (Fin n) R) → IsMarkedLimit (elementaryMarking n S) (matricialMarking n S N φ)` (tex 211–233)
- `PrintedPeriodicMatricialStatement : ∀ A … (S : Subshift A ℤ), Infinite S.carrier → IsMinimal S → ∃ N φ, IsMatricialVia (printedGenerators S) N φ` (tex 244–271)

When both land, `printedSimpleKazhdanGeneral` and `printedSimpleKazhdanSoficMain` are one-line applications.

## Printed-claim note

thm:general literally allows N_k = 0. The zero ring satisfies every matricial axiom, so interleaving size-zero models
breaks the marked convergence. ms-core-3 found this and reported it to main. `IsMatricialVia` requires N_k ≥ 1.
