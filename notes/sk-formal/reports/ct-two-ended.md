# Lane ct-two-ended: thm:general and thm:main of `simple_kazhdan_sofic_group.tex` — CLOSED

Target: the note at origin/main. Its last commit is 8b36733d7 (09-14 09:17, abstract only), which is still the last commit at origin 4e0c613ce.
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
`IsMatricialVia` requires N_k ≥ 1; subshift models have N_ℓ = least period ≥ 1. The wording at 8b36733d7 keeps the gap; main's ruling is to leave it as reported.

## SK census rows: the thm:general block, l.110–198 (census 9cb80166d at tip 8b36733d7)

These are the rows in `metadata/sk-census-rows/ct-two-ended.tsv`:

| key | lines | status | carriers |
|---|---|---|---|
| a9d39de3a9f7 | 110–112 | definition | binders of `PrintedSimpleKazhdanGeneral`, `ClopenGroupCrossedProduct` |
| 770348ecbf71 | 112–116 | definition | `IsMatricialVia`, which adds N_k ≥ 1 (see the note above) |
| b4a4e3abdeda | 116–118 | formalized | `printedSimpleKazhdanGeneral` (first four conjuncts) |
| ce4df433abd6 | 123–126 | partial | the periodic clause is carried by `printedPeriodicMatricialStatement`, `printedSimpleKazhdanSoficMain_of_general` and `printedSimpleKazhdanSoficMain`. Residual: the cor:host clause, `PrintedCountableLEFHost`, which `printedCountableLEFHost_of_lamplighter` reduces to the one open piece `LEFLamplighterStatement` |
| 386f01325a6d | 130 | structural | every sec:proof endpoint quantifies n ≥ 3 |

Simplicity step rows 18ac299bc474, e503326bf5e2, 5b3ad392ecb5 and 2b5ba855ed5c: `skf-consequences.tsv` landed 09:25, after the 09:21 census, and grades all four formalized with step declarations. I checked each printed step against the source on origin and added no duplicate rows. The merge accepts a second lane's row only at the same status, and that row replaces the first lane's decls.
- 18ac299bc474 (l.179–182):
  - "As h ≠ I₃, V is nonempty": the `V.Nonempty` output of `exists_isSmall_not_commute_elGen` (GeneralRoot), passed through `generalCommutatorWitness`.
  - "the ε_ab span a ring A_V ≅ M_{|B_w|}(F₂)": `epsilonHom` (E_ab ↦ ε_ab, `epsilonHom_single`), `epsilonHom_injective` for V ≠ ∅, and `mem_range_epsilonHom_of_mem_epsilonSpan`.
  - "1_V = Σ ε_aa": the local identity ψ(1).
  - "y ↦ (1−1_V)I₃ + y embeds GL₃(A_V) ≅ GL_d(F₂)": `ChainRadical.cornerMatrixHom` (`scalar (1 − φ 1) + M.map φ`), `copyGL = cornerUnitHom ψ ∘ blockFlatEquiv`, and `copyGL_injective`.
- e503326bf5e2 (l.187), "x = [g,h] ∈ K∖{1}": `hkK` and `hk1` inside `generalCommutatorWitness`, with x = ⁅g, e_ij(e_V)⁆.
- 5b3ad392ecb5 (l.193–196):
  - `hM`: the entries of g e_V E_ij g⁻¹, via `mul_charFn_mul_mem`.
  - `hE`: ε_ee E_ij, via `charFn_mem_epsilonSpan`.
  - `hk` and `hk'`: x − I and x⁻¹ − I. Lean uses h⁻¹ = I − ε_ee E_ij rather than the char-2 identity h⁻¹ = h.
  - Closure under products: `epsilonSpan_mul_mem`.
- 2b5ba855ed5c (l.196–198):
  - `ChainRadical.exists_cornerUnitHom_eq` takes X and Y with φX = x − I and φY = x⁻¹ − I. The images of 1+X and 1+Y are y and y′, the unit ⟨1+X, 1+Y⟩ gives yy′ = y′y = 1_V I₃, and this is checked through `cornerMatrixHom_injective`.
  - `exists_copyGL_eq` gives x ∈ H_V.

## Tracker: unassigned rows at census 9cb80166d and the origin row files (origin 4e0c613ce, 10:13)

The census marks 78 rows unassigned:
- 5 are my block rows above, landed with this report;
- 44 are covered by unmerged lane rows (oa-kirchberg, oa-llp, sk-stepanov, skf-consequences, ms-core-3, ms-traces-1, sk-lef-ultra, sk-lef-action, ms-intro-2, ms-traces-3);
- 29 are covered by no row file.

Among the covered rows, 4d2e3277d31f (l.240–242) is ms-core-3's row; its carriers are this lane's `perfectSpace_carrier` and `isTopologicallyFree_shift`. d00f0309aff7 has formalized rows from both ms-traces-1 and sk-lef-ultra; at equal status the merge gives no conflict.

Uncovered, by block:
- ms-traces-1 (l.288–338), 2 rows: 022271399cfb (298–302, cor:lef), 9b1a6e7489a1 (310–313, cor:host).
- ms-traces-3 (l.474–529), 7 rows: 25f820cbd165 (512–513), 1c40d21401f6 (513–516), dc73886fdc13 (516–519), 85fe62a789f3 (519–520), 60be9d39afa5 (522–523), 7d13cf4208bc (525–526), 7f61e23f0bee (529).
- oa-kirchberg (l.30–107): none.
- No assigned block, the cor:host proof in sec:lef (l.389–455), 20 rows:
  - 814c69fe374e (389–392), 69f426d03d8f (398–402), 5bd4618a3044 (409–410), 4f76927e5215 (412–413), 759568036721 (413–415);
  - f4530e72badf (415–417), 6ca89f8e4ff1 (417–420), c9ff6825e69d (420–423), 6b767019eab2 (423–428), 9f44cd00cd04 (428–430);
  - 6d24375846b3 (430–433), f0f7ef8941cf (433–435), 902f025b4bf7 (435–438), bb65ababe757 (438), 86b1b005fc2a (440–443);
  - e18417562d36 (443–444), 581584337a04 (444–447), 7bfa078c0bed (447–451), e3cd35e16e2f (451–454), 14148c1b4df0 (455).

  The rows around them, l.356–389 and l.397–403, are sk-lef-action and ms-intro-2 rows.
