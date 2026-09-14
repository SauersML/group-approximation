# Lane ct-involution (sk): ring sentences; Questions (conjugacy isomorphism, not finitely presented)

Lead: main (ROSTER-sk, PROTOCOL 19:45; RESUME 23:15). Target: the current origin/main tip of
`simple_kazhdan_sofic_group.tex`, read with `git show origin/main:simple_kazhdan_sofic_group.tex`. Census rows are keyed by the
12-hex sentence hash of `metadata/SK_SENTENCE_CENSUS.tsv`, in `metadata/sk-census-rows/ct-involution.tsv`.

## Item 1 (e80dcf20a): "The ring and property (T)", ring sentences — STALE after c8b6021ca

The note was restructured at c8b6021ca ("one general theorem"). At the tip, "The ring and property (T)" is stated for a group Λ
acting on Z (`R = ⊕_{ξ∈Λ} LC(Z,F₂) u_ξ`). The five keys this lane graded at e80dcf20a (c6bd4bf41f69, d31438fef85b, 9a58ee4cb6c1,
6fdf439f1009, 16a4a7086323) are absent from the census regenerated at 37551fd93, so those rows are stale. The carriers stay valid
for the subshift case (Λ = ℤ):

| module | content | status |
|---|---|---|
| `Manuscript/SimpleKazhdanSofic/RingPartitions.lean` | `IsMinimalSystem`, `eU`, `unit_mul_eU_mul_inv`, no periodic points, clopen partitions | LANDED 2f481625d |
| `Manuscript/SimpleKazhdanSofic/RingSimpleCentre.lean` | `isSimpleRing`, `mem_center_iff`, `mem_center_iff_eq_zero_or_one` | LANDED 6aa8851c6 |
| `Manuscript/SimpleKazhdanSofic/RingLaurent.lean` | uniqueness of the Laurent form, product formula | LANDED 374408a7c |
| `Manuscript/SimpleKazhdanSofic/RingGeneration.lean` | `printedRingGeneration`, `printedSubshiftRingFinitelyGenerated` | LANDED 22b15ce5e |

`printedSubshiftRingFinitelyGenerated` has the body of MainAssembly's `PrintedSubshiftRingFGStatement` (both are
`∀ A … S, IsFinitelyGeneratedRing (R S)`); that piece is already produced on origin by `MainAssemblyPieces.printedSubshiftRingFGStatement`.

## Item 2: Questions (tip 696c4b602, md5 0648e5f876e467e21ebf475e08b8ee92; text verified at the tip)

| key | tip l. | sentence | carrier | status |
|---|---|---|---|---|
| 3606856b9a07 | 569–570 | "If (X,T) is topologically conjugate to (Y,S) or to (Y,S⁻¹), then G_X ≅ G_Y." | `SimpleKazhdanSofic.printedConjugacyIsomorphism` (closed), `conjRingEquiv`, `flipRingEquiv`, `nonempty_elementaryGroup_equiv_of_conj_or_flip` (every rank) — CrossedProductConjugacy, LANDED 730da5240 | formalized (row landed b3b8de919) |
| 44b4aa4489ab | 556–558 | "A finitely presented LEF group is residually finite [Stepin, VershikGordon], and the infinite simple group G_X is not, so G_X is not finitely presented." | `printedFinitelyPresentedLEFResiduallyFinite`, `printedNotFinitelyPresentedOfLEFSimpleInfinite` (closed); `printedGXNotFinitelyPresented_of_main` over `PrintedSimpleKazhdanSoficMain` — QuestionsNotFinitelyPresented (absorbed from ms-compress-4) | partial after landing |

Route (conjugacy): a conjugacy φ gives `R_T ≃+* R_S` through chain-core `comap` along φ⁻¹ and φ (C(f) ↦ C(f ∘ φ⁻¹), u ↦ u); if
S' = S⁻¹ pointwise, `liftNCRingHom` gives `R_S ≃+* R_{S'}` (C(f) ↦ C(f), u ↦ u⁻¹); ring maps out of R_T are fixed by their values on
C(f) and u^j (`ringHom_ext_coeff_unit`); `elementaryCoefficientEquiv` gives the group isomorphism.

Absorption: main did not resume ms-compress-4 and moved `QuestionsNotFinitelyPresented.lean` to this lane. Origin holds its
first version (16d890864). The absorbed version (ms-compress-4 attic 094e0827c, PROBE GREEN 0913-213659-55652) adds
`printedGXNotFinitelyPresented_of_main`; this lane refreshed its docstring references to the tip and is re-probing it.

Residual of 44b4aa4489ab: `PrintedSimpleKazhdanSoficMain` (owner ct-two-ended), i.e. MainAssembly's four pieces
`PrintedSubshiftRingFGStatement` (produced, MainAssemblyPieces), `PrintedSimplicityStatement`,
`PrintedMarkedLimitExpandersStatement`, `PrintedMarkedLimitLEFStatement`.

Duplicate census row: skf-cite.tsv still holds a placeholder `partial` row for 3606856b9a07 ("owner ct-involution"); skf-cite was not
reachable after the restart.

## Released

`TowerUnits.lean` (attic 3ff509880), `TowerAbsorb.lean` (attic 4a46b7660), offered to ct-bilateral-mf.

## Progress log

- 09-13 19:42–20:30: ring modules and five ring rows landed (e80dcf20a).
- 09-13 20:37: claim for the conjugacy sentence (moved from ms-compress-4).
- 09-13 21:45: CrossedProductConjugacy PROBE GREEN; session limit and coordinator restart before landing.
- 09-13 23:15 resume: note restructured (c8b6021ca, 37551fd93, 696c4b602). CrossedProductConjugacy LANDED 730da5240; row 3606856b9a07
  landed; QuestionsNotFinitelyPresented absorbed; its re-probe is blocked by three MSI infra failures (hop died, git fetch, connection down).
