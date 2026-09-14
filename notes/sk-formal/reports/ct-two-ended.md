# Lane ct-two-ended: thm:main assembly of `simple_kazhdan_sofic_group.tex`

Target: origin/main tip e80dcf20a (386 lines, md5 4ad4921253626a4f858866c716a13385), Theorem `thm:main` (tex 48–62),
assembled from the range lanes' carriers. Settled with ms-intro-3 (~20:05) and confirmed by main (~20:30): the statement
`PrintedSimpleKazhdanSoficMain` and its closed theorem are this lane's, in `Manuscript/SimpleKazhdanSofic/MainAssembly.lean`.
ms-intro-3 keeps `Setting`, `MinimalDenseOrbits` and the census rows of the abstract, introduction and thm:main, which cite
these declarations. This lane keys no census rows of its own.

This file is written by ct-two-ended only.

## Landed

- `GroupApproximation.Manuscript.SimpleKazhdanSofic.MainAssembly` (bf15b32cf; probe 0913-195931-2051 GREEN; wire queued).
  Namespace `GroupApproximation.SimpleKazhdanSofic`:
  - `IsMarkedLimit s σ`: convergence in the space of marked groups (every word is eventually trivial in `H ℓ` iff trivial in `G`);
  - `IsExpanderFamily σ`: finite generating family, orders → ∞, uniform edge expansion `ε|S| ≤ #{(x,i) : x ∈ S, σ_i x ∉ S}`
    for `2|S| ≤ |H ℓ|`;
  - `PrintedMarkedLimitExpanders S n`: a marked limit of simple `SL (Fin n × Fin N_ℓ) F₂` with expanding Cayley graphs;
  - `PrintedSimpleKazhdanSoficMain` (tex 48–62, every n ≥ 3): infinite, `Group.FG`, `IsSimpleGroup`, `HasKazhdanPropertyT`,
    `PrintedMarkedLimitExpanders`, `IsLEF`, `IsSofic`, `IsHyperlinear` of `↥(elementaryGroup (Fin n) (R S))`;
  - `printedSimpleKazhdanSoficMain_of_pieces` over the four pieces below.

## In flight

- `MainAssembly` revision: the infinite clause along the printed route ("infinite because e₁₂(LC(X,F₂)) is infinite", tex
  113–114), through ms-compress-4's `infinite_locallyConstant_zmodTwo` and `ClopenCrossedProduct.coeff_injective`.
- `GroupApproximation.Manuscript.SimpleKazhdanSofic.MarkedLimitLEF` (tex 162–163, "…and G is LEF"):
  `isTextbookLEF_of_isMarkedLimit`, `isLEF_of_isMarkedLimit`, closed `printedMarkedLimitLEFStatement`. ms-core-3's row
  `60605fdb5e61` can cite it.

## Pieces and owners

| piece | tex | owner | producer status |
|---|---|---|---|
| `PrintedSubshiftRingFGStatement` | 97–99 | ct-involution | `printedRingGeneration` (RingGeneration, unlanded) plus finiteness of `ringGenerators S` |
| `PrintedSimplicityStatement` (every n ≥ 3) | 179–237 | skf-consequences, ct-bilateral-mf | `printedSimplicityThroughFiniteSimpleSubgroup` (unlanded) is Fin 3 only |
| `PrintedMarkedLimitExpandersStatement` | 147–164 | ms-core-3 (marked convergence, L1 at Fin n); oa-expanders (Kassabov) | L1 `printedBlockElementarySpecialLinear`, L2 `printedFreeAlgebraElementaryKazhdan` in flight at Fin 3 |
| `PrintedMarkedLimitLEFStatement` | 162–163 | ct-two-ended | `printedMarkedLimitLEFStatement`, in probe |

## Clauses proved in the assembly

| clause | carrier | route |
|---|---|---|
| (T), tex 110–113 | `Pestov91.elementary_hasKazhdanPropertyT` (EJZ, proved) over `PrintedSubshiftRingFGStatement` | printed |
| finitely generated | `KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT` | the note reads it off the generators (tex 109–110, ms-compress-4); both are proved |
| infinite, tex 113–114 | `infinite_elementaryGroup` over `infinite_locallyConstant_zmodTwo` | printed (revision in flight) |
| LEF ⇒ sofic ⇒ hyperlinear, tex 164–166 | `isSofic_of_isLEF`, `Pestov91.isHyperlinear_of_isLEF` | printed |

## Closure

Once the three open producers land, `theorem printedSimpleKazhdanSoficMain : PrintedSimpleKazhdanSoficMain` follows in one
line from `printedSimpleKazhdanSoficMain_of_pieces`. skf-degrees consumes it for the word-problem corollary.
