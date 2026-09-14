# Lane ms-compress-4: `simple_kazhdan_sofic_group.tex` 86–101 and 114–117 at bf961c128

Lead: session nonsofic-existence-49 (ROSTER-sk, re-scoped 18:58). Target text: origin/main bf961c128, 340 lines,
md5 7b3dc4ec92b4581553bc0dc2b0edcb99 (re-checked 19:10). Rows are keyed `LINE:<l>@bf961c128`.

CLAIM generic EL_3 facts of tex 86–101, 114–117 (identities, generation, (T), infinite, trivial centre) GroupApproximation/Manuscript/SimpleKazhdanSofic/ElementaryGroupFacts.lean

## Neighbours (ROSTER-sk table)
- ct-involution: tex 67–86 and 102–113. That covers `R`, the generation of `R` by `u, u⁻¹, e_a` (84–86), and `R` simple with
  `Z(R) = F₂` (102–113). My sentences 94–95, 99 and 116 consume those facts.
- ms-intro-3: thm:main assembly `Manuscript/SimpleKazhdanSofic/MainTheorem.lean`, which consumes pieces as named Props.
  The ring is `ClopenCrossedProduct (shiftHomeomorph hX) (ZMod 2)` (`u f u⁻¹ = f ∘ T⁻¹`, the printed convention).

## Plan
The statements are generic over any unital ring, which is at least the printed generality, and follow the printed routes.
The instances at `R_X` then consume ct-involution's named ring facts until they close.

## Ledger v1

| l. | sentence (abridged) | grade (target) | carrier | verdict |
|---|---|---|---|---|
| 86–87 | Put `G = EL_3(R)` and `e_ij(r) = I_3 + r E_ij`, `E_ij` the usual matrix unit. | definition | `elementaryGroup (Fin 3) R`, `elementaryUnit i j h r` (val `1 + Matrix.single i j r`), Leavitt/ElementaryGroup | OK |
| 88–93 | eq:elementary: `e_ij(r+s) = e_ij(r) e_ij(s)` (i ≠ j); `[e_ik(r), e_kj(s)] = e_ij(rs)` (i, j, k distinct). | formalized | `elementaryUnit_mul`, `elementaryUnit_commutator`; wrapper with the printed index names in this lane's module | OK, printed-form wrapper to land |
| 87, 94–95 | The identities show that the `e_ij(s)`, `s ∈ {1, u, u⁻¹} ∪ {e_a}`, generate `G`. | formalized (generic) + instance | GAP: generic "a ring generating set `Σ` gives `EL_3(R) = ⟨e_ij(s) : s ∈ Σ ∪ {1}⟩`", by the coefficient-subring route; instance consumes ct-involution 84–86 | build |
| 96 | Here `[g,h] = g h g⁻¹ h⁻¹`. | definition | Mathlib `commutatorElement_def` | OK |
| 97–99 | EJZ: `EL_n(R)` has (T) for every f.g. unital associative ring `R` and `n ≥ 3` [EJZ, Thm 1.1]. | formalized + attribution | `IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT : FinitelyGeneratedRingGeneralRankElementaryPropertyT` (proved; coefficient ring in `Type`) | check audit and root |
| 99 | Hence `G` has property (T). | formalized (generic) + instance | GAP: generic "a finite ring generating set gives `EL_3(R)` (T)", via `Pestov91.elementary_hasKazhdanPropertyT`; instance consumes ct-involution 84–86 | build |
| 100 | It is infinite because `e_12(LC(X, F₂))` is infinite. | formalized | GAP: `LC(X, F₂)` is infinite for infinite totally separated `X`; `a ↦ e_12(coeff a)` is injective, so `G` is infinite; instance at every infinite subshift `X ⊆ A^ℤ` | build |
| 114–115 | Commuting with every `e_ij(1)` forces a central element of `G` to be `c I_3`; commuting with all `e_ij(r)` gives `c ∈ Z(R)^× = {1}`. | formalized (generic) + instance | `Pestov91.exists_central_scalar_of_mem_center` (the element is central, the printed hypothesis; scalar via `Matrix.mem_range_scalar_of_commute_single` on the `e_ij(1)`, centre of `R` via the `e_ij(r)`), `exists_central_unit_scalar_of_mem_center` (unit), `center_elementaryGroup_eq_bot`, `SplitSimplicity.central_unit_eq_one_of_central_zero_or_one` (`Z(R) = F₂` gives `Z(R)^× = {1}`); `Z(R_X) = F₂` is ct-involution 110–113 | route OK on main; instance waits on 110–113 |
| 116 | Thus `Z(G) = {1}`. | formalized (generic) + instance | `Pestov91.center_elementaryGroup_eq_bot_of_central_zero_or_one`; instance consumes ct-involution 110–113 | instance |

## Interface with thm:main (ms-intro-3's in-flight `Setting` and `MainTheorem`, read 19:35, unlanded)
- `Setting`:
  - `R S = ClopenCrossedProduct (subshiftHomeo S) (ZMod 2)`;
  - `G S = ↥(elementaryGroup (Fin 3) (R S))`, for a Mathlib `Subshift A ℤ`.
- Named pieces:
  - `PrintedSubshiftRingFinitelyGenerated` (tex 84–86) and `PrintedSubshiftRingCentre` (tex 110–113), owned by ct-involution;
  - `PrintedMinimalSubshiftRingLEF` (ms-units).
- The instances of this range at `G S`:
  - tex 99, (T): `printedElementaryPropertyT`, or directly `Pestov91.elementary_hasKazhdanPropertyT`, over
    `PrintedSubshiftRingFinitelyGenerated`.
  - tex 116, `Z(G S) = 1`: `Pestov91.center_elementaryGroup_eq_bot_of_central_zero_or_one` over `PrintedSubshiftRingCentre`.
  - tex 100, `Infinite (G S)`: `printedElementaryInfinite` at `X = S.carrier` (infinite, totally separated) and
    `T = subshiftHomeo S`. Closed now.
- These rows stay `partial` until the two ct-involution pieces close. The instances then sit in ms-intro-3's assembly, which
  consumes this module's names.

## At the tip e80dcf20a (PROTOCOL 19:45: section "The ring and property (T)", rows by 12-hex hash)
- `SK_SENTENCE_CENSUS.tsv` on origin was generated at bf961c128, and the tip md5 is 4ad49212. Rows are keyed only where the
  sentence text is verified identical at the tip. The rest wait for skf-census to regenerate.
- **Module LANDED daef03299** (probe 0913-194134-17952 GREEN, BUILT): `printedElementaryIdentities`,
  `printedElementaryGeneration`, `printedElementaryPropertyT`, `printedElementaryInfinite`, all with `#audit_closed_axioms`.

| tip l. | sentence | status | carrier | hash |
|---|---|---|---|---|
| 99–102 | "Let `G = EL_3(R)` be the subgroup of `GL_3(R)` generated by the elementary matrices `e_ij(r) = I_3 + r E_ij`, `i ≠ j`, `r ∈ R` …" | definition | `elementaryGroup (Fin 3) R`, `elementaryUnit` | rewritten; waits for regeneration |
| 102–108 | "With `[g,h] = ghg⁻¹h⁻¹`," plus eq:elementary | formalized | `printedElementaryIdentities`; convention `commutatorElement_def` | display `d96b6930fe6d` survives (keyed) |
| 109–110 | "So the matrices `e_ij(s)` with `s ∈ {u, u⁻¹} ∪ {e_a}` generate `G`, as `1 = ∑_a e_a`." | partial | REWRITTEN: `1` left the generating set. Carrier `printedElementaryGenerationSumOne` (1 ∈ additive closure of `gens`), LANDED e18af7b3e (probe 0913-194547-46844 GREEN). Instance consumes ct-involution's generation of `R` | waits |
| 110–113 | "By Ershov and Jaikin-Zapirain [Thm 1.1], `EL_n(S)` has (T) for every f.g. associative unital ring `S` and `n ≥ 3`." | formalized | `IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT` | rewritten; waits |
| 113 | "So `G` has property (T)." | partial | `printedElementaryPropertyT`; instance over `PrintedSubshiftRingFinitelyGenerated` (ct-involution) | rewritten; waits |
| 113–114 | "It is infinite because `e_12(LC(X, F₂))` is infinite." | formalized | `printedElementaryInfinite` | `64da45d532f8` survives (keyed) |

- `Z(G) = 1` left this section. The tip's only centre step is in "Simplicity" (tex 191, "Taking V=X gives g=cI_3 …"), which
  the protocol assigns to ct-bilateral-mf and skf-consequences. Its carriers on main are
  `Pestov91.exists_central_scalar_of_mem_center` and `center_elementaryGroup_eq_bot_of_central_zero_or_one`.

## Progress log
- 19:1x ledger v1 and claim.
- 19:26 probe 0913-192655-523 red: the `⁅g, h⁆` bracket on units needs `open scoped commutatorElement`; an unused simp argument
  in `infinite_elementaryGroup_fin_three_of_injective`. Both fixed; re-probing.
