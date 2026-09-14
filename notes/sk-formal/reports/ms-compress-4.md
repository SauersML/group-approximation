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

## Progress log
- 19:1x ledger v1 and claim.
