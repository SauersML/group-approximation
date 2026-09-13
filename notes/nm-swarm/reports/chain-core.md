# Lane chain-core: sec:chain-core (tex 1336–1590) and Introduction 249–258

Snapshot: origin/main 3c64a92ef (09-13).  Census: 0 rows for this section; WORKLIST lists 121
section keys plus 5 Introduction keys (`684721560ced`, `d1c3c7f0f3a9`, `aac4a95b387b`,
`c6f8fb6abe29`, `350e53c0b888`), all `unassigned`.  Claims metadata: lem:chain-core-models,
lem:transient-matrices, thm:core-ring-reflection, thm:core-mf-radical, all `paper-proof`, `lean: []`.

## Existing carriers (origin/main, grepped for uses)

| manuscript object | carrier | module |
|---|---|---|
| algebraic crossed product, `C`, `u`, Laurent form | `Pestov91.CrossedProduct.{C, unit, unitOf, unitHom, val_unit_zpow, exists_sum_C_mul_unit_zpow}` over `SkewMonoidAlgebra A (Multiplicative ℤ)` | Pestov91/CrossedProduct |
| LEF ring (full-map form) | `Pestov91.IsLEFRing`, `isLEFRing_of_finite`, `IsLEFRing.matrix` | Pestov91/LEF |
| units of an LEF ring are LEF | `Pestov91.IsLEFRing.isLEF_units`; EL: `isLEF_elementaryGroup` | Pestov91/LEF |
| cycle-type periodic models ⇒ LEF crossed product | `Pestov91.isLEFRing_skewMonoidAlgebra_of_periodic` (`shiftMatrix`, `periodicModel`) | Pestov91/LEFCrossedProduct |
| action of a shift on `LocallyConstant X K` (pattern only; Toeplitz shift) | `Pestov91.witnessAction` | Pestov91/WitnessRing |
| LEF group | `Sofic.IsLEF`, `isLEF_of_injective`, `isLEF_of_forall_fg` | Sofic/LEF |
| countable LEF ⇒ MF | `isOperatorMF_of_isLEF` | Sofic/LocallyFiniteMF |
| MF radical | `MFQuotientUnits.mfHomKernel`, `mem_mfHomKernel_iff`, `mfHomKernel_normal` | Manuscript/OneSidedMFRadical/MFHomKernel |
| `EL_n(R, I)` | `relativeElementary` | Leavitt/CongruenceSubgroups |
| `EL_n(f)`, surjective for surjective `f` | `elementaryGroupMap`, `elementaryGroupMap_surjective_of_surjective` | Leavitt/ElementaryGroup |
| prop:torsion-defect-ring clause 1 (closed, audited) | `Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents.manuscriptTorsionComplementaryIdempotents` | Manuscript/OneSidedMFRadical/TorsionComplementaryIdempotents |
| directly / stably finite | Mathlib `IsDedekindFiniteMonoid`, `IsStablyFiniteRing` | Mathlib pin 81a5d257 |
| `f ∘ T⁻¹` on locally constant functions | Mathlib `LocallyConstant.congrLeftRingEquiv`, `comapRingHom` | Mathlib pin |

Nothing on origin or in any `lanes/*.files` on chain recurrence, word graphs, itinerary subshifts,
locally matricial algebras, the clopen defect pair, or LEF ⇒ stably finite.  Mathlib at the pin
has symbolic dynamics basics (`Subshift`, cylinders) and nothing on chain recurrence.

## Sub-items (≤ 6, lane-sized)

### S1 `basics` — TAKEN by chain-core
Setup and the elementary ring facts consumed by every later item.
Keys: `275bedb28f9f` `752564275a33` `a1bda19b475a` `8a557cb954fb` `6011dc411b20` `2d1ca8689ac6`
`b1a4887c5412` `1d0bcc92a75f` `1a88ddc187c0` `549aa93e832f` `bba38420cf8b` `6e533530564d`
`aa429ec8d623`.
Missing leaves:
1. coefficient synonym for `LC(X,k)` carrying the `ℤ`-action `j • f = f ∘ T^{-j}` of a homeomorphism
   `T`, and `R_X` as `SkewMonoidAlgebra` over it; `u C(f) u⁻¹ = C(f ∘ T⁻¹)`.
2. the printed LEF definition (partial tables, `0`/`1` when present) and its equivalence with
   `IsLEFRing`.
3. LEF rings are directly finite and stably finite (`IsStablyFiniteRing`), via `IsLEFRing.matrix`.
4. `GL_n` of an LEF ring is LEF (compose 3 with `isLEF_units`); countable ⇒ MF by
   `isOperatorMF_of_isLEF`.
5. eq:clopen-defect-pair: for clopen `P` with `T(P) ⊆ P`, `s = up + 1 − p`, `t = pu⁻¹ + 1 − p`,
   `ts = 1`, `st = 1 − d`, `d = 1_{P∖T(P)}`; a generic ring lemma (unit `u`, idempotents `q ≤ p`,
   `u p u⁻¹ = q`) plus the crossed-product instance.
6. a unital hom to a directly finite ring kills `d`; `2 • d = 0` over `F_2`.
7. `R_X` is countable (countable clopen basis).

### S2 `recurrence` — open
Chain recurrence and compressed clopen sets on a general space.
Keys: `49f76a64907a` `d5af28721656` `3ebdab1c418b` `0ae6fc9e199c` `73bd8ac910aa` `3ef2a7cdb9bd`
`c99bf0bdb029`, and part of `d8e1a694d87c` (closed, invariant).
Missing: `CR(T)` for a compatible metric, independent of the metric on compact `X`; closed and
invariant; `P∖T(P)` wandering for `T(P) ⊆ P`; chain recurrence passes to factors.

### S3 `symbolic` — open (critical path; needs S1.1)
Subshift case of lem:chain-core-models.
Keys: `53fd5ea7d3d0` `9bc3873fb872` `078684fc2a60` `dfc6d4510272` `8bf7f40918d5` `56b6a80cc911`
`2ed7f807a3a6` `57cd1b63930c` `0941296cf395` `4aede6d48b4d` `b94a006ee638` `533771f4f22d`
`9ea50b0ff631` `cbf45b0e1c51` `1d52a79f1fef` `f7c8d8aab016` `b39310f67614` `ded9e9646e4b`
`758517bf8d56` `647f44a95b8a` `ffa61d258258` `048953d87f92` `ae9c3d8b9922` `4fc54b29a740`
`a08f25fce44c` `d8f8d764406c` `9c49a2efb0ca` `854ec7cb0423`.
Missing: word graphs, cyclic edges, cycle condition; cycle condition ⇒ periodic models feeding
`isLEFRing_skewMonoidAlgebra_of_periodic`; retained-graph subshifts `Z_r`, `Y_0 = ⋂ Z_r`, language
stabilization; `Y_0 = CR(T)`; noncyclic edge ⇒ forward-closed cylinder union `P`, `Tx ∈ P∖T(P)`.

### S4 `general-X` — open (critical path; needs S2, S3)
Keys: `3d8a2204752a` `fe2bd83087c0` `4bb19e581840` `ed348643e2ad` `807793f12a5e` `b180421b55ab`
`2df08eeac3cb` `c825bc73828a` `e6626f95fede` `2583cbd0c0f2` `3b218f92cd81` `fb195144e5c2`
`8921296d639a` `042966c81c7e`, and the rest of `d8e1a694d87c` (nonempty; `R_Y` LEF).
Missing: refining clopen partitions and itinerary subshifts `π_m`, one-block factors `ρ_lm`,
`Y_* = ⋂ π_m⁻¹(Y_m)`; coefficient pullback injective unital; increasing union of LEF rings is LEF;
`Y_* = Y`; pullback of symbolic defects covers `X∖Y`.

### S5 `transient-matrices` — open (needs S4)
Keys: `eda117e756e6` `7ff20576d4cf` `f0c16e5c8519` `910136e6e66d` `c05b0ec8b821` `97e43ae93d14`
`2546c17d9884` `e60c16639f70` `f5264e48f943` `4244fb3c658b` `34e1eeff13be` `cd20a742dd3c`
`1687471008a1` `ff376e50f433` `a3598c08b42c` `741b64286b55` `1d0f9a56866c` `fd026a61f84f`
`46f3810145ee` `5079b22a3633` `d01cbef361ce` `2a63696d979b` `e55132ef58f5`.
Missing: locally matricial (definition); LC extension from closed subsets; restriction kernel =
compactly supported in `X∖Y`; exactness of `0 → I → R_X → R_Y → 0`; `I` generated by the defect
indicators; compact clopen partial shift graphs, class size ≤ `m`, loop erasing, freeness on `U`,
clopen representative set, levels ⇒ `M_h(k)`; local matriciality.

### S6 `theorems` — open (needs S1, S4, S5)
thm:core-ring-reflection keys: `42c043ef7ab5` `8981cd70915a` `43afa4ee3f10` `cfbacaa0fffa`
`9dae685e37b9` `400dde0dbd9d` `5a62e295ac1a` `d74779471003` `715cbd0f3410` `30a44485e5e8`
`f2baa4a46f78` `b23e0f5197b5`.
thm:core-mf-radical keys: `71da342a2cec` `ffcebac26044` `1dcedf0a7a5c` `87cd8b50757e` `380bfb5990c5`
`5ab74e7c4576` `3a5ab131efde` `3b9dae111508` `be106727feb1` `4c62dd1963db` `fd54e2645afe`
`2416b0e3e06b` `8ffeafc81808` `c13ca7c28028` `a47d16c7fbe5` `0b84b12a0927` `aef6776a7348`
`5bdc96184b03` `d6d4c3f1cdb5` `d2d559dae75f` `8ada929ece30`.
Introduction keys: `684721560ced` `d1c3c7f0f3a9` `aac4a95b387b` `c6f8fb6abe29` `350e53c0b888`.
Missing: corner `eAe` directly finite; amplification to `M_m`; `R_X` DF ⇔ SF ⇔ LEF ⇔ `X = Y`;
`GL_n(∏ M_{h_a}(F_2)) = EL_n` (determinant one over `F_2`, block flattening, commutators);
kernel of `GL_n(R_X) → GL_n(R_Y)` equals `EL_n(R_X, I)` and is locally finite; the radical equality
consuming `manuscriptTorsionComplementaryIdempotents` clause 1 and `isOperatorMF_of_isLEF`.
The torsion-defect consumer is available now; the kernel computation is blocked on S5.

## Critical path
S1 → S3 → S4 (with S2) → S5 → S6.  Only S1 and S2 have no upstream dependency in this section.

## Progress log
- 09-13: scope landed (this file).  S1 in progress.
