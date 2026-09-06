# Lane `cc-lix-odd` — mapping torus (Step B), the section and its zero (Step C), Lemma 2

Owns `GroupApproximation/CharClass/MappingTorus*.lean`,
`GroupApproximation/CharClass/LIXSection*.lean`,
`GroupApproximation/CharClass/LemmaTwo*.lean`, plus the four `AlgTop` section modules
handed over by the lead: `AlgTop/{EulerLocalModel, MappingTorusSectionZeros,
CPTautologicalSection, ManuscriptSectionZeroCount}.lean` (and their dependency
`AlgTop/ComplexProjectiveBasic.lean`, repaired in place).  Namespace
`GroupApproximation.CharClass`, or `GroupApproximation.AlgTop` for the `AlgTop` files.

## 1. GREEN

| module | jobs | content |
|---|---|---|
| `CharClass/MappingTorusProjection.lean` | 8662 | `IsCornerUnitary`, `cornerExtend`, `mtSym`/`mtProj`, `mtTrans`, `IsCircleChart`, `sphereOne`/`northPole`/`southPole`, `mappingTorus` = `W_g`, `mappingTorus_isStarProjection`, `mappingTorus_continuous`, `mappingTorus_north` (`V ⊕ 0` **on the nose**), `mappingTorus_south`, `trace_mappingTorus` |
| `CharClass/MappingTorusSection.lean` | 8662 | `mappingTorus_eq`, `IsMTSectionData`, `mtSection`, `mtSection_continuous`, `mtSection_mem`, `mtSection_eq_zero_iff`, `mtSection_eq_zero_iff_of_north_ne_zero` |
| `CharClass/LIXSectionPath.lean` | 8662 | `unitVectors_seam_eq_zero_iff`, `manuscriptPath`/`southParam`, `isMTSectionData_manuscript`, `manuscriptPath_eq_zero_iff_split` |
| `CharClass/LemmaTwoZero.lean` | 8658 | `blockNorth`/`blockSouth`, `isMTSectionData_blockSplit`, `mtSection_manuscript_eq_zero_iff` |
| `AlgTop/{ManuscriptSectionZeroCount, CPTautologicalSection, ComplexProjectiveBasic}` | 8662 | repaired; `CPTautologicalSection` additionally gained `tautColSection` (§4 TRAPS) |
| `CharClass/LIXSectionManuscript.lean` | 8666 | **Step C's single zero, concrete.**  `Hmat`/`Vmat` over `S⁵ × ∏ⱼ ℂP^{dⱼ}` with `isStarProjection_Vmat`/`continuous_Vmat`, the three fields `aVec`/`bVec`/`cVec` of (2.10), `Hmat_mulVec_cVec`, `isMTSectionData_manuscriptData`, and `manuscriptSection_eq_zero_iff_concrete` |
| `CharClass/LemmaTwoParity.lean` | 8667 | `trace_Hmat`/`trace_Vmat` (`rank V = (∑ⱼ dⱼ) + 3`), `LIXParityInput`, `LIXParityInput.gamma_top_eq_zero` = **Step D** at the LIX base |
| `CharClass/LIXSectionChart.lean` | 8663 | the chart of `S⁵` at `-e₃` on the plain product `ℂ × ℂ × ℝ` (`sphereChartVec`, `sphereChartVec_mem`, `sphereChart_zero`, `continuous_sphereChartVec`), the derivative at the zero with its bijectivity (`eulerLinearModel`, `eulerLinearEquiv`, `eulerContinuousLinearEquiv`), and `trivialBlockChart_eq_zero_iff` |
| `CharClass/LemmaTwoStatement.lean` | 8667 | `FHmat`/`EHmat` with `FHmat_eq_fromBlocks`, `ContinuousMvNEquiv`, `HasStepAUnitary`, `false_of_stepC_stepD`, `not_continuousMvNEquiv` = **Lemma 2** |
| `CharClass/LIXSectionDeriv.lean` | 8664 | **the strict derivative at the zero.** `chartLinearCLM`, `sphereChartVec_eq`, `hasStrictFDerivAt_chartQ`/`_chartWeight` (the radial weight has vanishing differential), `hasStrictFDerivAt_sphereChartVec`, and `hasStrictFDerivAt_trivialBlockChart`: the derivative of the section's trivial block at its zero **is** `eulerContinuousLinearEquiv` |
| `CharClass/LIXSectionNesting.lean` | 8663 | the base as a **left-nested** chain, for `cc-thom`'s one-factor-at-a-time Künneth: `piFinSnocHomeo` (peel the *last* factor, the end Mathlib and `piFinSuccHomeo` do not), `baseSnocHomeo` (the binary step), `baseNilHomeo` (the base case) |
| `CharClass/LIXSectionLocalHomeo.lean` | 8665 | **the local homeomorphism at the zero**, in the shape `cc-thom` consumes: `eulerLocalHomeo` from `HasStrictFDerivAt.toOpenPartialHomeomorph`, with `zero_mem_eulerLocalHomeo_source`, `zero_mem_eulerLocalHomeo_target`, `eulerLocalHomeo_zero`; plus `lixTopDegree` = `2 ∑ⱼ dⱼ + 6` with `lixTopDegree_eq_two_mul_rank` |
| `CharClass/LemmaTwoUnitary.lean` | 8661 | **Step A wired.** `cornerExtend_mulVec_eq`, `exists_isCornerUnitary_of_stepA` — `cs-clutching`'s continuous corner unitary becomes the `IsCornerUnitary` field `mappingTorus` consumes, seam `g e = s` intact |
| `CharClass/LIXStepESphereModel.lean` | 8797 | **the model mismatch, discharged**: `cxToEuc`/`eucToCx` with `normSq_cxToEuc`, `unitVectorsThreeHomeo` (the homeomorphism from the sup-normed Hermitian five-sphere to the Euclidean one), `puncturedAcyclic_unitVectorsThree`, and `hbase_of_vanishing` — `hbase` from two cohomology vanishings and one Künneth factor, with no transport left |
| `CharClass/LIXStepEBase.lean` | 8796 | the two sphere factors: `puncturedAcyclic_sphereOne` (**the circle factor with no transport at all**, since `sphereOne` already *is* a metric sphere of an inner product space), `puncturedAcyclic_unitVectorsThree_of_homeo` (the five-sphere factor, modulo one model homeomorphism), `hbase_of_factors` (the join).  So `hbase` is now four factor-level hypotheses plus one homeomorphism |
| `CharClass/LIXStepEPunctured.lean` | 8795 | **`cc-thom`'s Step E, first piece**: `puncturedAcyclic_lixBase` and `puncturedAcyclic_lixBase_lixTopDegree` — the punctured-product vanishing at `S¹ × S⁵ × ∏ⱼ ℂP^{dⱼ}`, by induction peeling the **last** projective factor.  Four named hypotheses: three for the `ℂP` factor (`cc-projective`), one transporting the two sphere factors into this lane's models |
| `CharClass/LIXStepESpheresDischarged.lean` | 8854 | **the sphere factors, discharged too**: `isZero_cohomology_sphereOne`/`_sphereFive`, `kunnethFactor_unitVectorsThree` and its punctured companion, `hbase_lix` and `puncturedAcyclic_lixBase_final` (**unconditional** but for positivity of the dimensions), and `stepC_of_thomChain''` — **Step C over `cc-thom`'s chain bundle alone** |
| `CharClass/LemmaTwoStepCAbsEquiv.lean` | 8876 | **`cc-thom`'s `absEquiv`, discharged**: `unitVectorsThreeHomeoSphere` (this lane's `unitVectorsThreeHomeo` at the vendored `Sphere 5`, which is that type on the nose), `nonempty_absEquiv_lix` and `absEquivLix` (**the top line at `N`, unconditional** but for positivity), `ThomChainOpen` = `ThomChainData` minus `absEquiv` with `toThomChainData`, `ne_zero_of_thomChainOpen`, and `stepC_of_thomChainOpen` — **Step C over the three open Thom-class fields and `cc-relative`'s green ones** |
| `CharClass/LemmaTwoStepCEuler.lean` | 8887 | **Step C down to two open fields**: `ThomChainEuler` (`ThomChainOpen` with the local model made concrete, so `loc`, `locEquiv` and `hg` are gone and `hsu` has become `hne : su ≠ 0`), `ne_zero_of_thomChainEuler`, `stepC_of_thomChainEuler`.  The collapse is a **`ZMod 2` fact** (`∀ c : ZMod 2, c ≠ 0 → c = 1`, by `decide`) and is recorded as such, since over any other field the equality form carries a scalar the nonvanishing form does not |
| `CharClass/LemmaTwoStepCThom.lean` | 8888 | **Step C in the shape the Thom class will arrive in**: `ThomChainThom` names the Thom class `u` and trades `hgamma` for the naturality datum `hu`, over `cc-thom`'s combination theorem.  **The count does not improve** — two open before (`hne`, `hgamma`), two after (`hne`, `hu`) — but the shape matches what `cc-projective` will produce, so it can be populated directly instead of manufacturing the identification afterwards |
| `CharClass/LemmaTwoStepDLix.lean` | 8900 | **Step D at the geometric model, and both steps about one class**: `WuStepDLix` (Step D's data at `lixN` — the four space parameters, two sphere generators, three projections and the `a`/`b` fields all gone), `stepD_of_wuLix`, and **`lemmaTwoInput_lix`**, which assembles Step C and Step D about the SAME class on the SAME space.  Three open inputs remain in it, all `cc-projective`'s: `hu` and `hne` in `ThomChainThom`, and `S` in `WuStepDLix` |
| `CharClass/LIXStepEDischarged.lean` | 8853 | **the projective factor, discharged**: `puncturedAcyclic_lixBase'`, `puncturedAcyclic_lixZero'`, `stepC_of_thomChain'`.  All three projective hypotheses come from `cc-thom`'s green `puncturedAcyclic_CP`, `kunnethFactor_CP`, `kunnethFactor_CP_punctured`, so Step C's punctured acyclicity now rests on **four cohomology statements and nothing else** |
| `CharClass/LemmaTwoStepC.lean` | 8833 | **Step C at the real objects**: `lixZero`, `puncturedAcyclic_lixZero` (the `hacyclic` argument **discharged** from this lane's own recursion), `ThomChainData` (`cc-thom`'s remaining arguments, each field naming its owner: six green from `cc-relative`, one now green from `cc-thom`, **three open**), `ne_zero_of_thomChain`, `stepC_of_thomChain` |
| `CharClass/LemmaTwoTopClass.lean` | 8828 | **the last seam**: `lixN`, `lixRank`, `LixChernDeg`, `lixChernOf` (total, degreewise), `lixTopClass`, `lixChernOf_mappingTorus`, `stepC_of_chain`, `stepD_of_topClass`, and **`lemmaTwoInput_of`** — both steps of Lemma 2 about ONE `topClass` |
| `CharClass/LemmaTwoStepD.lean` | 8807 | **Step D at the real objects**, off the endpoint path: `WuStepDData` (four remaining hypotheses in the record — Künneth uniqueness, the Künneth decomposition, instability, the splitting principle and the slice — plus the space-independent Cartan formula outside it), `WuStepDData.gamma_top_eq_zero`, `stepD_of_wu` (the Step D half of `LemmaTwoInput`), and `ne_zero_of_degree_ne_zero` (the single-degree to `TotalH` bridge) |
| `CharClass/LemmaTwoGlue.lean` | 8677 | **the endpoint seam.** `lixChi` = `sin (π τ)` with its three values, `lixZeroPoint`, `lixSection` with `lixSection_continuous`/`_mem`/**`lixSection_eq_zero_iff`** (the Step C input, unconditional, one zero at `(southPole, (-e₃, basePoints))`), `stepD_of_parity`, `LemmaTwoInput`, `lemmaTwo_of_input`, `lemmaTwo_matrix_of_input`, **`lemmaTwoHolds_of`** giving `LIX.LemmaTwoHolds` |
| `CharClass/LemmaTwoStepA.lean` | 8673 | **Step A as a theorem.** `colAt_mul_conjTranspose_eq_rankOneProj`, `mul_source_of_isStarProjection`, `isStarProjection_FHmat`/`_EHmat`, `hasStepAUnitary_of_continuousMvNEquiv`, and **`lemmaTwo_of_stepC_stepD`** / `lemmaTwo_matrix_of_stepC_stepD` — Lemma 2 with `stepA` discharged, only the two cohomological steps left |
| `CharClass/LemmaTwoBridge.lean` | 8669 | `toMatC`, `matEval_toMatC`, `continuous_matEval`, `continuousMvNEquiv_of_murrayVonNeumannEquiv`, `continuous_FHmat`/`continuous_EHmat`, `not_murrayVonNeumannEquiv` = **Lemma 2 in the C\*-side vocabulary** |

## 1b. The final instantiation (overnight 09-05/06)

Step C's odd side needed concrete objects at `lixN dd` that **nobody had built**: there was
no `Bundle` over the LIX base, no `relCohomology` at `lixN`, and no map from chart
coordinates *into* the base.  The chain below is those objects, in dependency order, each
green and each hash read from the file's last commit.

| module | hash | jobs | content |
|---|---|---|---|
| `LIXBundleModel` | `5e4fdec0d` | 8830 | the mapping torus **as a `Bundle`**; `rank_lixBundle` (deliverable 1 of the brief); `rank_lixBundle_plusOne`, so `cc-cohom-api`'s fibre dimension is derived, not a numeral |
| `LIXBundlePair` | `32a35d1c3` | 8841 | the pair `(E, E∖0)`, the section into the total space, the map-of-pairs proof, and `lixSRel` |
| `LIXProjectiveChartSection` | `1b6d6aba9` | 8660 | the H-block section in the affine chart; **the leading behaviour is complex conjugation** |
| `LIXProjectiveChartDeriv` | `56dcb97a8` | 8668 | its strict derivative at the base point |
| `LIXProductChart` | `782c68b05` | 8670 | the product chart, both factors |
| `LIXFullChart` | `e7bb3c8d7` | 8834 | the chart at the full rank, by a **dimension count** rather than index plumbing |
| `LIXCircleChart` | `28622411c` | 8656 | circle factor of the base chart |
| `LIXSphereChart` / `LIXSphereChartHomeo` | `a8dc29bd4` / `78449113b` | 8664 / 8665 | five-sphere factor, then its inverse and partial-homeomorphism structure |
| `LIXProjectiveBaseChart` / `LIXProjectiveTowerChart` | `79f6af162` / `fb429ae1f` | 8665 / 8666 | projective factor, then the tower |
| `LIXBaseChart` / `LIXBaseChartHomeo` | `eaf9f57ed` / `3698ae1e7` | 8839 / 8842 | **the base chart**, then as a partial homeomorphism |
| `LIXExcisionChart` | `24831f6e7` | 8852 | excision at the section's zero, onto chart coordinates |
| `LIXChartIso` | `103ce8e56` | 8857 | **`H(lixN, lixN∖z) ≅ H(ℂ^r, ℂ^r∖0)`**, i.e. `exc ≫ chartIso` as one object |
| `LIXBallNeighbourhood` / `LIXBaseBall` | `985bcd072` / `7ca948e29` | 8858 / 8859 | a convex ball, then a **contractible** neighbourhood inside any prescribed open set |
| `LIXLocalPair` | `85686d12b` | 8871 | the bundle pair over that neighbourhood, **identified with the local model** |

**What is left on the odd side, and it is in two other lanes.**  `cc-relative`'s
contractible-base corollary (carried in `LIXLocalPair` as the named hypothesis `hprod`) and
`cc-thom`'s bridge `H^*(E, E∖0) ≅ H^*(P(E⊕1), P(E))`, without which the Thom class datum
`u`/`hu` stays open.  Everything geometric is green.

**Three corrections I made to instructions rather than working around them**, each verified
first: the injectivity was never one application (the base chart did not exist); the chart
covered only the section's trivial block, three of the four conjuncts of its zero condition;
and `u`/`hu` were reported as supplied when `cc-thom`'s two files were about different
spaces.

## 1a. EXPORTS — the two shapes of Lemma 2

Both are green and both are available; pick by vocabulary.

**Continuous-field model** (`CharClass/LemmaTwoStatement.lean`), which the whole
`CharClass` layer speaks:

```lean
theorem not_continuousMvNEquiv (topClass) (stepA) (stepC) (stepD) :
    ¬ ContinuousMvNEquiv (FHmat (dd := dd)) EHmat
```

**Matrix-over-functions model** (`CharClass/LemmaTwoBridge.lean`), which the C*-side
speaks:

```lean
theorem not_murrayVonNeumannEquiv (topClass) (stepA) (stepC) (stepD) :
    ¬ MurrayVonNeumannEquiv (toMatC (FHmat (dd := dd)) continuous_FHmat)
      (toMatC (EHmat (dd := dd)) continuous_EHmat)
```

`toMatC P hP` is the continuous field `P` read as a matrix over `C(M, ℂ)`, and
`matEval_toMatC` says the translation is the identity on points.  The bridge itself is
`continuousMvNEquiv_of_murrayVonNeumannEquiv`: evaluation at a point is multiplicative and
star-preserving, so the implementer transports verbatim.  **The bridge does not depend on
the cohomology layer**, so `cs-clutching` can join as soon as Steps A, C and D land.

Step A's target is `HasStepAUnitary dd`.

## 2. AUTHORED, UNVERIFIED

Nothing.  `LemmaTwoUnitary` was the last entry here; `cs-clutching` restored
`Analysis/LIXObstructionComplementUnitary.lean` to green (commit `434bd8eae`) and it
probes green at 8661.

## 3. NEEDS

### The Lemma 2 target shape was ill-typed; here is the one that is green

The shape circulated by the lead compares a `Fin 3 ⊕ HIdx`-indexed projection with a
`Fin 2 ⊕ HIdx`-indexed one.  `MurrayVonNeumannEquiv` takes two elements of **one** type,
so no instance of that statement typechecks.  The manuscript's own formulation avoids it:
both bundles are complements inside the same `V = 𝟏³ ⊕ H`,

```text
F ⊕ H = V − s sᴴ ,      𝟏² ⊕ H = V − e eᴴ ,
```

with `e = (e₃, 0)` and `s = (x, 0)`.  That is `FHmat` and `EHmat` in
`CharClass/LemmaTwoStatement.lean`, and `FHmat_eq_fromBlocks` shows the first block is
`𝟏³ − x xᴴ`, i.e. `STW59.Fproj`.

### From `cs-clutching` — Step A: DISCHARGED

`hasStepAUnitary_of_continuousMvNEquiv` in `CharClass/LemmaTwoStepA.lean` proves
`ContinuousMvNEquiv (FHmat) EHmat → HasStepAUnitary dd` outright, so Lemma 2 no longer
carries `stepA`: `lemmaTwo_of_stepC_stepD` takes only the two cohomological steps.  The
implementer is used **adjointed**, since `ContinuousMvNEquiv` as stated has the
`s`-complement as its source while `exists_continuous_corner_unitary_apply_eq` starts from
the `e`-complement.

Historical target, for reference: `HasStepAUnitary dd`: a continuous `G` on `baseM dd` with
`IsCornerUnitary (Vmat m) (G m)` and `G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0`.
The direction is the manuscript's own `g e = s`; no adjoint.  `cornerExtend` and
`isCornerUnitary_cornerExtend` do the extension by `1 − V`.

### For `cc-thom` — Step C, delivered

`eulerLocalHomeo` in `CharClass/LIXSectionLocalHomeo.lean` is the `OpenPartialHomeomorph`
`openPartialHomeomorphChartPair` takes, with the zero in the source, the origin in the
target and `e z = 0`.  `lixTopDegree` is the single degree index, in added form.

**The left-nesting constraint is discharged.**  `cc-thom`'s punctured-product recursion
needs `N` left-nested binary because Künneth is available one factor at a time only, while
`baseM dd` has the dependent product `∀ j : Fin ℓ, CP (dd j)` in its second slot.
`CharClass/LIXSectionNesting.lean` supplies the translation as the **binary step** rather
than as a type family: `baseSnocHomeo` peels one `ℂP` off to the right, `baseNilHomeo` is
the base case, and iterating the first from the second builds any left-nested chain.
`PuncturedAcyclic.congr'` transports the conclusion back.

### Historical — the earlier request to `cc-thom`

I withdraw the "homotopy through nowhere-vanishing maps" offer of the previous report:
`EulerLocalChart.openPartialHomeomorphChartPair` consumes an `OpenPartialHomeomorph`, so
the inverse function theorem is owed, and it is now supplied.  `manuscriptSection_eq_zero_iff_concrete`
gives the single zero and `hasStrictFDerivAt_trivialBlockChart` gives the strict derivative
there as a `ContinuousLinearEquiv`, so `HasStrictFDerivAt.toOpenPartialHomeomorph` applies
directly.  **Confirm the exact shape you want** (an `OpenPartialHomeomorph` from `N` to
`Fin r → ℂ` carrying `z` to `0`) and I will assemble it against your signature.

### Step C: what is still owed, and by whom

Of `cc-thom`'s ten chain arguments, two are now theorems of this lane and eight are
supplied elsewhere:

* `hacyclic` — discharged in `CharClass/LIXStepESpheresDischarged.lean`, unconditional.
* `absEquiv` — discharged in `CharClass/LemmaTwoStepCAbsEquiv.lean`, unconditional.
  `cc-thom`'s `absEquiv_lixN` needed only this lane's `unitVectorsThreeHomeo`, since the
  vendored `Sphere 5` *is* the metric sphere of `EuclideanSpace ℝ (Fin 6)`.
* `j`, `i`, `hexact`, `exc`, `chartIso`, `locEquiv` — green in `cc-relative`.
* `hsu` and `hg` — collapsed by `cc-thom`'s `ThomStepCEuler.lean` into the single
  nonvanishing `hne : su ≠ 0`; `hg` is genuinely discharged, `hsu` is renamed content.
* `hne` and `hgamma` — the two that remained on the odd side; `hgamma` becomes the Thom
  class datum `hu` in `ThomChainThom`.

**Lemma 2 as a whole now rests on three inputs, all `cc-projective`'s**: `hu` and `hne` on
the odd side, and the `ChernSplit` field `S` on the even side.  `lemmaTwoInput_lix` in
`CharClass/LemmaTwoStepDLix.lean` puts both steps about one class on one space, so the
contradiction no longer crosses a model boundary.

**The model seam, and why no probe could have caught it.**  Until 2026-09-05 the even side
was green at `KnTwo.NTop Y = (Y × S⁵) × S¹` while this lane was green at
`lixN dd = S¹ × (S⁵ × Y)`.  Both sides were correct proofs about *different spaces*, and a
build certifies that a file proves what it says, never that what it says is what another
lane needs — so the usual signal is not merely weak here, it is structurally incapable of
firing on either side.  `cc-wu`'s `ParityEvenTransport.lean` closed it after the mismatch
was found by reading two statements side by side.

**Accounting note, resolved.**  `cc-thom` first reported this as leaving `hsu` alone.  The
three improvements — the nonvanishing form, the `Nonempty` top line and the naturality
discharge — lived in three theorems with no single one carrying all three, so the shortest
Step C then available had two open fields.  `cc-thom` has since published the combination
`topChernClass_ne_zero_of_su_ne_zero_naturality_line` and confirmed that the naturality
data is **not** green: `hu` mentions a Thom class that does not yet exist over the real
bundle.  So the count is two either way, and the naturality route is a change of shape
rather than a reduction.  Both shapes are published: `stepC_of_thomChainEuler` for a
consumer holding `gamma` first, `stepC_of_thomChainThom` for one holding the Thom class.

`ThomChainOpen` is exactly those remaining fields, so the shape of what is owed is now
readable off one structure rather than by subtraction.

### From `cc-cohom-api`, `cc-steenrod`, `cc-projective` — the fields of `LIXParityInput`

The Künneth inclusion, the Steenrod squares and the mod-2 Chern classes, in cc-wu's
element-level shape.  The slice hypothesis is cheap because `mappingTorus_north` is an
equality, not an equivalence.

## 4. TRAPS

* **The lexical `sorry` scan is wrong in both directions.**  It flags docstring prose that
  *asserts* the absence (three of this lane's files say "never a `sorry`" inside
  backticks), and it misses the real hazard: an unrelated elaboration failure makes clean
  declarations report "declaration uses `sorry`" (see the undecidable-`dite` entry below),
  so a file can pass the grep and fail the build, or fail the grep and be perfectly
  hygienic.  **The build is the only signal that is not wrong in one direction or the
  other.**
* **Two index shifts in one argument is where reconstruction from outside goes wrong.**
  `cc-wu`'s `b` is indexed by the *total* index while its degree is `2k − 6`, a shift of
  three; and the ring degree is `6 + n` against the degreewise index `n`, a shift of six.
  Both appear in the same Künneth argument.  This lane declined to write that argument from
  outside for exactly this reason, and `cc-wu` independently confirmed it was the right
  call.
* **A green lemma in the right area is not the hypothesis it is offered for.**  The
  two-sphere Künneth injectivity was announced as discharging `tx_inj`; the green statement
  is for *one* sphere factor in the graded world, the field is for *two* in the ring.  One
  grep of both statements showed it.  Check before propagating.

* **The Whitehead path does not descend to the circle.**  Its entries are degree-four
  monomials in the quarter angle, polynomial in `(cos πt, sin πt)` but not in
  `(cos 2πt, sin 2πt)`, and running the rotation over the whole circle returns it to `1`,
  which *trivialises* `h (V ⊕ 0) hᴴ`.  Clutching over the two-point equator avoids the
  quotient and gives the north-pole slice on the nose.
* **The `ℂP` section must be the column, not the row.**  `dualTautSection` is the `i`-th
  **row** and `dualTautComponent_isSection` shows it is fixed by the *conjugate*
  projection.  With `H` built from the projections themselves, `IsMTSectionData`'s
  `south_mem` is then **false**, not merely unproved.  `tautColSection` (the `(i+1)`-st
  column) is fixed by the projection itself, by `entry_sum_mul`; same zero locus, by
  `entry_symm`; the affine chart model picks up a complex conjugation, whose derivative is
  still a real-linear isomorphism.
* **The IFT step needs no `EuclideanSpace` and no `WithLp` bridge.**  `S⁵` is
  `unitVectors (Fin 3)` inside the *sup-normed* function space, while
  `eulerLocalModelEquiv` wants a real inner product space and an orthogonal-complement
  submodule.  Charting the sphere at `-e₃` by `(u, v, c) ↦ ![u, v, c i − √(1 − ‖·‖²)]` on
  the plain product `ℂ × ℂ × ℝ` parametrises the real tangent space `{ξ : re ξ₂ = 0}`
  directly; the derivative and its inverse are then four lines of arithmetic.
* **`χ = sin(π τ)` is the right bump.**  The zero-locus argument constrains `χ` only at
  `0`, `1/2` and `1`, and the sine is analytic, so strict differentiability is free.  Do
  not build a smooth bump function.
* **`Continuous.if_le` needs both branches continuous globally.**  So the section is
  `W *ᵥ (ξ, 0)` and `W *ᵥ (0, η)` with no `1/(1±t)` normalisation; the surviving component
  carries the factor `(1 ± t)/2 ≥ 1/2` on its own half, which is what makes the zero
  analysis work anyway.
* `Matrix.trace_fromBlocks` and `Matrix.blockDiagonal'_mulVec` do **not** exist at the pin;
  `trace_fromBlocks'` (square blocks), `trace_fromBlocks_gen` (different index types) and
  `blockDiagonal'_mulVec` are the two-line replacements.
* `WithLp` is a **structure** at this pin, so `EuclideanSpace ℝ (Fin 2)` is not defeq to
  `Fin 2 → ℝ`; build points with `WithLp.toLp 2 ![a, b]`.
* **`congr 1` splits dependent proof arguments.**  Diagnosed in `cc-steenrod`'s
  `cocycleClass_add`, where it descends into a `Classical.choose` index; prove additivity
  one level down on the cycle and push up with `map_add`.
