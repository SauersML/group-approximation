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

## 2. AUTHORED, UNVERIFIED

* `CharClass/LemmaTwoUnitary.lean` — blocked on `cs-clutching`'s
  `Analysis/LIXObstructionComplementUnitary.lean`, which is red at the pin.  Not a
  `sorry`; a real proof waiting on a real dependency.

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

### From `cs-clutching` — Step A

Target `HasStepAUnitary dd`: a continuous `G` on `baseM dd` with
`IsCornerUnitary (Vmat m) (G m)` and `G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0`.
The direction is the manuscript's own `g e = s`; no adjoint.  `cornerExtend` and
`isCornerUnitary_cornerExtend` do the extension by `1 − V`.

### From `cc-thom` — Step C

I withdraw the "homotopy through nowhere-vanishing maps" offer of the previous report:
`EulerLocalChart.openPartialHomeomorphChartPair` consumes an `OpenPartialHomeomorph`, so
the inverse function theorem is owed and is being supplied.  What is already deliverable:
`manuscriptSection_eq_zero_iff_concrete` gives the single zero, and
`eulerContinuousLinearEquiv` gives the derivative there as a `ContinuousLinearEquiv` on
`(ℂ × ℂ × ℝ) × ℝ`.  What remains on my side is the `HasStrictFDerivAt` of the section read
in those charts.

### From `cc-cohom-api`, `cc-steenrod`, `cc-projective` — the fields of `LIXParityInput`

The Künneth inclusion, the Steenrod squares and the mod-2 Chern classes, in cc-wu's
element-level shape.  The slice hypothesis is cheap because `mappingTorus_north` is an
equality, not an equivalence.

## 4. TRAPS

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
