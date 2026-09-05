# Lane `cc-lix-odd` — mapping torus (Step B), the section and its zero (Step C), Lemma 2

Owns `GroupApproximation/CharClass/MappingTorus*.lean`,
`GroupApproximation/CharClass/LIXSection*.lean`,
`GroupApproximation/CharClass/LemmaTwo*.lean`; namespace `GroupApproximation.CharClass`.

## 1. GREEN

*(job counts appear here only after a probe prints `Build completed successfully (N jobs)`
with a `Built …` line for the module.)*

## 2. AUTHORED, UNVERIFIED

* `CharClass/MappingTorusProjection.lean` — `IsCornerUnitary`, `cornerExtend`,
  `mtSym`/`mtProj` (clutched projection), `mtTrans` (transition matrix), `IsCircleChart`,
  `sphereOne` with `northPole`/`southPole`, `mappingTorus` = `W_g`, with
  `mappingTorus_isStarProjection`, `mappingTorus_continuous`, `mappingTorus_north`
  (`W_g` on the north-pole slice is `V ⊕ 0` **on the nose**), `mappingTorus_south`,
  `trace_mappingTorus` (`rank W_g = rank V`).
* `CharClass/MappingTorusSection.lean` — `mappingTorus_eq` (block normal form),
  `IsMTSectionData`, `mtSection`, `mtSection_continuous`, `mtSection_mem`,
  `mtSection_eq_zero_iff`, `mtSection_eq_zero_iff_of_north_ne_zero`.

## 3. NEEDS (signatures wanted from peers)

### From `cc-thom` (Step C consumer side)

I can deliver the odd side in the following shape, and **not** in a shape that requires a
derivative or an orientation.  Please state the Thom/Euler interface so that it consumes:

```lean
-- `N` a compact space, `W : N → Matrix (n ⊕ n) (n ⊕ n) ℂ` a continuous projection-valued
-- map of constant trace `r`, `S : N → (n ⊕ n) → ℂ` continuous with `W z *ᵥ S z = S z`.
-- (a) exactly one zero:
--        ∃! z₀, S z₀ = 0
-- (b) a local model at that zero: a homeomorphism `φ` of a neighbourhood `U ∋ z₀` onto an
--     open `Ω ∋ 0` in `ℂ^r` (equivalently `ℝ^{2r}`) and a homotopy
--        H : [0,1] × Ω → ℂ^r,  H 0 = (S read in a local trivialisation of W over U),
--        H 1 = a linear isomorphism,  ∀ τ w, H τ w = 0 ↔ w = 0
-- ⊢ γ_r(W) ≠ 0.
```

The homotopy form (b) is the one the paused fleet's `AlgTop/CPTautologicalSection.lean`
already produces for the `ℂP` factors (`tautChartHomotopy_eq_zero_iff`), and it is the one
a **mod-2** local index consumes: no derivative, no sign, no orientation.  If `cc-thom`
insists on `HasStrictFDerivAt` + `HasStrictFDerivAt.toPartialHomeomorph`, say so in your
report and I will differentiate the chart formulas instead; but the extra work is real
(`Real.arccos`, `Real.sqrt` of `1 - ‖w‖²`, and the affine `ℂP` charts all have to be
differentiated) and it buys nothing mod 2.

### From `cs-clutching` (Step A)

```lean
-- over `M`, `V` a continuous projection-valued map, `e s : M → ℂ^K` continuous unit
-- sections of `V` (`V m *ᵥ e m = e m`, `‖e m‖ = 1`, likewise `s`), and
--   MurrayVonNeumannEquiv (complement of e in V) (complement of s in V)
-- ⊢ ∃ g : M → Matrix (Fin K) (Fin K) ℂ, Continuous g ∧
--     (∀ m, g m * V m = g m) ∧ (∀ m, V m * g m = g m) ∧
--     (∀ m, (g m)ᴴ * g m = V m) ∧ (∀ m, g m * (g m)ᴴ = V m) ∧
--     (∀ m, g m *ᵥ e m = s m)
```

**Direction check (done, recorded here).**  My mapping torus glues the southern field to
the northern one by `η = G *ᵥ ξ` at `y = 1`.  With the northern field constant `= e` and
the southern field the manuscript's path from `e` (at `y = -1`) to `s` (at `y = 1`), the
descent condition is `G *ᵥ e = s`, i.e. **the manuscript's own `g e = s`**.  No adjoint is
needed anywhere.  If Step A delivers `g` with `g s = e` instead, I instantiate with `gᴴ`.

`cornerExtend V g = g + (1 - V)` turns that `g` into the unitary `G` of the full matrix
algebra that `mappingTorus` consumes (`isCornerUnitary_cornerExtend`).

### From `cc-wu` (Step D)

I own the instantiation of your `ParityData` from the concrete cohomology of
`N = S¹ × S⁵ × Y`.  Please keep the interface *element-level* (a type `H` with `+`, `*`,
a grading predicate or graded pieces, `Sq`, and the listed identities) so it can be fed by
`cc-cohom-api`'s `cohomologyZMod2` API through explicit ring maps; a bundled
`GradedAlgebra` would cost me a transport layer.

### From `cs-stages`

`Analysis/LIXBlockProjections.lean`'s `Hproj`/`Eproj` live over `baseX i = S⁴ × Y_i`.
Lemma 2 needs the **`S⁵`** base.  I define the general-`d` projections over
`↥sphereFive × ∏ⱼ CP (dd j)` in my own files rather than editing yours; if you want a
shared `Hproj` over a general base, say so and I will use it.

## 4. TRAPS

* **The Whitehead path does not descend.**  `h t = diag(G,1) R t diag(Gᴴ,1) (R t)ᵀ` with
  `R t` the rotation by `π t / 2` is a genuine path from `1` to `diag(G, Gᴴ)`, and
  `t ↦ h t (V ⊕ 0) (h t)ᴴ` really is a loop (I computed the entries: they are the degree-4
  monomials in `(cos(π t/2), sin(π t/2))` applied to `V, g, gᴴ, g², (gᴴ)²`, and both ends
  give `V ⊕ 0`).  But the loop only descends through the quotient `[0,1]/(0∼1)`: the
  entries are polynomial in `(cos π t, sin π t)`, **not** in `(cos 2π t, sin 2π t)`, and
  running the rotation over the full circle sends `h` back to `1`, which trivialises
  `h (V⊕0) hᴴ` outright.  Do not try to reparametrise; clutch instead.
* **Clutching over the two-point equator is strictly better.**  `S¹ = {y² + t² = 1}` with
  transition `G` at `y = 1` and `1` at `y = -1`; the transition matrix
  `f y = if 0 ≤ y then y • G else (-y) • 1` is continuous because both branches vanish at
  `y = 0`, and `fᴴ f = f fᴴ = (1 - t²) • 1` is exactly the clutching normalisation.  The
  north-pole slice then gives `V ⊕ 0` **on the nose**, with no Murray--von Neumann
  transport to carry through Step D.
* **`Continuous.if_le` needs both branches continuous globally**, not just on their half.
  So the section must be `W *ᵥ (ξ, 0)` and `W *ᵥ (0, η)` — with no `1/(1+t)` normalisation,
  which would blow up at the far pole.  The zero analysis still works because the surviving
  component carries the factor `(1 ± t)/2 ≥ 1/2` on its own half.
* `Matrix.trace_fromBlocks` does **not** exist at the pin; `trace_fromBlocks'` in
  `MappingTorusProjection.lean` is a two-line replacement.
* `WithLp` is a **structure** at this pin, so `EuclideanSpace ℝ (Fin 2)` is not defeq to
  `Fin 2 → ℝ`; build points with `WithLp.toLp 2 ![a, b]` and read coordinates through the
  `CoeFun`, with `PiLp.continuous_apply` for continuity.
