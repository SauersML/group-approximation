# Lane `ejz-integral`: the general-characteristic Ershov–Jaikin-Zapirain residue

Date opened 2026-09-07.  Lane owner: session `ejz-integral` of the non-MF formalization
campaign.  Everything below is a statement about the repository as it stands on
`origin/main`; nothing here is assumed anywhere in the Lean tree.

## 0. One-paragraph summary

Theorem 2 of `non_mf_groups_exist.tex` cites Ershov–Jaikin-Zapirain, *Property (T) for
noncommutative universal lattices*, Invent. Math. 179 (2010), Theorem 1.1: `EL_n(R)` has
property (T) for every finitely generated associative unital ring `R` and every `n ≥ 3`.
The manuscript actually **uses** that theorem only for `R = L_{F_2}(1,2)`, a finitely
generated `F_2`-algebra, and for that case the tree proves it unconditionally
(`GroupApproximation/Manuscript/NonMF/PriorWorkErshovJaikinZapirain.lean`, whose proof runs
through `primeCharFinitelyGeneratedRingElementary_hasKazhdanPropertyT`).  What is open is the
theorem in the generality in which it is *cited*: arbitrary characteristic.  The open part is
one analytic estimate over `ℤ⟨X⟩`, everything else — the descent to a free integral algebra,
the rank propagation, the `A₂` orthogonality half of the Kazhdan certificate — is proved.

## 1. The open Prop, exactly

The single named Prop that the downstream lanes consume, in
`GroupApproximation/PropertyT/EJZIntegralReduction.lean`:

```lean
def GroupApproximation.FinitelyGeneratedRingGeneralRankElementaryPropertyT : Prop :=
  ∀ (A : Type) [Ring A], IsFinitelyGeneratedRing A →
    ∀ (n : ℕ), 3 ≤ n →
      HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin n) A)
```

Two proved implications reduce it.  In the same file:

```lean
def GroupApproximation.FreeIntegralGeneralRankElementaryPropertyT : Prop :=
  ∀ (X : Type) [Fintype X] (n : ℕ), 3 ≤ n →
    HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin n) (FreeAlgebra ℤ X))

theorem GroupApproximation.freeIntegralGeneralRank_implies_finitelyGeneratedRingGeneralRank :
    FreeIntegralGeneralRankElementaryPropertyT →
      FinitelyGeneratedRingGeneralRankElementaryPropertyT
```

and in `GroupApproximation/PropertyT/EJZIntegralGeneralRankReduction.lean`:

```lean
def GroupApproximation.IntegralFreeColumnPlaneMassBounds : Prop :=
  ∀ (X : Type) [Fintype X], ∃ C : ℝ, 0 ≤ C ∧
    IntegralCharacterMass.ColumnPlaneMassBound.{0, 0}
      (FreeAlgebra ℤ X) (IntegralCharacterMass.integralControlSet X) C

theorem GroupApproximation.printedEJZColumnPlaneReduction :
    IntegralFreeColumnPlaneMassBounds →
      FinitelyGeneratedRingGeneralRankElementaryPropertyT
```

So `IntegralFreeColumnPlaneMassBounds` is *the* residue: it is strictly smaller than the
printed theorem and it implies it.  `ColumnPlaneMassBound` is
`GroupApproximation/PropertyT/IntegralCharacterMass.lean`:

```lean
def ColumnPlaneMassBound (R : Type u) [Ring R]
    (S : Finset (elementaryGroup (Fin 3) R)) (C : ℝ) : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
    ∀ (rho : elementaryGroup (Fin 3) R →* (E ≃ₗᵢ[ℝ] E)) (z : E) (δ : ℝ),
      0 < δ → (∀ s ∈ S, ‖rho s z - z‖ < δ) →
        ∀ (i j k : Fin 3) (_hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
          ‖KazhdanFixedSpace.subgroupMovingProjection rho
              (elementaryRootSubgroup i k hik ⊔ elementaryRootSubgroup j k hjk) z‖ ≤ C * δ
```

`integralControlSet X` is the `6 * (|X| + 1)` element set `{x_ij(1)} ∪ {x_ij(x_l)}`, one copy
in each of the six ordered roots of rank three.

### 1.1 Equivalent projection-free forms (all proved)

`GroupApproximation/PropertyT/IntegralColumnPlaneReduction.lean` proves that the residue is
equivalent, up to universal factors of two, to three progressively more elementary
statements.  Any one of them closes the theorem:

| name | content |
| --- | --- |
| `exists_columnPlaneMassBound_iff_exists_displacementBound` | replace the moving projection by a uniform displacement bound on the two-root subgroup |
| `integral_exists_columnPlaneMassBound_iff_exists_rootCoefficientBound` | replace the subgroup by a single root: `∃ C, ∀ ρ z δ, (control set within δ) → ∀ i ≠ k, ∀ a : ℤ⟨X⟩, ‖ρ (x_ik a) z − z‖ ≤ C δ` |
| `integral_exists_columnPlaneMassBound_iff_exists_integralStageBound` | the same with `a` ranging over one finite-rank degree stage, with `C` independent of the stage |

The last row is the sharpest formulation of the gap: *one displacement constant, uniform in
the polynomial degree*.

### 1.2 Consumers

* `printedEJZIntegralReduction` and `printedEJZColumnPlaneReduction`, both closed-axiom
  audited, are the only Lean consumers on `origin/main`.
* Lane `ring-b-end` carries `FinitelyGeneratedRingGeneralRankElementaryPropertyT` as an
  explicit hypothesis.
* The manuscript's own use of EJZ does **not** consume it: `PriorWork.ershovJaikinZapirain_binaryLeavitt_application`
  is unconditional through the characteristic-two route.

## 2. What is already proved, and where the integral route stops

The rank-three certificate is `IsKazhdanSubset(rootSet, κ)` (the root set is a Kazhdan set)
plus `ControlsSubsetDisplacement(controlSet, rootSet, C)` (the finite control set dominates
the root set).

* **First half: closed, unconditionally, for every ring.**
  `A2MagicExponentFree.elementary_exists_rootSet_isKazhdan` — no exponent, no
  characteristic, no finiteness hypothesis.  This is the `A₂`-graded orthogonality theorem
  in the generality Ershov and Jaikin-Zapirain state it.
* **Second half: this lane.**  Note the first half alone is worthless: *every* group `G` is
  a Kazhdan set for itself with constant `√2` (convex-hull argument), so an infinite Kazhdan
  set carries no information without the quantitative control half.  The control half is
  where finite generation of the ring must enter, and it cannot be obtained by any
  compactness or direct-integral argument: it is a genuinely quantitative statement.

Unconditional pieces of the control half already on `main`:

* `IntegralScalarRootDisplacement.norm_integral_scalarRoot_displacement_le_of_controlSet_near` —
  every **integer scalar** coefficient in every root is controlled with the single constant
  `12000`, via the `P13` presentation of `SL₃(ℤ)`.  This is the degree-zero stage, and it is
  coefficient-independent.
* `IntegralColumnPlaneSpectralMassBound.scalarTorusMeasure_punctured_mass_le` — the scalar
  torus spectral measure of the column plane has mass at most `(2 + √10)² δ²` away from its
  trivial character.  This is the `ℤ² ⋊ SL₂(ℤ)`-shaped estimate, run on the two-torus with
  the four unit shears, and it is exactly the *degree-zero region* of the general estimate.
* `IntegralCharacterMass.norm_displacement_wordMonomial_le` — the Steinberg recursion gives
  `‖ρ(x_ij(w))z − z‖ ≤ (3·2^{|w|} − 2)·δ` for a word monomial `w`.  The constant is
  exponential in the word length; killing that exponential is the whole problem.
* `IntegralPolynomialDisplacement.exists_integral_polynomial_displacement_constant` — a
  finite constant for each *fixed* polynomial, unbounded as the polynomial varies.

## 3. Diagnosis: what the finite-field proof used that the integral file does not

The characteristic-`p` proof lives in `FreeRootPlaneMass.lean` / `FreeRootPlaneFourier.lean`
and terminates in

```lean
FreeRootPlaneMass.norm_joinRootMovingProjection_sq_le_explicit_errors
```

which bounds the squared moving projection of the join of the two column roots by

1. `4 · gap(ψ)⁻¹ · (∑_{t ∈ K} ‖ρ(x_ik(t))z − z‖² + ∑_{t ∈ K} ‖ρ(x_jk(t))z − z‖²)` — the
   **degree-zero** term, a sum over the *finite* field;
2. `(3/2) · ∑_{x ∈ X} 2‖z‖·‖ρ(x_ji(x))z − z‖ + (same with i,j swapped)` — the **generator
   shear** term;
3. two unit-shear terms;
4. `(9/2) ·` boundary masses, which vanish in the degree limit
   (`tendsto_firstBoundaryMass_zero`).

The engine is a valuation descent on the dual, `sum_planeMass_AB_le_coarse_CD` and
`sum_planeMass_CB_le_coarse_AD`, whose combinatorial heart is
`coarse_pairRegion_of_fine_AB_opposite` / `coarse_pairRegion_of_fine_CB_forward`.  Written
out: for a dual functional `φ` let `val φ` be the least word degree at which `φ` is
nontrivial, let `∂_x φ` be the left derivative `(∂_x φ)(w) = φ(x·w)`, and classify a
character of the plane by the pair `(val φ₁, val φ₂)` into regions

* `D`: some `val = 0` (visible already at the unit coefficient),
* `A`: `val φ₂ < val φ₁`, `B`: `val φ₁ = val φ₂ > 0`, `C`: `val φ₁ < val φ₂`.

Conjugation by `x_{10}(x)` sends `(φ₁, φ₂) ↦ (φ₁ + ∂_x φ₂, φ₂)` and by `x_{01}(x)` sends
`(φ₁, φ₂) ↦ (φ₁, φ₂ + ∂_x φ₁)`.  If `val φ₂ = v > 0` there is a generator `x` with
`val (∂_x φ₂) = v − 1` exactly, so region `A ∪ B` is pushed into `C ∪ D` one degree lower,
and symmetrically `C ∪ B` into `A ∪ D`.  Disjointness of the images across the `|X|` choices
of `x` is obtained by carrying the *selector* (the least leading generator index) into the
target: the opposite shear does not touch the second coordinate, so the selector is
preserved, and the images sit in disjoint selector fibres.  That is why one copy of the
target mass, not `|X|` copies, appears in the estimate.

**None of that valuation descent exists over `ℤ`.**  The integral file
`IntegralColumnPlaneSpectralMassBound.lean` (2337 lines) builds the whole apparatus —
`rootWordVisibleSet`, `leastRootWordDegreeWithin`, `leastRootWordDetectionSet` and its
disjointness and covering, `wordPairRegion` with the same `A/B/C/D/zero` classification,
Borel measurability of every region — and then analyses **only the unit shears**
`x_{01}(1)`, `x_{10}(1)`.  Multiplication by `1` does not lower a valuation, so the unit
shear cannot move a region downward: the file proves `upperUnitCharacterAction_mapsTo_A`,
`wordPairRegion_upperUnit_eq_B_or_C_of_eq_B`, and terminates at

```lean
columnPlaneSpectralMeasure_A_union_B_le_ABC :
  μ (A ∪ B) ≤ μ ((A ∪ B) ∪ C) + 2δ√(μ (A ∪ B)) + δ²
```

which is **vacuous**: the right side already contains the left.  The file's own docstring is
honest about it ("no claim is made here that a shear cannot cancel the two corresponding
circle phases").  So the integral development stops precisely one step short of the step
that does all the work in characteristic `p`.

**The obstruction the module docstrings name — "the finite dual becomes a torus, the sum
becomes an integral, and there is no equidistribution statement" — is not the real
obstruction.**  The measure-theoretic replacement for the finite sum is already built and
used: `MeasurableQuasiInvariantAtScale` gives `|μ(gB) − μ(B)| ≤ 2δ√(μ B) + δ²` for every
shear in the control set, and crucially

```lean
IntegralColumnPlaneSpectralShear.upperShear_measurableQuasiInvariantAtScale
    (X) (rho) (z) (hz) (delta) (hdelta) (hnear) (q : Option X)
IntegralColumnPlaneSpectralShear.lowerShear_measurableQuasiInvariantAtScale  -- same signature
```

are stated for **every** `q : Option X`, that is for the unit shear *and every generator
shear*.  The generator instances are proved and unused.

## 4. Assessment of the mathematical route

The valuation argument is characteristic-free.  Over `ℤ` a character `χ` of the plane is a
homomorphism to `ℝ/ℤ`, `val χ` is the least word degree at which `χ` is nontrivial (this is
`leastRootWordDegreeWithin`, already defined and already proved to have disjoint, covering,
Borel fibres), and the two facts the descent needs both hold verbatim:

* **Descent.** If `χ` is trivial on every word of degree `< v` and nontrivial on some word
  `w` of degree `v ≥ 1`, write `w = x·w'`; then `∂_x χ` is nontrivial at `w'` (degree
  `v − 1`) and trivial at every word of degree `< v − 1` (because `x·u` then has degree
  `< v`).  So `val (∂_x χ) = v − 1` exactly.  No division, no field, no finiteness.
* **Non-archimedean addition.** If `val ψ < val φ` then `val (φ + ψ) = val ψ`, for the same
  reason: at degree `val ψ` the summand `φ` is still trivial.

So the route is: **port the generator-shear valuation descent from `FreeRootPlaneMass` to
`IntegralColumnPlaneSpectralMassBound`, replacing the finite dual sum by the spectral
measure and the finite-field degree-zero term by the already-proved torus bound.**  The
region `D` of the integral classification is exactly `unitRootNontrivialSet`, and
`scalarTorusMeasure_punctured_mass_le` already bounds its mass by `(2 + √10)² δ²`.  The
boundary terms vanish in the limit by `disjoint_leastRootWordDetectionSet` together with
`iUnion_leastRootWordDetectionSet_range`, both proved.

I regard this as a finite, mechanical-but-long formalization rather than an open
mathematical problem.  The mathematical content that is *not* in the tree is one page; the
Lean content is on the order of the `FreeRootPlaneMass` file it mirrors.

### 4.1 The concrete missing lemmas, in dependency order

1. `generatorShearCharacterAction` — the dual action of `x_{01}(ι x)` and `x_{10}(ι x)` as a
   `MeasurableEquiv` on `Spectrum rho`, with the coordinate formula.  The formula is already
   proved for an arbitrary ring coefficient `r`:
   `IntegralColumnPlaneSpectralTorus.coordinateAngle_characterAction_upper_one`
   gives `coordinateAngle (1,a) (u_r · χ) = coordinateAngle (0, r*a) χ + coordinateAngle (1,a) χ`.
2. `exists_generator_leastRootWordDegree_pred` — the descent above, at the level of
   `leastRootWordDegreeWithin`.  Statement:
   ```lean
   theorem exists_generator_descent (b : Fin 2) (n : ℕ) (chi : Spectrum rho)
       (hvis : chi ∈ rootWordVisibleSet rho b (n + 1))
       (hpos : 0 < leastRootWordDegreeWithin rho b (n + 1) chi) :
       ∃ x : X, ∀ w : FreeMonoid X,
         freeWordLength X w = leastRootWordDegreeWithin rho b (n + 1) chi - 1 → …
   ```
   concretely: the shifted character `a ↦ coordinateAngle (b, ι x * a) χ` has least visible
   degree exactly one less.
3. `wordPairRegion_generatorShear_*` — the four placement lemmas replacing
   `wordPairRegion_upperUnit_*`: `A ∪ B` at stage `n + 2` goes to `C ∪ D` at stage `n + 1`
   under the *selected* lower generator shear, `C ∪ B` to `A ∪ D` under the upper one.
4. `leastLeadingGeneratorIndex` for the integral spectrum and the measurable partition of
   `A ∪ B` into its `|X|` selector fibres, with the target fibres disjoint.
5. The mass inequality at one stage, then the limit `n → ∞`, then
   `μ (fullPlaneNontrivialSet rho) ≤ K(|X|) · δ²`.
6. Assembly: `∫ ‖χ(coordinate q) − 1‖² dμ ≤ 4 μ (fullPlaneNontrivialSet)` with
   `RepresentedRootPlaneSpectralMeasure.integral_coordinate_displacement_sq` gives
   `RootCoefficientDisplacementBound (FreeAlgebra ℤ X) (integralControlSet X) (2√K)`, and
   `integral_exists_columnPlaneMassBound_iff_exists_rootCoefficientBound` closes
   `IntegralFreeColumnPlaneMassBounds`.

### 4.2 Routes considered and rejected

* **Soft conversion of the infinite Kazhdan set to a finite one.**  Rejected: any group is a
  Kazhdan set for itself with constant `√2`, so `IsKazhdanSubset(rootSet, κ)` has no soft
  consequence.  Some quantitative estimate is unavoidable.
* **Word-by-word transport.**  For `χ` nontrivial at the word `w` in coordinate 0, the shear
  `x_{01}(w)` carries `χ` into the unit-detected region, so `μ(U_w) ≤ μ(U_1) + err(w)`.  But
  `x_{01}(w)` is not in the control set, and the Steinberg recursion gives it displacement
  `(3·2^{|w|} − 2)δ`, so `err(w)` is exponential in `|w|` and the countable union over `w`
  diverges.  This is exactly the exponential the valuation descent avoids, by moving
  *one letter at a time* and paying only the `|X|` generator displacements once per stage.
* **Qualitative relative property (T) for the pair `(EL₃(ℤ⟨X⟩), plane)` followed by a
  soft linear bound.**  The pair is not normal, the plane's normalizer `R² ⋊ EL₂(R)` is not
  finitely generated by the control set (inside rank two there is no third index to build
  `x_{01}(x_1x_2)` from `x_{01}(x_1)`, `x_{01}(x_2)`), and the qualitative-to-linear
  conversion is itself a direct-integral argument with no Mathlib support.  Strictly harder
  than the direct route.

## 5. Status of this lane's landings

* `notes/nonmf-lane-reports/ejz-integral.md` (this file).

## 6. If the lane closes nothing further

The residue to leave standing is exactly `FinitelyGeneratedRingGeneralRankElementaryPropertyT`
in `GroupApproximation/PropertyT/EJZIntegralReduction.lean`, with
`printedEJZColumnPlaneReduction` recording that it follows from the single analytic family
`IntegralFreeColumnPlaneMassBounds`.
