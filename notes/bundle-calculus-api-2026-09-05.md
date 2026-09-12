# Bundle calculus: the shared API (lane `found-bundle-calculus`, 2026-09-05)

Consumers: `found-chern-classes`, `found-ktheory-bott`, `found-euler-class`,
`found-mapping-torus-parity`, `lix-spaces`, `lix-clutching`, `lix-obstruction`.

Mathlib names below are checked at pin `81a5d257` (toolchain v4.32.0).

> **Revision.** The first version of this note told five lanes to move their
> ambient algebra, and introduced an `MvNEquiv` that duplicated the repository's
> existing `MurrayVonNeumannEquiv`.  Both were wrong; both are corrected below,
> and the code has been changed rather than the lanes.

---

## 1. Do not invent a new equivalence relation

The campaign already has one, and it is exactly the right one:

```lean
-- GroupApproximation/Analysis/FiniteCStarMurrayVonNeumann.lean
def MurrayVonNeumannEquiv {A : Type*} [Mul A] [Star A] (p q : A) : Prop :=
  ∃ v : A, star v * v = p ∧ v * star v = q
```

with, in that file, `MurrayVonNeumannEquiv.refl`, `.symm`, and
`.of_isometry_conjugate` (`p ∼ u p u*` from `star u * u = 1` alone), and in
`GroupApproximation/KTheory/MatrixProjection.lean`, `.trans`, `.map`, plus
`blockSum`, `isStarProjection_blockSum`, `murrayVonNeumannEquiv_blockSum` and
`murrayVonNeumannEquiv_submatrix`.

**So the direct sum, the padding maps, and the reindexing moves already exist.**
Read `KTheory/MatrixProjection.lean` before building any of them.

Projections are Mathlib's `IsStarProjection` (fields `.isIdempotentElem`,
`.isSelfAdjoint`, both `protected`, reached by dot notation).  `IsIdempotentElem`
is a plain `def`, so `rw` needs `hp.isIdempotentElem.eq`, while
`have h : p * p = p := hp.isIdempotentElem` is fine.

## 2. The ambient algebra: keep `SectionAlgebra`

```lean
-- GroupApproximation/Analysis/LIXCornerAlgebra.lean
abbrev SectionAlgebra (X : Type*) [TopologicalSpace X] (ι : Type*) [Fintype ι]
    [DecidableEq ι] := C(X, CStarMatrix ι ι ℂ)
```

At the pin this type is a `CStarAlgebra` (given `[CompactSpace X]`) and carries
the pointwise `PartialOrder`, but it has **no `StarOrderedRing` instance** — and
without one there is no `ℝ≥0` continuous functional calculus, so no inverse
square root, so no homotopy invariance.

That is a one-instance gap, not a structural defect, and the instance is now
supplied:

```lean
-- GroupApproximation/AlgTop/BundleCalculusTransport.lean
instance (priority := 50) BundleCalculus.instContinuousSqrtOfCStarAlgebra
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    ContinuousSqrt A
```

`ContinuousMap.instStarOrderedRing` derives `StarOrderedRing C(α, R)` from
`ContinuousSqrt R`, and Mathlib instantiates `ContinuousSqrt` for `ℝ`, `ℝ≥0` and
`ℂ` only.  But every ordered C*-algebra has one: `ContinuousSqrt` asks for a
continuous `s` with `b = a + s*s` on `{a ≤ b}`, and `s = CFC.sqrt (b - a)` is
one — `CFC.sqrt_nonneg`, `CFC.sqrt_mul_sqrt_self`, and continuity on the positive
cone from `CFC.continuousOn_sqrt`
(`Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Isometric.lean`).
Low priority, so `instContinuousSqrtRCLike` keeps precedence on the scalar
fields.

**To use it**: `import GroupApproximation.AlgTop.BundleCalculusTransport` and
`open scoped ComplexOrder`.  The `ComplexOrder` line is not optional — without
it the missing `PartialOrder ℂ` surfaces much later as a missing
`StarOrderedRing`, which is a confusing place to start debugging.

`CStarMatrix ι ι C(X, ℂ)` — the space on the inside — is the other spelling and
needs no extra instance; `CStarMat n A` in
`Analysis/CStarMatrixBlockInclusion.lean` is the campaign's name for it.  Either
works.  Two facts about `CStarMatrix` worth knowing before you fight them:

* its order is the **spectral** order (`CStarAlgebra.spectralOrder`, a `def`
  promoted to an instance).  Spend it by naming lemmas, not by rewriting it into
  the entrywise order.
* its topology **is** the product topology — `CStarMatrix.ofMatrixL` is a
  continuous linear equivalence with `continuous_toFun := continuous_id`.  So
  continuity of a map *into* `CStarMatrix` is entrywise continuity, and never
  needs a norm estimate.

## 3. What this lane adds: unitary conjugacy and homotopy invariance

Module: `GroupApproximation/AlgTop/BundleCalculusProjection.lean`
Namespace: `GroupApproximation.BundleCalculus`

```lean
/-- Stronger than Murray–von Neumann equivalence, and what the analysis produces. -/
def UnitaryConj [Monoid R] [StarMul R] (p q : R) : Prop :=
  ∃ u ∈ unitary R, u * p * star u = q

UnitaryConj.refl / .symm / .trans
UnitaryConj.map                     -- along a unital star hom (BundleCalculusTransport)
UnitaryConj.murrayVonNeumannEquiv (hp : IsStarProjection p) :
  UnitaryConj p q → MurrayVonNeumannEquiv p q
```

In a unital C*-algebra with `[CStarAlgebra A] [PartialOrder A]
[StarOrderedRing A]` (Mathlib's own idiom, as in
`Mathlib/Analysis/CStarAlgebra/Projection.lean`):

```lean
/-- Close projections are unitarily conjugate. -/
theorem unitaryConj_of_norm_sub_lt_one {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    UnitaryConj p q

theorem murrayVonNeumannEquiv_of_norm_sub_lt_one   -- same hypotheses

/-- A continuous family of projections over a preconnected space is constant
up to unitary conjugation. -/
theorem unitaryConj_of_preconnected {Y : Type*} [TopologicalSpace Y]
    [PreconnectedSpace Y] {f : Y → A} (hf : Continuous f)
    (hproj : ∀ y, IsStarProjection (f y)) (y₀ y₁ : Y) :
    UnitaryConj (f y₀) (f y₁)

theorem unitaryConj_of_isPreconnected {Y : Type*} [TopologicalSpace Y]
    {s : Set Y} (hs : IsPreconnected s) {f : Y → A} (hf : Continuous f)
    (hproj : ∀ y, IsStarProjection (f y)) {y₀ y₁ : Y} (h₀ : y₀ ∈ s) (h₁ : y₁ ∈ s) :
    UnitaryConj (f y₀) (f y₁)

theorem unitaryConj_of_path {f : ℝ → A} (hf : Continuous f)
    (hproj : ∀ t : ℝ, IsStarProjection (f t)) : UnitaryConj (f 0) (f 1)

theorem murrayVonNeumannEquiv_of_path   -- same hypotheses
```

and, with the instance ladder of §2 discharged, the same three specialised to
`C(X, CStarMatrix ι ι ℂ)`: `unitaryConj_of_path_sectionAlgebra`,
`murrayVonNeumannEquiv_of_path_sectionAlgebra`,
`unitaryConj_of_isPreconnected_sectionAlgebra`.

**The index space is a parameter, not `[0,1]`.**  That is the design decision to
take away from this note.  `s := Set.Icc 0 1` is homotopy invariance; `s := X`
is "a projection over a connected base has constant rank"; a contractible base
gives triviality.  Three lanes were each about to reprove one of those.

### How the proof goes, so you can predict what generalises

For `‖p - q‖ < 1` put `z = q p + (1 - q)(1 - p)`.  Then `z p = q z = q p`, and
`p² = p`, `q² = q` give `z* z = z z* = 1 - (p - q)²`.  So `z` is normal, that
element is positive, and `‖(p - q)²‖ ≤ ‖p - q‖² < 1` makes it a unit.  The polar
part `u = z · a^(-1/2)` (`CFC.rpow`) is unitary, and since `a^(-1/2)` is a
continuous function of `a` it inherits `a`'s commutation with `p` — `(p - q)²`
commutes with `p` — turning `z p = q z` into `u p = q u`.

Globally: `{y | UnitaryConj (f y₀) (f y)}` and its complement are both open,
each being a union of balls on which the local step applies.  Nonempty clopen in
a preconnected space is everything.  **No subdivision, no uniform continuity, no
compactness of the index space** — which is why the theorem holds over an
arbitrary unital C*-algebra and an arbitrary preconnected index space.

## 4. Landing next in this lane — ask before duplicating

* **pullback** along `f : C(X, Z)`, from `ContinuousMap.compStarAlgHom'`;
  well definedness on classes is `MurrayVonNeumannEquiv.map` / `UnitaryConj.map`,
  since a pullback is a unital star homomorphism.
* **rank** `x ↦ trace (P x)` as a continuous `X → ℤ`; locally constant; constant
  on connected `X`; additive on `blockSum`, multiplicative on Kronecker.
* **nowhere-vanishing section** ↔ `E ≅ E' ⊕ 1`, phrased with `blockSum` from
  `KTheory/MatrixProjection.lean` (for `found-euler-class` and the
  `CommonZeroProperty` work).
* **clutching**: `lix-clutching` owns the C*-side.  What is missing everywhere is
  the glueing itself — a projection over `X = X₀ ∪ X₁` from a unitary on the
  overlap.  One construction in the campaign, not two.

Direct sum, padding and reindexing are **already done** in
`KTheory/MatrixProjection.lean`; do not rebuild them.

---

## 5. Later modules (all committed, none verified as of this writing)

`GroupApproximation/AlgTop/BundleCalculusPullback.lean`

```lean
noncomputable def pullback (f : C(X, Z)) :
  C(Z, CStarMatrix ι ι ℂ) →⋆ₐ[ℂ] C(X, CStarMatrix ι ι ℂ)   -- = compStarAlgHom'
pullback_id / pullback_comp / isStarProjection_pullback
murrayVonNeumannEquiv_pullback / unitaryConj_pullback
unitaryConj_pullback_of_homotopy      (H : ContinuousMap.Homotopy f₀ f₁)
murrayVonNeumannEquiv_pullback_of_homotopy / _of_homotopic
```

Pullback is precomposition, so it is a `StarAlgHom` for free and well definedness
on classes is `MurrayVonNeumannEquiv.map`.  Only the base `X` needs compactness;
the target `Z` needs none.

`GroupApproximation/AlgTop/BundleCalculusInvariant.lean`

```lean
eq_of_unitaryConj (τ : A → B)
  (hτ : ∀ u ∈ unitary A, ∀ a, τ (u * a * star u) = τ a) : UnitaryConj p q → τ p = τ q
isLocallyConstant_of_unitaryInvariant / eq_of_preconnected / eq_of_isPreconnected
trace_isometry_conj (hu : star u * u = 1) : trace (u * a * star u) = trace a
rankAt / isLocallyConstant_rankAt / rankAt_eq_of_preconnectedSpace
```

Homotopy invariance of *every* unitary invariant at once, rather than one proof
per invariant.  Rank is the case `τ = Matrix.trace`; note that neither
continuity of the trace nor its integrality is used — the ball where two
projections are within distance `1` does the job.

`GroupApproximation/AlgTop/BundleCalculusModelBridge.lean`

```lean
noncomputable def matrixSectionEquiv :
  Matrix ι ι C(X, ℂ) ≃⋆ₐ[ℂ] C(X, CStarMatrix ι ι ℂ)
toSection / ofSection (+ `@[simp]` apply lemmas, both round trips)
isStarProjection_toSection / _ofSection
murrayVonNeumannEquiv_toSection / _ofSection, unitaryConj_toSection / _ofSection
murrayVonNeumannEquiv_of_path_block   -- analytic hypothesis, algebraic conclusion
```

The join between the two models.  Needs no compactness; only multiplicativity is
non-definitional.

`GroupApproximation/AlgTop/BundleCalculusUnitSection.lean` — for
`found-euler-class`, over a commutative star ring `R` (take `R = C(X, ℂ)`):

```lean
def rankOneProj (ξ : ι → R) := Matrix.vecMulVec ξ (star ξ)
structure IsUnitSection (P) (ξ) : Prop   -- mulVec_eq, sum_star_mul_self
def perp (P) (ξ) := P - rankOneProj ξ
isStarProjection_rankOneProj / isStarProjection_perp
perp_add_rankOneProj / perp_mul_rankOneProj / rankOneProj_mul_perp
murrayVonNeumannEquiv_rankOneProj_single (i₀ : ι)
```

Stated **unstably**, inside `M_ι(R)`: `P = perp P ξ + rankOneProj ξ` with the two
pieces orthogonal and the second equivalent to a matrix unit.  The blockSum
phrasing `MurrayVonNeumannEquiv P (blockSum P' 1)` is the wrong statement — the
sides live in different algebras, and stabilising is exactly what destroys the
obstruction target 3 turns on.

Still to come: `exists_isUnitSection_of_nowhere_zero` (normalisation, the one
lemma needing `[CompactSpace X]`), and the clutching construction, which is
blocked on `lix-clutching` naming the type of its overlap datum.
