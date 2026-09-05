# Bundle calculus: the shared API (lane `found-bundle-calculus`, 2026-09-05)

Consumers: `found-chern-classes`, `found-ktheory-bott`, `found-euler-class`,
`found-mapping-torus-parity`, `lix-spaces`, `lix-clutching`, `lix-obstruction`.

Code against the signatures below rather than inventing your own projection
vocabulary.  Everything here is Mathlib-pin-checked at `81a5d257`
(toolchain v4.32.0).

---

## 1. Pick the right ambient algebra: `CStarMatrix n n C(X, ℂ)`

There are two plausible spellings of "matrix-valued function on `X`" and only
one of them carries the instances the analysis needs.

| spelling | `CStarAlgebra` | `PartialOrder` | `StarOrderedRing` |
|---|---|---|---|
| `Matrix (Fin N) (Fin N) C(X,ℂ)` | no norm at all | — | — |
| `C(X, CStarMatrix (Fin N) (Fin N) ℂ)` | yes | no | **no** |
| `CStarMatrix (Fin N) (Fin N) C(X,ℂ)` | yes | yes | **yes** |

`Matrix` has no C*-norm in Mathlib (its `NormedRing` instances are the sup and
Frobenius norms, and they are scoped).  `C(α, A)` gets `StarOrderedRing` only
through `ContinuousMap.instStarOrderedRing`, which needs `ContinuousSqrt A`, and
that class is instantiated for `ℝ`, `ℝ≥0`, `ℂ` and nothing else — so
`C(X, CStarMatrix n n ℂ)` is a dead end for every order-dependent argument,
which means for every CFC argument, which means for homotopy invariance.

**So: put the space on the inside.**

```lean
open scoped ComplexOrder     -- supplies `PartialOrder ℂ`

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] {N : ℕ}

abbrev BundleAlg (X : Type*) [TopologicalSpace X] [CompactSpace X] (N : ℕ) :=
  CStarMatrix (Fin N) (Fin N) C(X, ℂ)
```

The instance ladder that then fires, in order:

1. `PartialOrder ℂ` — scoped, from `open scoped ComplexOrder`.  **Without this
   line nothing below resolves**, and the failure looks like a missing
   `StarOrderedRing`, not like a missing order on `ℂ`.
2. `ContinuousMap.partialOrder : PartialOrder C(X, ℂ)` (pointwise).
3. `ContinuousMap.instStarOrderedRing : StarOrderedRing C(X, ℂ)` — via
   `ContinuousSqrt ℂ`.
4. `ContinuousMap.instCommCStarAlgebra : CommCStarAlgebra C(X, ℂ)` — needs
   `[CompactSpace X]`.  `T2Space` is *not* required.
5. `CStarMatrix.instCStarAlgebra`, `CStarMatrix.instPartialOrder`
   (`= CStarAlgebra.spectralOrder _`), `CStarMatrix.instStarOrderedRing`.

Two traps worth knowing before you hit them:

* the `CStarMatrix` order is the **spectral order**, a `def` promoted to an
  instance.  Spend it by naming lemmas about it; do not try to rewrite it into
  the entrywise order.
* the topology on `CStarMatrix m n A` is the product topology —
  `CStarMatrix.ofMatrixL` is a continuous linear equivalence with
  `continuous_toFun := continuous_id`.  So continuity of a map *into*
  `CStarMatrix` is entrywise continuity, and you never need a norm estimate for
  it.

## 2. Bundle = projection, isomorphism = Murray–von Neumann

Module: `GroupApproximation/AlgTop/BundleCalculusProjection.lean`
Namespace: `GroupApproximation.BundleCalculus`

Use Mathlib's `IsStarProjection` — do not roll your own.

```lean
structure IsStarProjection [Mul R] [Star R] (p : R) : Prop where
  isIdempotentElem : IsIdempotentElem p     -- `.eq : p * p = p`
  isSelfAdjoint : IsSelfAdjoint p           -- `.star_eq : star p = p`
```

Both fields are `protected`, so reach them by dot notation, and remember that
`IsIdempotentElem` is a plain `def`: `rw` needs `hp.isIdempotentElem.eq`, while
`have h : p * p = p := hp.isIdempotentElem` is fine.

The two equivalence notions:

```lean
/-- Murray–von Neumann equivalence.  This is bundle isomorphism. -/
def MvNEquiv {R : Type*} [Mul R] [Star R] (p q : R) : Prop :=
  ∃ v : R, star v * v = p ∧ v * star v = q

/-- Unitary conjugacy.  Stronger, and what the analysis actually produces. -/
def UnitaryConj {R : Type*} [Monoid R] [StarMul R] (p q : R) : Prop :=
  ∃ u ∈ unitary R, u * p * star u = q
```

Groupoid lemmas (`R` a monoid with `StarMul`):

```lean
UnitaryConj.refl  (p : R) : UnitaryConj p p
UnitaryConj.symm  : UnitaryConj p q → UnitaryConj q p
UnitaryConj.trans : UnitaryConj p q → UnitaryConj q r → UnitaryConj p r
UnitaryConj.mvNEquiv (hp : IsStarProjection p) : UnitaryConj p q → MvNEquiv p q

MvNEquiv.refl  (hp : IsStarProjection p) : MvNEquiv p p
MvNEquiv.symm  : MvNEquiv p q → MvNEquiv q p
MvNEquiv.trans (hp : IsStarProjection p) (hr : IsStarProjection r) :
  MvNEquiv p q → MvNEquiv q r → MvNEquiv p r
```

`MvNEquiv.trans` genuinely needs the two projection hypotheses: for a general
`v` the element `star v * v` need not be idempotent, so the composite partial
isometry has to be recognised using `p * p = p`.

## 3. Homotopy invariance — the theorem the whole layer rests on

In a unital C*-algebra `A` with `[CStarAlgebra A] [PartialOrder A]
[StarOrderedRing A]` (exactly Mathlib's own idiom in
`Mathlib/Analysis/CStarAlgebra/Projection.lean`):

```lean
/-- Close projections are unitarily conjugate. -/
theorem unitaryConj_of_norm_sub_lt_one {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    UnitaryConj p q

theorem mvNEquiv_of_norm_sub_lt_one {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    MvNEquiv p q

/-- A continuous family of projections indexed by a preconnected space is
constant up to unitary conjugation. -/
theorem unitaryConj_of_preconnected {Y : Type*} [TopologicalSpace Y]
    [PreconnectedSpace Y] {f : Y → A} (hf : Continuous f)
    (hproj : ∀ y, IsStarProjection (f y)) (y₀ y₁ : Y) :
    UnitaryConj (f y₀) (f y₁)

theorem unitaryConj_of_isPreconnected {Y : Type*} [TopologicalSpace Y]
    {s : Set Y} (hs : IsPreconnected s) {f : Y → A} (hf : Continuous f)
    (hproj : ∀ y, IsStarProjection (f y)) {y₀ y₁ : Y} (h₀ : y₀ ∈ s) (h₁ : y₁ ∈ s) :
    UnitaryConj (f y₀) (f y₁)

/-- Endpoints of a continuous path of projections. -/
theorem unitaryConj_of_path {f : ℝ → A} (hf : Continuous f)
    (hproj : ∀ t : ℝ, IsStarProjection (f t)) : UnitaryConj (f 0) (f 1)

theorem mvNEquiv_of_path {f : ℝ → A} (hf : Continuous f)
    (hproj : ∀ t : ℝ, IsStarProjection (f t)) : MvNEquiv (f 0) (f 1)
```

The index space is a *parameter*, not `[0,1]` baked in.  Take
`unitaryConj_of_isPreconnected` with `s := Set.Icc 0 1` for a homotopy, but take
it with `s := X` when you want "a projection over a connected `X` has constant
rank" or "over a contractible base every projection is trivial".

Note what is **not** assumed: `A` is any unital C*-algebra.  Compactness of `X`
enters only through the instance ladder of §1, and the theorem never sees it.

### How the proof goes, so you can predict what generalises

For `‖p - q‖ < 1` put `z = q p + (1 - q)(1 - p)`.  Then `z p = q z = q p`, and
`p² = p`, `q² = q` give `z* z = z z* = 1 - (p - q)²`.  So `z` is normal, that
element is positive, and `‖(p - q)²‖ ≤ ‖p - q‖² < 1` makes it a unit.  The polar
part `u = z · a^(-1/2)` (`CFC.rpow`) is unitary, and since `a^(-1/2)` is a
continuous function of `a` it inherits `a`'s commutation with `p` — `(p - q)²`
commutes with `p` — turning `z p = q z` into `u p = q u`.

Globally: `{y | UnitaryConj (f y₀) (f y)}` and its complement are both open,
because each is a union of the balls on which the local step applies.  Nonempty
clopen in a preconnected space is everything.  **No subdivision, no uniform
continuity, no compactness of the index space.**

## 4. Landing next (do not duplicate — ask me)

Same lane, module `GroupApproximation/AlgTop/BundleCalculusMatrixModel.lean`:

* **pullback** `f^* : BundleAlg Z N → BundleAlg X N` along `f : C(X, Z)`,
  entrywise `ContinuousMap.compStarAlgHom'`; respects `MvNEquiv` because it is a
  star algebra hom, and *every* star algebra hom does (`IsStarProjection.map`).
* **direct sum** (block diagonal, `N + M`), **tensor** (Kronecker, `N * M`),
  **trivial bundle** `1^n`, **dual** (transpose composed with entrywise
  conjugation).
* **rank** `x ↦ trace (P x)` as a continuous `X → ℤ`; locally constant; constant
  on connected `X`; additive on `⊕`, multiplicative on `⊗`.
* **complement** `P ⊕ (1 - P) = 1^N`.
* **nowhere-vanishing section** ↔ `E ≅ E' ⊕ 1` (for `found-euler-class` and the
  `CommonZeroProperty` work).
* **clutching**: `lix-clutching` owns the C*-side in
  `GroupApproximation/Analysis/LIXClutching.lean`; I supply the bundle-side
  lemmas.  One construction in the campaign, not two — coordinate before writing
  a second one.

Rank, additivity and the pullback are all pure algebra plus §3 and should be
cheap.  The *only* place where a genuinely new analytic idea is needed is
cancellation (target 3), and there the honest statement is that cancellation
fails; state carefully, prove only the stable-range direction.
