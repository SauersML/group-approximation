# cs-simplicity

Owns `Analysis/CStarSimple.lean`, `Analysis/LIXSimplicity.lean`,
`Analysis/LIXSimplicityInstance*.lean`.

## 1. GREEN

| module | job count |
|---|---|
| `Analysis/CStarSimple` | 2961 (built together with the other two) |
| `Analysis/LIXSimplicity` | 2961 |
| `Analysis/LIXSimplicityInstance` | 2988 (after adding the tower bridge; re-probed clean) |

All three probed together via `ccprobe.sh cs-simplicity Analysis.CStarSimple
Analysis.LIXSimplicity Analysis.LIXSimplicityInstance`, `Build completed successfully`, no
warnings, no `sorry`/`axiom`/`admit`/`opaque`.

## 2. What is delivered

* `Analysis/CStarSimple.lean` — `IsSimpleCStar (A : Type u) [CStarAlgebra A]`
  (`∀ I : Ideal A, I.IsTwoSided → IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤`, no order, no
  `Nontrivial`, universe-polymorphic — this is the exact definition `cs-endpoint` asked for),
  `IsSimpleCStar.eq_bot_or_eq_top`, `IsSimpleCStar.eq_top_of_mem`, `IsSimpleCStar.of_starAlgEquiv`,
  `isSimpleCStar_iff_isSimpleRing`, `isTwoSided_closure` (closure of a two-sided ideal of a
  topological ring is two-sided — `Ideal.closure` only proves the left-ideal half).
* `Analysis/LIXSimplicity.lean` — the positive-cutdown argument, off the unavailable
  C⋆-quotient (see TRAPS 1 below, unchanged from the previous session): `posCut`, `sqrtPosCut`,
  `resCut`, `invCut`; `cfc_mem_of_isClosed`; `IsFull`, `IsFullIn`, `IsFullIn.isFull`,
  `isFullIn_of_sum_eq_one`, `isFull_of_sum_eq_one`, `one_mem_of_isFull`; `mem_of_mul_self_le`
  (closed two-sided ideals are hereditary); `exists_ge_nonneg_mem_approx`;
  `exists_ge_mem_ideal_of_nonneg`; `eq_top_of_stagewise_full`; `isSimpleCStar_of_stagewise_full`.
* `Analysis/LIXSimplicityInstance.lean` — the packaging layer, now **two** layers deep:
  * `StagewiseFullTower A` / `StagewiseFullTower.isSimpleCStar` — the bundled hypothesis
    (stages, closedness, monotonicity, density, stagewise fullness) and its simplicity theorem,
    as before.
  * `isFullIn_of_isFull_map`, `isClosed_range` — transport of fullness and closedness along a
    ⋆-homomorphism, as before.
  * **New this session**: `nonneg_iff_of_injective` — an injective unital ⋆-homomorphism of
    C⋆-algebras reflects positivity, for *any* compatible `StarOrderedRing` structure on either
    side. Proved by chaining `StarOrderedRing.nonneg_iff_spectrum_nonneg` (valid for any such
    order — the C⋆-order is unique) with `IsSelfAdjoint.map_spectrum_real` (spectral permanence
    of an injective ⋆-hom, `Mathlib.Analysis.CStarAlgebra.Hom`) both ways. Mathlib does not yet
    have this fact (its own `Unitization.inr_le_iff` carries a `-- TODO: prove the more general
    result for star monomorphisms and use it here`), so this is new content, not a citation.
  * **New this session**: `CStarTower.stagewiseFullTower` / `CStarTower.isSimpleCStar_limit` —
    the *concrete* bridge from `Analysis/LIXLimitTower`'s/`Analysis/LIXLimitCompletion`'s
    `CStarTower A` (cs-limit's structure, green, see NEEDS below for the exact names) to
    `IsSimpleCStar T.Limit`, given fullness stated **entirely inside the finite stages**, with
    the finite stages' own order: `∀ k (a : A k), 0 ≤ a → a ≠ 0 → ∃ j ≥ k, IsFull (T.climb j k
    a)`. This is exactly the shape a stage lane naturally proves (no reference to the limit's
    order or to `T.limIota` needed in the hypothesis at all — `nonneg_iff_of_injective` and
    `isFullIn_of_isFull_map` absorb all of the cross-algebra bookkeeping inside the proof).

## 3. NEEDS

Only one thing remains before the LIX-specific instantiation is one line:

### From `cs-stages` (not yet landed as of this report — no `connect`/`connect_injective`/fullness
theorem found in `Analysis/LIXStageAlgebra.lean` or `Analysis/LIXConnectingMapPoints.lean` yet)

```lean
namespace STW59
def connect (i : ℕ) : StageAlgebra i →⋆ₐ[ℂ] StageAlgebra (i + 1)
theorem connect_injective (i : ℕ) : Function.Injective (connect i)
-- and, with `T := CStarTower.ofInjective connect connect_injective`, `T.climb` as in
-- Analysis/LIXLimitTower (composite of `connect`):
theorem fullness (k : ℕ) (a : StageAlgebra k) (h0 : 0 ≤ a) (hne : a ≠ 0) :
    ∃ j, k ≤ j ∧ GroupApproximation.LIX.IsFull (T.climb j k a)
```

`0 ≤ a` under whatever `[PartialOrder (StageAlgebra k)] [StarOrderedRing (StageAlgebra k)]`
instance the stage lane installs — `nonneg_iff_of_injective` makes the choice irrelevant, as
long as it is a genuine `StarOrderedRing` (the order is then forced to be the spectral one,
Mathlib's `CStarAlgebra.instNonnegSpectrumClass'` holds for any such instance). `IsFull` needs
no order at all.

Once `connect`/`connect_injective`/`fullness` exist, the whole instantiation is:

```lean
def STW59.tower : LIX.CStarTower STW59.StageAlgebra :=
  LIX.CStarTower.ofInjective STW59.connect STW59.connect_injective

theorem STW59.isSimpleCStar : LIX.IsSimpleCStar STW59.tower.Limit :=
  STW59.tower.isSimpleCStar_limit STW59.fullness
  -- needs `[Nontrivial STW59.tower.Limit]`, free from `[Nontrivial (StageAlgebra 0)]`
  -- via `CStarTower.instNontrivialLimit` (cs-limit, already green).
```

(cs-endpoint should confirm `STW59.tower.Limit` is the same limit algebra `cs-limit`'s
`T.exists_unitary_witness` is stated about — from `cs-limit`'s report it is, since both consume
the same `CStarTower.ofInjective STW59.connect STW59.connect_injective`.)

### cs-limit's actual interface (corrected from my earlier speculative names — read directly
from `Analysis/LIXLimitTower.lean`/`Analysis/LIXLimitCompletion.lean`, both green)

```lean
structure CStarTower (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]
CStarTower.ofInjective : (∀ n, A n →⋆ₐ[ℂ] A (n+1)) → (∀ n, Injective (φ n)) → CStarTower A
T.climb (i k : ℕ) : A k → A i                    -- total, junk 0 when k > i
T.Limit                                           -- := UniformSpace.Completion T.Colim
T.limIota (i : ℕ) : A i →⋆ₐ[ℂ] T.Limit           -- isometric, injective
T.limIota_climb (h : k ≤ i) : T.limIota i (T.climb i k a) = T.limIota k a
T.stage (i : ℕ) : StarSubalgebra ℂ T.Limit        -- = (T.limIota i).range
T.mem_stage_iff, T.limIota_mem_stage, T.isClosed_stage, T.stage_mono, T.dense_iUnion_stage
```

My earlier `LIXLimit`/`lixStage`/`lixStage_full` names in this file were placeholders written
before cs-limit's actual module existed; the NEEDS section above replaces them with the real
interface. `cs-limit` did **not** register a competing `PartialOrder`/`StarOrderedRing` instance
on `T.Limit` (checked: `LIXLimitCompletion.lean` has none), so installing
`CStarAlgebra.spectralOrder T.Limit` / `CStarAlgebra.spectralOrderedRing T.Limit` locally at the
instantiation site is safe.

## 4. TRAPS

1. **The manuscript's quotient route is unavailable in this repo** (unchanged from last report):
   `Analysis/CStarIdealQuotient`'s C⋆-identity for the quotient norm is not proved, so there is
   no CFC on `B ⧸ I`. Replaced by an argument that never leaves `B`: `d (a - ε) d = c c` with
   `d = cfc (√ ∘ (·-ε)₊) a`, then `c c ≤ d b d ∈ I`, then heredity of closed two-sided ideals
   (`mem_of_mul_self_le`).
2. **Heredity without an approximate unit** (unchanged): `0 ≤ s`, `s s ≤ v ∈ I ⟹ s ∈ I` via the
   resolvent `r_δ = δ (v + δ)⁻¹` written as a functional calculus of `v`.
3. **`Ideal.closure` is only a left ideal in Mathlib** (unchanged): `I.closure.IsTwoSided` needs
   `mulRight_continuous` supplied by hand.
4. **`NonUnitalStarAlgHom.isometry`/`.norm_map` live in `Mathlib.Analysis.CStarAlgebra.Hom`**,
   which is only `public import`ed by the umbrella `Mathlib.lean`, *not* transitively reachable
   through the `ContinuousFunctionalCalculus.{Order,Isometric,Unique}` imports
   `Analysis/LIXSimplicity` already carries. A file that wants it (e.g. for
   `isClosed_range`/`nonneg_iff_of_injective`) must `import Mathlib.Analysis.CStarAlgebra.Hom`
   explicitly — the "Unknown constant" error this produces gives no hint that the fix is an
   import, since the name really does exist at the pin.
5. **A `def` returning a `structure` whose field is `noncomputable` must itself be
   `noncomputable`**, even though the `def` itself does no computation — `stage := T.stage`
   inside a `where`-block silently makes the whole definition depend on the noncomputable
   `CStarTower.stage`.  Ordinary "consider marking it as `noncomputable`" error, easy fix.
6. **Mathlib does not yet have "injective ⋆-monomorphism is an order embedding for the spectral
   order"** — confirmed absent (only a `TODO` comment on the unitization-inclusion special case
   in `Unitization.lean`'s `inr_le_iff`) — so `nonneg_iff_of_injective` had to be proved from
   scratch. It goes through cleanly in eight lines once phrased via
   `StarOrderedRing.nonneg_iff_spectrum_nonneg` (works for *any* compatible order, since a
   C⋆-algebra's order is pinned) plus `IsSelfAdjoint.map_spectrum_real`; no CFC-of-CFC or
   sum-of-squares reasoning needed.
