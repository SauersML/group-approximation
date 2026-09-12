import GroupApproximation.Analysis.LIXSimplicity
import GroupApproximation.Analysis.LIXLimitCompletion
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# The simplicity input of the LIX tower, bundled

`Analysis/LIXSimplicity` proves that a unital C⋆-algebra which is the closure of an increasing
union of closed ⋆-subalgebras, each of whose nonzero positive elements becomes full in a later
one, is simple.  This module packages that hypothesis as a single structure and adds the two
transport lemmas an inductive limit needs to build it, so that the LIX limit algebra can hand
over its data in one term.

## Contents

* `StagewiseFullTower A` — the bundled hypothesis: the stages, their closedness, monotonicity,
  density of the union, and stagewise fullness.
* `StagewiseFullTower.isSimpleCStar` — `IsSimpleCStar A` from it.  The conclusion mentions no
  order instance, so it is directly the endpoint's `IsSimpleCStar`.
* `isFullIn_of_isFull_map` — fullness travels along a unital ⋆-homomorphism into a subalgebra
  containing its image.  This is how a stage of the tower delivers fullness: the stage lane
  proves `φ_{k,i+1}(a)` full in the finite-stage algebra `A_{i+1}`, and this lemma moves that
  statement into the limit along `ι_{i+1}`.
* `isClosed_range` — the range of an injective ⋆-homomorphism of C⋆-algebras is closed, because
  such a map is isometric.  This is how the limit lane gets `IsClosed (stage i)`.
* `nonneg_iff_of_injective` — an injective unital ⋆-homomorphism of C⋆-algebras reflects
  positivity.  This is what lets a fullness hypothesis phrased with the *finite stage's own*
  order (the natural place for the stage lane to prove it) drive `StagewiseFullTower`'s
  hypothesis, phrased with the *limit's* order.
* `CStarTower.stagewiseFullTower` — the concrete bridge from `Analysis/LIXLimitTower`'s
  `CStarTower A` (an abstract tower of C⋆-algebras with its algebraic colimit and completion) to
  `StagewiseFullTower T.Limit`, given fullness stated entirely inside the finite stages: for
  `0 ≤ a` in `A k`, `a ≠ 0`, some later `T.climb j k a` is full in `A j`.  This is exactly the
  shape the stage lane's tower-specific theorem takes, so the LIX instantiation reduces to
  `(CStarTower.ofInjective STW59.connect STW59.connect_injective).stagewiseFullTower hfull`.

Everything here is about an arbitrary C⋆-algebra; the LIX tower is named only in the docstrings.
The instantiation at the limit algebra is one application of `CStarTower.stagewiseFullTower`
followed by `StagewiseFullTower.isSimpleCStar`, and lands as soon as the stage lane's fullness
theorem is stated in the form above.

## Manuscript status

Interface for Lemma 5 of
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`; certifies no
manuscript step on its own.
-/

namespace GroupApproximation

namespace LIX

universe u v

/-! ### Transport along a ⋆-homomorphism -/

section Transport

variable {A : Type u} {C : Type v} [CStarAlgebra A] [CStarAlgebra C]

/-- **Fullness travels along a unital ⋆-homomorphism.**  If `a` is full in `C` and every value of
`f` lies in the subalgebra `T`, then `f a` is full in `T`: apply `f` to the finite sums, which it
preserves, and use that a ⋆-homomorphism of C⋆-algebras is contractive. -/
theorem isFullIn_of_isFull_map (f : C →⋆ₐ[ℂ] A) {T : StarSubalgebra ℂ A}
    (hT : ∀ c : C, f c ∈ T) {a : C} (h : IsFull a) : IsFullIn T (f a) := by
  intro ε hε
  obtain ⟨n, x, y, hxy⟩ := h ε hε
  refine ⟨n, fun i => f (x i), fun i => f (y i), fun i => hT _, fun i => hT _, ?_⟩
  have hmap : (1 : A) - ∑ i, f (x i) * f a * f (y i) = f (1 - ∑ i, x i * a * y i) := by
    rw [map_sub, map_one, map_sum]
    simp only [map_mul]
  rw [hmap]
  exact lt_of_le_of_lt (NonUnitalStarAlgHom.norm_apply_le f _) hxy

/-- **The range of an injective ⋆-homomorphism of C⋆-algebras is closed.**  Such a map is
isometric, so it is a closed embedding of a complete space. -/
theorem isClosed_range (f : C →⋆ₐ[ℂ] A) (hf : Function.Injective f) :
    IsClosed ((f.range : StarSubalgebra ℂ A) : Set A) := by
  have hiso : Isometry (f : C → A) := NonUnitalStarAlgHom.isometry f hf
  have hcoe : ((f.range : StarSubalgebra ℂ A) : Set A) = Set.range (f : C → A) := rfl
  rw [hcoe]
  exact hiso.isClosedEmbedding.isClosed_range

end Transport

section OrderTransport

variable {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder C] [StarOrderedRing C]

/-- **An injective unital ⋆-homomorphism of C⋆-algebras reflects positivity.**

Positivity of a self-adjoint element under *any* compatible `StarOrderedRing` structure on a
C⋆-algebra is exactly nonnegativity of its real spectrum
(`StarOrderedRing.nonneg_iff_spectrum_nonneg`, which needs no more than `NonnegSpectrumClass`,
itself automatic for any such order — this is the statement that the C⋆-order is unique).  An
injective ⋆-homomorphism preserves the real spectrum of a self-adjoint element
(`IsSelfAdjoint.map_spectrum_real`).  Chaining the two both ways gives the "iff": no
order-theoretic content beyond spectral permanence is needed, and in particular this holds no
matter which of the (unique) compatible orders is installed on `A` and on `C`. -/
theorem nonneg_iff_of_injective (f : C →⋆ₐ[ℂ] A) (hf : Function.Injective f) (a : C) :
    0 ≤ f a ↔ 0 ≤ a := by
  constructor
  · intro h
    have hsaA : IsSelfAdjoint (f a) := .of_nonneg h
    have hsaC : IsSelfAdjoint a := hf (by rw [map_star]; exact hsaA.star_eq)
    rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) (a := f a) hsaA,
      hsaC.map_spectrum_real f hf] at h
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) (a := a) hsaC).mpr h
  · intro h
    have hsaC : IsSelfAdjoint a := .of_nonneg h
    have hsaA : IsSelfAdjoint (f a) := hsaC.map f
    rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) (a := a) hsaC] at h
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) (a := f a) hsaA).mpr
      (hsaC.map_spectrum_real f hf ▸ h)

end OrderTransport

/-! ### The bundled hypothesis -/

/-- **The data a stagewise-full tower supplies.**

`stage i` is the image of the `i`-th finite stage in the limit, as a closed ⋆-subalgebra; the
stages increase, their union is dense, and every nonzero positive element of a stage becomes full
in some later stage.  For the LIX tower `stage i = (ι i).range`, `isClosed_stage` is
`isClosed_range` and `full_stage` is `isFullIn_of_isFull_map` applied to the fullness of the
point-evaluation summand.

The order instances are those of the ambient algebra; the conclusion of
`StagewiseFullTower.isSimpleCStar` mentions none, so the endpoint can install
`CStarAlgebra.spectralOrder` locally and still get its order-free `IsSimpleCStar`. -/
structure StagewiseFullTower (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] where
  /-- The stages, as closed unital ⋆-subalgebras of the limit. -/
  stage : ℕ → StarSubalgebra ℂ A
  /-- Each stage is closed, which is what makes it a C⋆-algebra in its own right. -/
  isClosed_stage : ∀ i, IsClosed (stage i : Set A)
  /-- The stages increase. -/
  mono_stage : Monotone stage
  /-- Their union is dense: the algebra is the closure of the union of its stages. -/
  dense_stage : Dense (⋃ i, (stage i : Set A))
  /-- Every nonzero positive element of a stage becomes full in a later stage. -/
  full_stage : ∀ (k : ℕ) (a : A), a ∈ stage k → 0 ≤ a → a ≠ 0 →
    ∃ j, k ≤ j ∧ IsFullIn (stage j) a

/-- **A stagewise-full tower has a simple limit.**  This is `isSimpleCStar_of_stagewise_full` with
the hypotheses read off the structure. -/
theorem StagewiseFullTower.isSimpleCStar {A : Type u} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Nontrivial A] (T : StagewiseFullTower A) : IsSimpleCStar A :=
  isSimpleCStar_of_stagewise_full T.isClosed_stage T.mono_stage T.dense_stage T.full_stage

/-! ### The concrete bridge from a tower -/

/-- **A stagewise-full tower, assembled from a `CStarTower` plus fullness in the finite stages.**

`Analysis/LIXLimitTower`/`Analysis/LIXLimitCompletion` build, from a tower `T : CStarTower A` of
unital C⋆-algebras, the limit `T.Limit` with stages `T.stage i := (T.limIota i).range`, already
closed, increasing, with dense union.  What remains to invoke `StagewiseFullTower.isSimpleCStar`
is fullness, and the hypothesis below asks for it in the cheapest form a stage lane can supply:
entirely inside the finite stages, with the finite stages' own order.

Given a positive nonzero element `x` of the `k`-th stage, `x = T.limIota k a` for a unique
`a : A k` (`T.mem_stage_iff`); `nonneg_iff_of_injective` transports positivity of `x` back to `a`
(`T.limIota k` is injective, being isometric), and injectivity transports `x ≠ 0` to `a ≠ 0`.
The hypothesis then gives fullness of `T.climb j k a` inside `A j`; pushing it forward along
`T.limIota j` (`isFullIn_of_isFull_map`, using that `T.stage j` is literally the range of
`T.limIota j`) and rewriting `T.limIota j (T.climb j k a) = T.limIota k a = x`
(`T.limIota_climb`) gives fullness of `x` itself. -/
noncomputable def CStarTower.stagewiseFullTower {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]
    [∀ n, PartialOrder (A n)] [∀ n, StarOrderedRing (A n)]
    (T : CStarTower A) [PartialOrder T.Limit] [StarOrderedRing T.Limit]
    (hfull : ∀ (k : ℕ) (a : A k), 0 ≤ a → a ≠ 0 →
      ∃ j, k ≤ j ∧ IsFull (T.climb j k a)) :
    StagewiseFullTower T.Limit where
  stage := T.stage
  isClosed_stage := T.isClosed_stage
  mono_stage := T.stage_mono
  dense_stage := T.dense_iUnion_stage
  full_stage := by
    intro k x hxk hx0 hxne
    obtain ⟨a, rfl⟩ := T.mem_stage_iff.mp hxk
    have ha0 : 0 ≤ a := (nonneg_iff_of_injective (T.limIota k) (T.limIota_injective k) a).mp hx0
    have hane : a ≠ 0 := by
      intro h
      apply hxne
      rw [h, map_zero]
    obtain ⟨j, hkj, hfullj⟩ := hfull k a ha0 hane
    refine ⟨j, hkj, ?_⟩
    have hpush := isFullIn_of_isFull_map (T.limIota j) (fun c => T.limIota_mem_stage j c) hfullj
    rwa [T.limIota_climb hkj] at hpush

/-- **`IsSimpleCStar` for the limit of a tower whose finite stages are eventually full.**  The
composition of `CStarTower.stagewiseFullTower` and `StagewiseFullTower.isSimpleCStar`, in the
form the LIX endpoint consumes directly from a stage lane's tower and fullness theorem. -/
theorem CStarTower.isSimpleCStar_limit {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]
    [∀ n, PartialOrder (A n)] [∀ n, StarOrderedRing (A n)]
    (T : CStarTower A) [PartialOrder T.Limit] [StarOrderedRing T.Limit] [Nontrivial T.Limit]
    (hfull : ∀ (k : ℕ) (a : A k), 0 ≤ a → a ≠ 0 →
      ∃ j, k ≤ j ∧ IsFull (T.climb j k a)) :
    IsSimpleCStar T.Limit :=
  (T.stagewiseFullTower hfull).isSimpleCStar

/-! ### The positivity-free variant

A tower whose fullness argument does not use positivity — the LIX tower is one, since a section
nonzero in every fibre generates the whole corner whether or not it is positive — can supply the
hypothesis for *every* nonzero element of a stage.  That is a stronger hypothesis, so the
theorem below is formally weaker than `isSimpleCStar_limit`; what it buys is that the finite
stages then need no order at all.  `nonneg_iff_of_injective` was the only reason
`stagewiseFullTower` asked for `[∀ n, PartialOrder (A n)] [∀ n, StarOrderedRing (A n)]`, and with
positivity gone there is nothing to transport, so a stage lane using this entry point never has
to install an order on its stages.

Both entry points are kept.  `isSimpleCStar_limit` demands less of the tower and is the right
default; this one demands less of the *ambient setup*. -/

/-- `StagewiseFullTower` from fullness of every nonzero element of a stage, with no order on the
stages.  See the section note for why both this and `stagewiseFullTower` exist. -/
noncomputable def CStarTower.stagewiseFullTowerOfNeZero {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]
    (T : CStarTower A) [PartialOrder T.Limit] [StarOrderedRing T.Limit]
    (hfull : ∀ (k : ℕ) (a : A k), a ≠ 0 → ∃ j, k ≤ j ∧ IsFull (T.climb j k a)) :
    StagewiseFullTower T.Limit where
  stage := T.stage
  isClosed_stage := T.isClosed_stage
  mono_stage := T.stage_mono
  dense_stage := T.dense_iUnion_stage
  full_stage := by
    intro k x hxk _ hxne
    obtain ⟨a, rfl⟩ := T.mem_stage_iff.mp hxk
    have hane : a ≠ 0 := by
      intro h
      apply hxne
      rw [h, map_zero]
    obtain ⟨j, hkj, hfullj⟩ := hfull k a hane
    refine ⟨j, hkj, ?_⟩
    have hpush := isFullIn_of_isFull_map (T.limIota j) (fun c => T.limIota_mem_stage j c) hfullj
    rwa [T.limIota_climb hkj] at hpush

/-- **`IsSimpleCStar` for the limit, from fullness of every nonzero element of a stage.**  The
positivity-free entry point: the finite stages carry no order. -/
theorem CStarTower.isSimpleCStar_limit_of_ne_zero {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]
    (T : CStarTower A) [PartialOrder T.Limit] [StarOrderedRing T.Limit] [Nontrivial T.Limit]
    (hfull : ∀ (k : ℕ) (a : A k), a ≠ 0 → ∃ j, k ≤ j ∧ IsFull (T.climb j k a)) :
    IsSimpleCStar T.Limit :=
  (T.stagewiseFullTowerOfNeZero hfull).isSimpleCStar

end LIX

end GroupApproximation
