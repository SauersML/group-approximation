import GroupApproximation.Analysis.LIXSimplicity

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

Everything here is about an arbitrary C⋆-algebra; the LIX tower is named only in the docstrings.
The instantiation at the limit algebra is one application of `StagewiseFullTower.isSimpleCStar`
and lands as soon as the limit and stage lanes are green.

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

end LIX

end GroupApproximation
