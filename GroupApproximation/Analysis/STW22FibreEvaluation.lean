import GroupApproximation.Analysis.AntipodalHomogeneousBlock
import Mathlib.Topology.UrysohnsLemma

/-!
# The fibres of the antipodal block are full matrix algebras

The STW Problem XXII audit says of its homogeneous blocks:

> Every fibre of `D_s` is `M_(s+1)`.

With the concrete model of `Analysis/AntipodalHomogeneousBlock` — antipodally
covariant matrix functions on `S^d`, i.e. the fixed-point algebra of
`f ↦ (y ↦ u · f(-y) · u)` — that sentence becomes a provable statement about
evaluation homomorphisms, and this file proves it:

* `blockEval d s u _ _ x` is the `⋆`-algebra map "evaluate at `x`";
* `blockEval_surjective` — each one is **onto** `M_(s+1)`, so the fibres really
  are full matrix algebras;
* `blockEval_eq_zero_iff` — the family is **jointly faithful**;
* `blockEval_neg` — `eval (-x) = u · eval x · u`, so the fibres are indexed by
  `RP^d` rather than by `S^d`.

## Why surjectivity is the interesting clause

It is where the involution is spent.  A point of a sphere is never its own
antipode (`sphere_neg_ne_self`), so Urysohn separates `{x}` from `{-x}`: pick `φ`
vanishing at `-x` and equal to one at `x`, and set

```text
f y = φ y • m + φ (-y) • (u * m * u).
```

Then `f (-y) = u * f y * u` — the check consumes `u * u = 1` exactly once, in
`u * (u * m * u) * u = m` — and `f x = m`.  So every matrix is hit.

## What is *not* proved here, and why

`FibreEvaluationClassification` states that every irreducible representation is
`(s+1)`-dimensional and onto, i.e. that the fibre evaluations above are *all* of
them.  That is a genuine classical theorem — Dixmier, *C\*-algebras*, §4.7 (see
also Fell, *The structure of algebras of operator fields*) — and it is carried
here as a named hypothesis rather than proved, because its standard proof needs
Schur's lemma for C⋆-representations, which needs spectral projections of a
self-adjoint element of the commutant, i.e. **Borel** functional calculus.
Mathlib has only the continuous functional calculus, and none of the usual
substitutes (double commutant, Kadison transitivity, Amitsur–Levitzki plus
Kaplansky) are available either.  This is the one honestly-named gap; note the
audit's headline discontinuity theorem does not consume it — it only qualifies
the counterexample's class.

The Prop spells irreducibility out inline rather than reusing
`IsIrreducibleRep`/`IsHomogeneousRep`, so that it elaborates without a
`CStarAlgebra` instance on the block; the block is a `StarSubalgebra`, which
already carries the ring, algebra and star structure the statement needs.
-/

namespace GroupApproximation
namespace STW22

open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

open scoped CStarAlgebra Matrix

set_option linter.unusedSectionVars false

noncomputable section

/-! ## Evaluation homomorphisms -/

/-- Evaluation at a point of the sphere, as a `⋆`-algebra homomorphism. -/
def sphereEval (d s : ℕ) (x : Sphere d) :
    SphereMatrixFunctions d s →⋆ₐ[ℂ] CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ where
  toFun f := f x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
theorem sphereEval_apply (d s : ℕ) (x : Sphere d) (f : SphereMatrixFunctions d s) :
    sphereEval d s x f = f x := rfl

/-- Evaluation of an antipodally covariant matrix function at a point of the
sphere — the fibre map of the block. -/
def blockEval (d s : ℕ) (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u) (x : Sphere d) :
    AntipodalBlock d s u hu_sq hu_star →⋆ₐ[ℂ] CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ :=
  (sphereEval d s x).comp (antipodalBlockStarSubalgebra d s u hu_sq hu_star).subtype

@[simp]
theorem blockEval_apply (d s : ℕ) (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u) (x : Sphere d)
    (F : AntipodalBlock d s u hu_sq hu_star) :
    blockEval d s u hu_sq hu_star x F = (F : SphereMatrixFunctions d s) x := rfl

/-- **The fibres are indexed by `RP^d`.**  Antipodal points give conjugate
evaluations. -/
theorem blockEval_neg (d s : ℕ) (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u) (x : Sphere d)
    (F : AntipodalBlock d s u hu_sq hu_star) :
    blockEval d s u hu_sq hu_star (-x) F
      = u * blockEval d s u hu_sq hu_star x F * u :=
  F.2 x

/-- **Joint faithfulness.**  The fibre evaluations separate the block. -/
theorem blockEval_eq_zero_iff (d s : ℕ) (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u)
    (F : AntipodalBlock d s u hu_sq hu_star) :
    (∀ x : Sphere d, blockEval d s u hu_sq hu_star x F = 0) ↔ F = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    exact h x
  · rintro rfl x
    exact map_zero _

/-! ## Surjectivity of the fibre maps -/

/-- A point of a sphere is never its own antipode. -/
theorem sphere_neg_ne_self {d : ℕ} (x : Sphere d) : (-x : Sphere d) ≠ x := by
  intro h
  have hcoe : -(x : EuclideanSpace ℝ (Fin (d + 1))) = (x : EuclideanSpace ℝ (Fin (d + 1))) :=
    congrArg Subtype.val h
  have hnorm : ‖(x : EuclideanSpace ℝ (Fin (d + 1)))‖ = 1 := by
    have hmem := x.2
    rw [Metric.mem_sphere, dist_zero_right] at hmem
    exact hmem
  have hsum : (x : EuclideanSpace ℝ (Fin (d + 1))) + (x : EuclideanSpace ℝ (Fin (d + 1))) = 0 := by
    nth_rewrite 1 [← hcoe]
    simp
  have hzero : ((2 : ℝ) • (x : EuclideanSpace ℝ (Fin (d + 1)))) = 0 := by
    rw [two_smul]
    exact hsum
  have h2 : (2 : ℝ) * ‖(x : EuclideanSpace ℝ (Fin (d + 1)))‖ = 0 := by
    calc (2 : ℝ) * ‖(x : EuclideanSpace ℝ (Fin (d + 1)))‖
        = ‖((2 : ℝ) • (x : EuclideanSpace ℝ (Fin (d + 1))))‖ := by
          rw [norm_smul]
          simp
      _ = 0 := by rw [hzero, norm_zero]
  rw [hnorm, mul_one] at h2
  norm_num at h2

/-- **The fibres are full matrix algebras.**  Every matrix is the value at `x`
of an antipodally covariant function.  The witness is
`y ↦ φ y • m + φ (-y) • (u * m * u)` for a Urysohn bump `φ` separating `x` from
`-x`; covariance is exactly where `u * u = 1` is used. -/
theorem blockEval_surjective (d s : ℕ) (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u) (x : Sphere d) :
    Function.Surjective (blockEval d s u hu_sq hu_star x) := by
  intro m
  obtain ⟨φ, hφ0, hφ1, -⟩ :=
    exists_continuous_zero_one_of_isClosed
      (X := Sphere d) (s := ({-x} : Set (Sphere d))) (t := ({x} : Set (Sphere d)))
      isClosed_singleton isClosed_singleton
      (by simpa [Set.disjoint_singleton] using sphere_neg_ne_self x)
  have hφx : φ x = 1 := by simpa using hφ1 (Set.mem_singleton x)
  have hφnx : φ (-x) = 0 := by simpa using hφ0 (Set.mem_singleton (-x))
  have hconj : u * (u * m * u) * u = m := by
    calc u * (u * m * u) * u = u * u * m * (u * u) := by noncomm_ring
      _ = m := by rw [hu_sq]; simp
  have hcont : Continuous
      (fun y : Sphere d => (φ y : ℂ) • m + (φ (-y) : ℂ) • (u * m * u)) := by
    have h1 : Continuous (fun y : Sphere d => ((φ y : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp φ.continuous
    have h2 : Continuous (fun y : Sphere d => ((φ (-y) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (φ.continuous.comp continuous_neg)
    exact (h1.smul continuous_const).add (h2.smul continuous_const)
  refine ⟨⟨⟨fun y => (φ y : ℂ) • m + (φ (-y) : ℂ) • (u * m * u), hcont⟩, ?_⟩, ?_⟩
  · intro y
    show (φ (-y) : ℂ) • m + (φ (-(-y)) : ℂ) • (u * m * u)
      = u * ((φ y : ℂ) • m + (φ (-y) : ℂ) • (u * m * u)) * u
    rw [neg_neg]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hconj]
    exact add_comm _ _
  · show (φ x : ℂ) • m + (φ (-x) : ℂ) • (u * m * u) = m
    rw [hφx, hφnx]
    simp

/-! ## The classical classification input -/

/-- **Named classical input — Dixmier, *C\*-algebras*, §4.7 (cf. Fell).**  Every
irreducible representation of the antipodal block is `(s+1)`-dimensional and
onto; equivalently, the fibre evaluations of `blockEval` are, up to unitary
equivalence, *all* the irreducible representations.

This is not proved here.  Its standard proof needs Schur's lemma for
C⋆-representations, hence spectral projections, hence Borel functional calculus,
which Mathlib does not have; see the module docstring for the alternatives that
were checked and are also unavailable.  `blockEval_surjective` and
`blockEval_eq_zero_iff` supply the concrete half — that the evaluations really
are surjective and jointly faithful — which is the sentence the audit itself
asserts. -/
def FibreEvaluationClassification (d s : ℕ)
    (u : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (hu_sq : u * u = 1) (hu_star : star u = u) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : AntipodalBlock d s u hu_sq hu_star →⋆ₐ[ℂ] (H →L[ℂ] H)),
      (∃ a : AntipodalBlock d s u hu_sq hu_star, π a ≠ 0) →
      (∀ M : Submodule ℂ H, IsClosed (M : Set H) →
          (∀ a : AntipodalBlock d s u hu_sq hu_star, ∀ v ∈ M, π a v ∈ M) →
          M = ⊥ ∨ M = ⊤) →
        Module.finrank ℂ H = s + 1 ∧
          Function.Surjective (π : AntipodalBlock d s u hu_sq hu_star → (H →L[ℂ] H))

/-- The concrete `s`-th block of the counterexample has surjective, jointly
faithful fibre evaluations indexed by `RP^d`. -/
theorem realProjectiveBlock_fibres (d s : ℕ) (x : Sphere d) :
    Function.Surjective (blockEval d s (blockInvolution s) (blockInvolution_sq s)
      (blockInvolution_star s) x) :=
  blockEval_surjective d s (blockInvolution s) (blockInvolution_sq s) (blockInvolution_star s) x

end

end STW22
end GroupApproximation
