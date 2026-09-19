import GroupApproximation.AlgTop.BundleCalculusTransport

/-!
# Bundle calculus V: the two ambient models are one algebra

The campaign runs two spellings of "matrix-valued function on `X`", and both are
load-bearing:

* `Matrix ι ι C(X, ℂ)` -- the space on the **inside**.  This is where
  `KTheory/MatrixProjection.lean` and `KTheory/Functorial.lean` live: block
  sums, padding, reindexing and `K₀` itself, all stated over a bare
  `[NonUnitalSemiring A] [StarRing A]`.  There is no norm on `Matrix` at the
  Mathlib pin, so this model **cannot** host the continuous functional calculus,
  and therefore cannot reach homotopy invariance -- but nothing in the block
  calculus wants an analytic hypothesis, and re-deriving that calculus under one
  would be strictly worse.
* `C(X, CStarMatrix ι ι ℂ)` -- the space on the **outside**.  This is
  `Analysis/LIXCornerAlgebra.lean`'s `SectionAlgebra`, and it is a genuine
  C*-algebra, so it carries the corners, the CFC, and
  `BundleCalculusProjection`'s homotopy invariance.  Moving `K₀` here would be a
  rewrite of everything `KTheory/` already has.

Each model carries the half it is good at.  What was missing is the one object
that lets them talk, and it is this file:

    matrixSectionEquiv : Matrix ι ι C(X, ℂ) ≃⋆ₐ[ℂ] C(X, CStarMatrix ι ι ℂ)

reading a matrix of functions as a function to matrices.  Since it is a star
algebra equivalence, `MurrayVonNeumannEquiv.map` and `UnitaryConj.map` transport
along it in one line in each direction: a `K₀` class computed in the first model
inherits homotopy invariance proved in the second, and a projection understood
analytically in the second acquires the block calculus of the first.

Two things worth noticing about the hypotheses.  The equivalence needs **no
compactness of `X`** -- compactness enters only when one wants the sup norm, and
nothing here does -- and it is **order-free**: the ring, star and algebra
structures on `CStarMatrix` are `inferInstanceAs` copies of `Matrix`'s, so only
the topology on `CStarMatrix ι ι ℂ` (which comes from its norm, hence from
`ComplexOrder`) is involved at all.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace BundleCalculus

open scoped ComplexOrder

section Bridge

variable {X : Type*} [TopologicalSpace X]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluating a finite sum of continuous functions is summing the values.  Used
only to push evaluation through `Matrix.mul_apply`; proved by induction rather
than through a bundled evaluation homomorphism so that it depends on nothing but
`ContinuousMap.zero_apply` and `ContinuousMap.add_apply`. -/
theorem continuousMap_sum_apply {ι' : Type*} (s : Finset ι') (f : ι' → C(X, ℂ)) (x : X) :
    (∑ k ∈ s, f k) x = ∑ k ∈ s, f k x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ContinuousMap.add_apply, ih]

/-- A matrix of continuous functions, read as a continuous matrix-valued
function.  Continuity is entrywise because the topology on `CStarMatrix` *is*
the product topology -- `CStarMatrix.ofMatrixL` is a continuous linear
equivalence whose forward map is `continuous_id`. -/
def toSection (M : Matrix ι ι C(X, ℂ)) : C(X, CStarMatrix ι ι ℂ) where
  toFun x := fun i j => M i j x
  continuous_toFun :=
    continuous_pi fun i => continuous_pi fun j => map_continuous (M i j)

@[simp]
theorem toSection_apply (M : Matrix ι ι C(X, ℂ)) (x : X) (i j : ι) :
    toSection M x i j = M i j x := rfl

/-- A continuous matrix-valued function, read as a matrix of continuous
functions. -/
def ofSection (P : C(X, CStarMatrix ι ι ℂ)) : Matrix ι ι C(X, ℂ) := fun i j =>
  ⟨fun x => P x i j,
    (continuous_apply j).comp ((continuous_apply i).comp (map_continuous P))⟩

@[simp]
theorem ofSection_apply (P : C(X, CStarMatrix ι ι ℂ)) (i j : ι) (x : X) :
    ofSection P i j x = P x i j := rfl

theorem ofSection_toSection (M : Matrix ι ι C(X, ℂ)) : ofSection (toSection M) = M := by
  ext i j x
  rfl

theorem toSection_ofSection (P : C(X, CStarMatrix ι ι ℂ)) : toSection (ofSection P) = P := by
  ext x i j
  rfl

theorem toSection_add (M N : Matrix ι ι C(X, ℂ)) :
    toSection (M + N) = toSection M + toSection N := by
  ext x i j
  rfl

theorem toSection_star (M : Matrix ι ι C(X, ℂ)) :
    toSection (star M) = star (toSection M) := by
  ext x i j
  rfl

theorem toSection_smul (c : ℂ) (M : Matrix ι ι C(X, ℂ)) :
    toSection (c • M) = c • toSection M := by
  ext x i j
  rfl

theorem toSection_one : toSection (1 : Matrix ι ι C(X, ℂ)) = 1 := by
  ext x i j
  rw [toSection_apply]
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply_eq, CStarMatrix.one_apply_eq]
  · simp [Matrix.one_apply_ne h, CStarMatrix.one_apply_ne h]

/-- Multiplicativity is the only field that is not definitional: it is
`Matrix.mul_apply` on both sides with evaluation pushed through the sum. -/
theorem toSection_mul (M N : Matrix ι ι C(X, ℂ)) :
    toSection (M * N) = toSection M * toSection N := by
  ext x i j
  simp only [toSection_apply, Matrix.mul_apply, continuousMap_sum_apply,
    ContinuousMap.mul_apply, CStarMatrix.mul_apply]

/-- **The two ambient models are the same star algebra.**  A matrix of functions
is a function to matrices, and the identification respects everything: sums,
products, adjoints and scalars.  Transport `MurrayVonNeumannEquiv` along it with
`MurrayVonNeumannEquiv.map` and `UnitaryConj` with `UnitaryConj.map`. -/
noncomputable def matrixSectionEquiv :
    Matrix ι ι C(X, ℂ) ≃⋆ₐ[ℂ] C(X, CStarMatrix ι ι ℂ) where
  toFun := toSection
  invFun := ofSection
  left_inv := ofSection_toSection
  right_inv := toSection_ofSection
  map_add' := toSection_add
  map_mul' := toSection_mul
  map_star' := toSection_star
  map_smul' := toSection_smul

@[simp]
theorem matrixSectionEquiv_apply (M : Matrix ι ι C(X, ℂ)) :
    matrixSectionEquiv M = toSection M := rfl

@[simp]
theorem matrixSectionEquiv_symm_apply (P : C(X, CStarMatrix ι ι ℂ)) :
    (matrixSectionEquiv (X := X) (ι := ι)).symm P = ofSection P := rfl

end Bridge

section Transfer

variable {X : Type*} [TopologicalSpace X]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A projection in the block-calculus model is a projection in the analytic
model. -/
theorem isStarProjection_toSection {P : Matrix ι ι C(X, ℂ)} (hP : IsStarProjection P) :
    IsStarProjection (toSection P) :=
  hP.map (matrixSectionEquiv (X := X) (ι := ι))

theorem isStarProjection_ofSection {P : C(X, CStarMatrix ι ι ℂ)} (hP : IsStarProjection P) :
    IsStarProjection (ofSection P) :=
  hP.map (matrixSectionEquiv (X := X) (ι := ι)).symm

/-- **Bundle isomorphism crosses the bridge.**  This is the lemma that lets a
`K₀` computation in `Matrix ι ι C(X, ℂ)` be compared with an analytic argument
in `C(X, CStarMatrix ι ι ℂ)`. -/
theorem murrayVonNeumannEquiv_toSection {P Q : Matrix ι ι C(X, ℂ)}
    (h : MurrayVonNeumannEquiv P Q) :
    MurrayVonNeumannEquiv (toSection P) (toSection Q) :=
  h.map (matrixSectionEquiv (X := X) (ι := ι))

theorem murrayVonNeumannEquiv_ofSection {P Q : C(X, CStarMatrix ι ι ℂ)}
    (h : MurrayVonNeumannEquiv P Q) :
    MurrayVonNeumannEquiv (ofSection P) (ofSection Q) :=
  h.map (matrixSectionEquiv (X := X) (ι := ι)).symm

theorem unitaryConj_toSection {P Q : Matrix ι ι C(X, ℂ)} (h : UnitaryConj P Q) :
    UnitaryConj (toSection P) (toSection Q) :=
  h.map (matrixSectionEquiv (X := X) (ι := ι))

theorem unitaryConj_ofSection {P Q : C(X, CStarMatrix ι ι ℂ)} (h : UnitaryConj P Q) :
    UnitaryConj (ofSection P) (ofSection Q) :=
  h.map (matrixSectionEquiv (X := X) (ι := ι)).symm

end Transfer

section HomotopyInBlockModel

open scoped ComplexOrder

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Homotopy invariance, imported into the block-calculus model.**  A
continuous path of projections in `Matrix ι ι C(X, ℂ)` -- continuity measured
after crossing the bridge, since that model has no norm of its own -- has
Murray-von Neumann equivalent ends.

This is the join the campaign was missing: the hypothesis is analytic and lives
in the second model, the conclusion is algebraic and lives in the first. -/
theorem murrayVonNeumannEquiv_of_path_block {P : ℝ → Matrix ι ι C(X, ℂ)}
    (hP : Continuous fun t => toSection (P t))
    (hproj : ∀ t : ℝ, IsStarProjection (P t)) :
    MurrayVonNeumannEquiv (P 0) (P 1) := by
  have h : MurrayVonNeumannEquiv (toSection (P 0)) (toSection (P 1)) :=
    murrayVonNeumannEquiv_of_path hP fun t => isStarProjection_toSection (hproj t)
  have h' := murrayVonNeumannEquiv_ofSection h
  rwa [ofSection_toSection, ofSection_toSection] at h'

end HomotopyInBlockModel

end BundleCalculus
end GroupApproximation
