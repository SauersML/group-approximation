import GroupApproximation.Analysis.LIXBlockProjections
import GroupApproximation.Analysis.LIXCornerAlgebra
import GroupApproximation.Analysis.LIXConnectingMapPoints

set_option autoImplicit false

/-!
# The stage algebras `A_i` of the STW LIX tower

The manuscript's (4.1) sets `A_i = Γ(X_i, End E_i)`, and `Analysis/LIXCornerAlgebra.lean`
turns that into a definition: the section algebra of the endomorphism bundle of the
bundle presented by a projection `p` **is** the corner `p M_ι(C(X)) p`.  This file
instantiates that with the block projections of `Analysis/LIXBlockProjections.lean`:

* `STW59.stageProj i : SectionAlgebra (baseX i) (EIdx i)` is `E_i` in the C-star picture
  `C(X_i, CStarMatrix (EIdx i) (EIdx i) ℂ)`;
* `STW59.StageAlgebra i` is the corner it cuts out, a **unital C-star algebra with unit
  `E_i`** (`STW59.instCStarAlgebraStageAlgebra` is Mathlib's instance ladder, checked
  here by `example`);
* `STW59.stageEval i w a : Matrix (EIdx i) (EIdx i) ℂ` is the value of the section `a` in
  the fibre over `w ∈ X_i`; it is a `*`-homomorphism onto the fibre corner, and a section
  is zero exactly when every one of its values is (`STW59.stageAlgebra_eq_zero_iff`).

Everything here is bookkeeping; the mathematics is in `LIXBlockProjections` (the
projections) and `LIXCornerAlgebra` (the C-star structure).

## The `Matrix ι ι C(X, ℂ)` ↔ `C(X, CStarMatrix ι ι ℂ)` dictionary

`LIXBlockProjections` builds projections as matrices of continuous functions, because
that picture makes block assembly free; the C-star instances live on the other picture.
`STW59.ofFunctionMatrix` (in `LIXCornerAlgebra`) goes one way; `STW59.toFunctionMatrix`
here goes back, and the two are mutually inverse `*`-isomorphisms.  The topology of
`CStarMatrix` is `inferInstanceAs` the entrywise one
(`Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean`, `instUniformSpace`), so the inverse
needs no estimate.
-/

namespace GroupApproximation
namespace STW59

open scoped Matrix ComplexOrder CStarAlgebra

noncomputable section

/-! ### The inverse of the bridge -/

section Bridge

variable {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluation of a section of the ambient homogeneous algebra in the fibre over a point.
`CStarMatrix ι ι ℂ` is a type synonym for `Matrix ι ι ℂ` whose algebraic instances are
transported along the identity, so every compatibility below is `rfl`. -/
def sectionEval (w : X) (a : SectionAlgebra X ι) : Matrix ι ι ℂ := a w

@[simp]
theorem sectionEval_apply (w : X) (a : SectionAlgebra X ι) (s t : ι) :
    sectionEval w a s t = a w s t := rfl

theorem sectionEval_mul (w : X) (a b : SectionAlgebra X ι) :
    sectionEval w (a * b) = sectionEval w a * sectionEval w b := rfl

theorem sectionEval_add (w : X) (a b : SectionAlgebra X ι) :
    sectionEval w (a + b) = sectionEval w a + sectionEval w b := rfl

theorem sectionEval_star (w : X) (a : SectionAlgebra X ι) :
    sectionEval w (star a) = (sectionEval w a)ᴴ := rfl

theorem sectionEval_zero (w : X) : sectionEval w (0 : SectionAlgebra X ι) = 0 := rfl

theorem sectionEval_smul (w : X) (c : ℂ) (a : SectionAlgebra X ι) :
    sectionEval w (c • a) = c • sectionEval w a := rfl

@[simp]
theorem sectionEval_ofFunctionMatrix (w : X) (M : Matrix ι ι C(X, ℂ)) :
    sectionEval w (ofFunctionMatrix M) = matEval w M := rfl

theorem sectionAlgebra_ext {a b : SectionAlgebra X ι}
    (h : ∀ w, sectionEval w a = sectionEval w b) : a = b :=
  ContinuousMap.ext fun w => CStarMatrix.ext fun s t =>
    congrFun (congrFun (h w) s) t

theorem sectionAlgebra_eq_zero_iff {a : SectionAlgebra X ι} :
    a = 0 ↔ ∀ w, sectionEval w a = 0 := by
  constructor
  · intro h w
    rw [h, sectionEval_zero]
  · intro h
    exact sectionAlgebra_ext fun w => by rw [h w, sectionEval_zero]

/-- A section, read back as a matrix of continuous scalar functions.  Inverse to
`STW59.ofFunctionMatrix`. -/
def toFunctionMatrix (a : SectionAlgebra X ι) : Matrix ι ι C(X, ℂ) :=
  Matrix.of fun s t => ⟨fun w => a w s t, a.continuous.matrix_elem s t⟩

@[simp]
theorem toFunctionMatrix_apply (a : SectionAlgebra X ι) (s t : ι) (w : X) :
    toFunctionMatrix a s t w = a w s t := rfl

@[simp]
theorem matEval_toFunctionMatrix (a : SectionAlgebra X ι) (w : X) :
    matEval w (toFunctionMatrix a) = sectionEval w a := rfl

@[simp]
theorem toFunctionMatrix_ofFunctionMatrix (M : Matrix ι ι C(X, ℂ)) :
    toFunctionMatrix (ofFunctionMatrix M) = M := rfl

@[simp]
theorem ofFunctionMatrix_toFunctionMatrix (a : SectionAlgebra X ι) :
    ofFunctionMatrix (toFunctionMatrix a) = a := rfl

theorem toFunctionMatrix_injective :
    Function.Injective (toFunctionMatrix : SectionAlgebra X ι → Matrix ι ι C(X, ℂ)) := by
  intro a b h
  rw [← ofFunctionMatrix_toFunctionMatrix a, ← ofFunctionMatrix_toFunctionMatrix b, h]

theorem toFunctionMatrix_add (a b : SectionAlgebra X ι) :
    toFunctionMatrix (a + b) = toFunctionMatrix a + toFunctionMatrix b := by
  apply ofFunctionMatrix_injective
  rw [ofFunctionMatrix_toFunctionMatrix, ofFunctionMatrix_add, ofFunctionMatrix_toFunctionMatrix,
    ofFunctionMatrix_toFunctionMatrix]

theorem toFunctionMatrix_mul (a b : SectionAlgebra X ι) :
    toFunctionMatrix (a * b) = toFunctionMatrix a * toFunctionMatrix b := by
  apply ofFunctionMatrix_injective
  rw [ofFunctionMatrix_toFunctionMatrix, ofFunctionMatrix_mul, ofFunctionMatrix_toFunctionMatrix,
    ofFunctionMatrix_toFunctionMatrix]

theorem toFunctionMatrix_star (a : SectionAlgebra X ι) :
    toFunctionMatrix (star a) = star (toFunctionMatrix a) := by
  apply ofFunctionMatrix_injective
  rw [ofFunctionMatrix_toFunctionMatrix, ofFunctionMatrix_star, ofFunctionMatrix_toFunctionMatrix]

theorem toFunctionMatrix_smul (c : ℂ) (a : SectionAlgebra X ι) :
    toFunctionMatrix (c • a) = c • toFunctionMatrix a := by
  apply ofFunctionMatrix_injective
  rw [ofFunctionMatrix_toFunctionMatrix, ofFunctionMatrix_smul, ofFunctionMatrix_toFunctionMatrix]

end Bridge

/-! ### The stage algebras, generic in the rank `n` -/

namespace Gen

/-- `E_i` as a projection of the ambient homogeneous algebra `M_{E_i}(C(X_i))`. -/
def stageProj (n i : ℕ) : SectionAlgebra (baseX n i) (EIdx n i) :=
  ofFunctionMatrix (Eproj n i)

theorem isStarProjection_stageProj (n i : ℕ) : IsStarProjection (stageProj n i) :=
  isStarProjection_ofFunctionMatrix (isStarProjection_Eproj n i)

@[simp]
theorem sectionEval_stageProj (n i : ℕ) (w : baseX n i) :
    sectionEval w (stageProj n i) = matEval w (Eproj n i) := rfl

@[simp]
theorem toFunctionMatrix_stageProj (n i : ℕ) :
    toFunctionMatrix (stageProj n i) = Eproj n i := rfl

/-- **`A_i = Γ(X_i, End E_i)`** at rank `n`, the `i`-th stage of the AH tower of the
manuscript's (4.1), as the corner `E_i · M_{E_i}(C(X_i)) · E_i`. -/
abbrev StageAlgebra (n i : ℕ) : Type :=
  Corner (stageProj n i) (isStarProjection_stageProj n i)

section Instances

example (n i : ℕ) : CStarAlgebra (StageAlgebra n i) := inferInstance

example (n i : ℕ) : Ring (StageAlgebra n i) := inferInstance

example (n i : ℕ) : StarRing (StageAlgebra n i) := inferInstance

example (n i : ℕ) : NormedAlgebra ℂ (StageAlgebra n i) := inferInstance

end Instances

/-- The unit of `A_i` is `E_i`. -/
@[simp]
theorem coe_stageAlgebra_one (n i : ℕ) :
    ((1 : StageAlgebra n i) : SectionAlgebra (baseX n i) (EIdx n i)) = stageProj n i := rfl

/-- Membership in the stage algebra, at the level of matrices of functions. -/
theorem mem_stageAlgebra_iff {n i : ℕ} {a : SectionAlgebra (baseX n i) (EIdx n i)} :
    a ∈ cornerAlgebra (stageProj n i) (isStarProjection_stageProj n i) ↔
      stageProj n i * a * stageProj n i = a := Iff.rfl

/-- Evaluation of a section of `End E_i` in the fibre over `w`. -/
def stageEval (n i : ℕ) (w : baseX n i) (a : StageAlgebra n i) :
    Matrix (EIdx n i) (EIdx n i) ℂ :=
  sectionEval w (a : SectionAlgebra (baseX n i) (EIdx n i))

theorem stageEval_mul (n i : ℕ) (w : baseX n i) (a b : StageAlgebra n i) :
    stageEval n i w (a * b) = stageEval n i w a * stageEval n i w b := rfl

theorem stageEval_add (n i : ℕ) (w : baseX n i) (a b : StageAlgebra n i) :
    stageEval n i w (a + b) = stageEval n i w a + stageEval n i w b := rfl

theorem stageEval_star (n i : ℕ) (w : baseX n i) (a : StageAlgebra n i) :
    stageEval n i w (star a) = (stageEval n i w a)ᴴ := rfl

theorem stageEval_zero (n i : ℕ) (w : baseX n i) :
    stageEval n i w (0 : StageAlgebra n i) = 0 := rfl

@[simp]
theorem stageEval_one (n i : ℕ) (w : baseX n i) :
    stageEval n i w (1 : StageAlgebra n i) = matEval w (Eproj n i) := rfl

/-- **A section of `End E_i` is zero exactly when all of its fibre values are.** -/
theorem stageAlgebra_eq_zero_iff {n i : ℕ} {a : StageAlgebra n i} :
    a = 0 ↔ ∀ w, stageEval n i w a = 0 := by
  constructor
  · intro h w
    rw [h, stageEval_zero]
  · intro h
    refine corner_ext ?_
    rw [coe_corner_zero]
    exact sectionAlgebra_eq_zero_iff.mpr h

/-- The fibre value of a section lies in the fibre corner of `E_i`. -/
theorem stageEval_mem_corner {n i : ℕ} (w : baseX n i) (a : StageAlgebra n i) :
    matEval w (Eproj n i) * stageEval n i w a * matEval w (Eproj n i) = stageEval n i w a := by
  have h := coe_corner_mem a
  have h' := congrArg (sectionEval w) h
  rw [sectionEval_mul, sectionEval_mul, sectionEval_stageProj] at h'
  exact h'

/-- The fibre rank of `E_i` is `r_i`, so a frame of the fibre has `r_i` columns. -/
theorem trace_stageEval_one (n i : ℕ) (w : baseX n i) :
    (stageEval n i w (1 : StageAlgebra n i)).trace = ((stageRank n i : ℕ) : ℂ) :=
  trace_matEval_Eproj n i w

/-- The membership condition of `StageAlgebra n i`, read back at the
`Matrix (EIdx n i) (EIdx n i) C(baseX n i, ℂ)` level. -/
theorem toFunctionMatrix_mem_corner {n i : ℕ} (a : StageAlgebra n i) :
    Eproj n i * toFunctionMatrix (a : SectionAlgebra (baseX n i) (EIdx n i)) * Eproj n i
      = toFunctionMatrix (a : SectionAlgebra (baseX n i) (EIdx n i)) := by
  have h := coe_corner_mem a
  have h' := congrArg toFunctionMatrix h
  rwa [toFunctionMatrix_mul, toFunctionMatrix_mul, toFunctionMatrix_stageProj] at h'

/-- **`A_i` is nontrivial**: its unit `E_i` is a nonzero projection (it has rank
`r_i > 0`, which is where `n ≠ 0` enters), so `1 ≠ 0` in the corner. -/
theorem stageAlgebra_one_ne_zero (n i : ℕ) [NeZero n] : (1 : StageAlgebra n i) ≠ 0 := by
  intro h
  have h' : stageEval n i (stagePoint n i) (1 : StageAlgebra n i)
      = stageEval n i (stagePoint n i) (0 : StageAlgebra n i) :=
    congrArg (stageEval n i (stagePoint n i)) h
  rw [stageEval_one, stageEval_zero] at h'
  have htrace : (matEval (stagePoint n i) (Eproj n i)).trace
      = (0 : Matrix (EIdx n i) (EIdx n i) ℂ).trace := congrArg Matrix.trace h'
  rw [trace_matEval_Eproj, Matrix.trace_zero] at htrace
  exact (Nat.cast_ne_zero.mpr (stageRank_pos n i).ne') htrace

instance instNontrivialStageAlgebra (n i : ℕ) [NeZero n] : Nontrivial (StageAlgebra n i) :=
  nontrivial_of_ne 1 0 (stageAlgebra_one_ne_zero n i)

/-- The stage algebras as a *family*: `LIX.CStarTower` binds `[∀ i, CStarAlgebra (A i)]`,
and instance search does not assemble that pi-instance from the per-stage one on its own.

This is a **data** class, so there must not be a second, independent instance at `n = 2`:
`STW59.instCStarAlgebraStageAlgebraPi` below is `fun _ => inferInstance`, which resolves
*through* this one, so the two are the same term after unfolding. -/
noncomputable instance instCStarAlgebraStageAlgebraPi (n : ℕ) :
    ∀ i : ℕ, CStarAlgebra (StageAlgebra n i) := fun _ => inferInstance

end Gen

/-! ### The `n = 2` instance -/

/-- `E_i` as a projection of the ambient homogeneous algebra `M_{E_i}(C(X_i))`. -/
abbrev stageProj (i : ℕ) : SectionAlgebra (baseX i) (EIdx i) := Gen.stageProj 2 i

theorem isStarProjection_stageProj (i : ℕ) : IsStarProjection (stageProj i) :=
  Gen.isStarProjection_stageProj 2 i

@[simp]
theorem sectionEval_stageProj (i : ℕ) (w : baseX i) :
    sectionEval w (stageProj i) = matEval w (Eproj i) := rfl

@[simp]
theorem toFunctionMatrix_stageProj (i : ℕ) : toFunctionMatrix (stageProj i) = Eproj i := rfl

/-- The defining equation of `stageProj`.  `stageProj` is now an `abbrev` for
`Gen.stageProj 2`, so `rw [stageProj]` unfolds to the generic name rather than to this
right-hand side; a consumer that wants the right-hand side must name this lemma. -/
theorem stageProj_def (i : ℕ) : stageProj i = ofFunctionMatrix (Eproj i) := rfl

/-- **`A_i = Γ(X_i, End E_i)`**, the `i`-th stage of the AH tower of the manuscript's
(4.1), as the corner `E_i · M_{E_i}(C(X_i)) · E_i`. -/
abbrev StageAlgebra (i : ℕ) : Type := Gen.StageAlgebra 2 i

section Instances

example (i : ℕ) : CStarAlgebra (StageAlgebra i) := inferInstance

example (i : ℕ) : Ring (StageAlgebra i) := inferInstance

example (i : ℕ) : StarRing (StageAlgebra i) := inferInstance

example (i : ℕ) : NormedAlgebra ℂ (StageAlgebra i) := inferInstance

end Instances

/-- The unit of `A_i` is `E_i`. -/
@[simp]
theorem coe_stageAlgebra_one (i : ℕ) :
    ((1 : StageAlgebra i) : SectionAlgebra (baseX i) (EIdx i)) = stageProj i := rfl

/-- Membership in the stage algebra, at the level of matrices of functions. -/
theorem mem_stageAlgebra_iff {i : ℕ} {a : SectionAlgebra (baseX i) (EIdx i)} :
    a ∈ cornerAlgebra (stageProj i) (isStarProjection_stageProj i) ↔
      stageProj i * a * stageProj i = a := Iff.rfl

/-- Evaluation of a section of `End E_i` in the fibre over `w`. -/
def stageEval (i : ℕ) (w : baseX i) (a : StageAlgebra i) : Matrix (EIdx i) (EIdx i) ℂ :=
  Gen.stageEval 2 i w a

/-- The defining equation of `stageEval`, for the same reason as `stageProj_def`. -/
theorem stageEval_def (i : ℕ) (w : baseX i) (a : StageAlgebra i) :
    stageEval i w a = sectionEval w (a : SectionAlgebra (baseX i) (EIdx i)) := rfl

theorem stageEval_mul (i : ℕ) (w : baseX i) (a b : StageAlgebra i) :
    stageEval i w (a * b) = stageEval i w a * stageEval i w b := rfl

theorem stageEval_add (i : ℕ) (w : baseX i) (a b : StageAlgebra i) :
    stageEval i w (a + b) = stageEval i w a + stageEval i w b := rfl

theorem stageEval_star (i : ℕ) (w : baseX i) (a : StageAlgebra i) :
    stageEval i w (star a) = (stageEval i w a)ᴴ := rfl

theorem stageEval_zero (i : ℕ) (w : baseX i) : stageEval i w (0 : StageAlgebra i) = 0 := rfl

@[simp]
theorem stageEval_one (i : ℕ) (w : baseX i) :
    stageEval i w (1 : StageAlgebra i) = matEval w (Eproj i) := rfl

/-- **A section of `End E_i` is zero exactly when all of its fibre values are.** -/
theorem stageAlgebra_eq_zero_iff {i : ℕ} {a : StageAlgebra i} :
    a = 0 ↔ ∀ w, stageEval i w a = 0 := Gen.stageAlgebra_eq_zero_iff

/-- The fibre value of a section lies in the fibre corner of `E_i`. -/
theorem stageEval_mem_corner {i : ℕ} (w : baseX i) (a : StageAlgebra i) :
    matEval w (Eproj i) * stageEval i w a * matEval w (Eproj i) = stageEval i w a :=
  Gen.stageEval_mem_corner w a

/-- The fibre rank of `E_i` is `r_i`, so a frame of the fibre has `r_i` columns. -/
theorem trace_stageEval_one (i : ℕ) (w : baseX i) :
    (stageEval i w (1 : StageAlgebra i)).trace = ((stageRank i : ℕ) : ℂ) :=
  Gen.trace_stageEval_one 2 i w

/-- The membership condition of `StageAlgebra i`, read back at the `Matrix (EIdx i) (EIdx i)
C(baseX i, ℂ)` level: `Analysis/LIXConnectingMap.lean` needs exactly this shape to check that
the connecting map lands in the next corner. -/
theorem toFunctionMatrix_mem_corner {i : ℕ} (a : StageAlgebra i) :
    Eproj i * toFunctionMatrix (a : SectionAlgebra (baseX i) (EIdx i)) * Eproj i
      = toFunctionMatrix (a : SectionAlgebra (baseX i) (EIdx i)) :=
  Gen.toFunctionMatrix_mem_corner a

/-- **`A_i` is nontrivial.** -/
theorem stageAlgebra_one_ne_zero (i : ℕ) : (1 : StageAlgebra i) ≠ 0 :=
  Gen.stageAlgebra_one_ne_zero 2 i

/-- The stage algebras as a *family*: `LIX.CStarTower` binds `[∀ n, CStarAlgebra (A n)]`, and
instance search does not assemble that pi-instance from the per-stage one on its own. -/
noncomputable instance instCStarAlgebraStageAlgebraPi :
    ∀ n : ℕ, CStarAlgebra (StageAlgebra n) := fun _ => inferInstance

end

end STW59
end GroupApproximation
