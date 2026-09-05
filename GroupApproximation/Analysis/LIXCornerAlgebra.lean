import GroupApproximation.Analysis.LIXProjectiveSpaceModel
import GroupApproximation.KTheory.MatrixProjection
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes

set_option autoImplicit false

/-!
# The corner algebra `p A p` of a projection, and the section algebras of LIX

For the STW Problem LIX counterexample
(`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`) the
building blocks of the AH system are section algebras `Γ(X, End E)` of endomorphism
bundles.  The manuscript records the fact that makes those blocks elementary: such a
block *is a full corner of a matrix algebra over the base*.  This file takes that as the
definition, so no bundle library is needed anywhere.

The corner is built **for an arbitrary unital C-star algebra `A` and a projection
`p : A`**:

  `Γ(p) := p A p = {a ∈ A | p a p = a}`   (`STW59.Corner p hp`),

a closed `*`-subalgebra of `A` which is **unital with unit `p`** (it is not a unital
subalgebra of `A`, since `1 ∉ p A p` unless `p = 1`; that is why the C-star structure is
assembled by an explicit ladder rather than by `StarSubalgebra.cstarAlgebra`).  The
ambient algebra of the LIX tower is then

  `SectionAlgebra X ι := C(X, CStarMatrix ι ι ℂ)`,

used with `X = X_i` compact and `ι = EIdx i` in `Analysis/LIXStageAlgebra.lean`.

## Design notes / repo warnings honoured

* **The corner is developed over an abstract `A`.**  An earlier version worked directly
  inside `C(X, CStarMatrix ι ι ℂ)`; there, `mul_add`, `mul_assoc` and `star_mul` all
  failed to apply, because `CStarMatrix` carries a bare `Mul` instance
  (`Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean`, `instance ... : Mul (CStarMatrix n n A)`)
  beside the one coming from its semiring structure, and `C(X, -)` propagates the
  mismatch.  Over an abstract `[CStarAlgebra A]` every instance comes from one chain and
  the lemmas apply.  The `Diagnostics` section below pins the ambient chain down.
* The non-unital half comes free from Mathlib's
  `NonUnitalStarSubalgebra.nonUnitalCStarAlgebra`, given a registered `IsClosed`
  instance.  Only the unital half — `One`, `Ring`, `NormedRing`, `Algebra ℂ` — is built
  by hand, and each link is a named instance so that nothing is left to a blind search.
* Subtypes are always written `↥`, never a term-level `↑`.
* **Murray–von Neumann equivalence is not redefined here.**  The repository already has
  `GroupApproximation.MurrayVonNeumannEquiv` with `refl`, `symm`
  (`Analysis/FiniteCStarMurrayVonNeumann.lean`), `trans` and `map`
  (`KTheory/MatrixProjection.lean`), together with `blockSum` and its compatibility
  lemmas — the repo's stand-in for "bundle isomorphism" and "direct sum of bundles".
  The one genuinely missing fact, invariance under conjugation by an isometry, is added
  here as `STW59.murrayVonNeumannEquiv_conj`.
* `STW59.ofFunctionMatrix` is the `*`-homomorphism from the "matrix over the function
  algebra" picture `Matrix ι ι C(X, ℂ)` used by `KTheory/MatrixProjection.lean` and by
  `Analysis/LIXBlockProjections.lean` into the C-star picture used here.
-/

namespace GroupApproximation
namespace STW59

open scoped Matrix ComplexOrder CStarAlgebra

noncomputable section

/-! ### Murray–von Neumann equivalence under conjugation by an isometry -/

/-- **Murray–von Neumann equivalence is preserved by conjugation by an isometry.**

If `v` implements `p ∼ q`, then `u v u*` implements `u p u* ∼ u q u*`; only
`u* u = 1` is used, so `u` need not be unitary.  This is the repo's stand-in for "a
bundle isomorphism is carried along by a change of trivialization".

This complements `MurrayVonNeumannEquiv.of_isometry_conjugate`, which is the different
statement `p ∼ u p u*`. -/
theorem murrayVonNeumannEquiv_conj {A : Type*} [Monoid A] [StarMul A] {p q u : A}
    (hu : star u * u = 1) (h : MurrayVonNeumannEquiv p q) :
    MurrayVonNeumannEquiv (u * p * star u) (u * q * star u) := by
  obtain ⟨v, hv₁, hv₂⟩ := h
  refine ⟨u * v * star u, ?_, ?_⟩
  · calc star (u * v * star u) * (u * v * star u)
        = u * (star v * (star u * u) * v) * star u := by
          rw [star_mul, star_mul, star_star]
          simp only [mul_assoc]
      _ = u * (star v * v) * star u := by rw [hu, mul_one]
      _ = u * p * star u := by rw [hv₁]
  · calc (u * v * star u) * star (u * v * star u)
        = u * (v * (star u * u) * star v) * star u := by
          rw [star_mul, star_mul, star_star]
          simp only [mul_assoc]
      _ = u * (v * star v) * star u := by rw [hu, mul_one]
      _ = u * q * star u := by rw [hv₂]

/-! ### The corner of a projection in a unital C-star algebra -/

section Corner

variable {A : Type*} [CStarAlgebra A]

/-- The underlying set of the corner `p A p`. -/
def cornerCarrier (p : A) : Set A := {a | p * a * p = a}

theorem mem_cornerCarrier {p a : A} : a ∈ cornerCarrier p ↔ p * a * p = a := Iff.rfl

/-- `p` is a left unit on its corner. -/
theorem corner_left_unit {p a : A} (hp : IsStarProjection p) (ha : p * a * p = a) :
    p * a = a := by
  calc p * a = p * (p * a * p) := by rw [ha]
    _ = (p * p) * a * p := by simp only [mul_assoc]
    _ = p * a * p := by rw [hp.isIdempotentElem.eq]
    _ = a := ha

/-- `p` is a right unit on its corner. -/
theorem corner_right_unit {p a : A} (hp : IsStarProjection p) (ha : p * a * p = a) :
    a * p = a := by
  calc a * p = (p * a * p) * p := by rw [ha]
    _ = p * a * (p * p) := by simp only [mul_assoc]
    _ = p * a * p := by rw [hp.isIdempotentElem.eq]
    _ = a := ha

/-- **The corner `Γ(p) = p A p`** as a non-unital `*`-subalgebra of `A`. -/
def cornerAlgebra (p : A) (hp : IsStarProjection p) : NonUnitalStarSubalgebra ℂ A where
  carrier := cornerCarrier p
  zero_mem' := by
    show p * 0 * p = 0
    rw [mul_zero, zero_mul]
  add_mem' := by
    intro a b ha hb
    have ha' : p * a * p = a := ha
    have hb' : p * b * p = b := hb
    show p * (a + b) * p = a + b
    rw [mul_add, add_mul, ha', hb']
  mul_mem' := by
    intro a b ha hb
    have ha' : p * a * p = a := ha
    have hb' : p * b * p = b := hb
    show p * (a * b) * p = a * b
    calc p * (a * b) * p = (p * a) * (b * p) := by simp only [mul_assoc]
      _ = a * b := by rw [corner_left_unit hp ha', corner_right_unit hp hb']
  smul_mem' := by
    intro c a ha
    have ha' : p * a * p = a := ha
    show p * (c • a) * p = c • a
    rw [mul_smul_comm, smul_mul_assoc, ha']
  star_mem' := by
    intro a ha
    have ha' : p * a * p = a := ha
    show p * star a * p = star a
    have hstar : star (p * a * p) = p * star a * p := by
      rw [star_mul, star_mul, hp.isSelfAdjoint.star_eq, mul_assoc]
    rw [← hstar, ha']

theorem mem_cornerAlgebra_iff {p : A} {hp : IsStarProjection p} {a : A} :
    a ∈ cornerAlgebra p hp ↔ p * a * p = a := Iff.rfl

/-- **`Γ(p)`**: the corner of `A` cut out by the projection `p`.

For `A = M_ι(C(X))` and `p` a projection-valued function this is the repo's stand-in for
the section algebra `Γ(X, End E)` of the endomorphism bundle of the bundle presented by
`p`. -/
abbrev Corner (p : A) (hp : IsStarProjection p) := ↥(cornerAlgebra p hp)

theorem coe_corner_mem {p : A} {hp : IsStarProjection p} (a : Corner p hp) :
    p * (a : A) * p = (a : A) := a.2

theorem self_mem_cornerAlgebra (p : A) (hp : IsStarProjection p) :
    p ∈ cornerAlgebra p hp := by
  show p * p * p = p
  rw [hp.isIdempotentElem.eq, hp.isIdempotentElem.eq]

theorem isClosed_cornerCarrier (p : A) : IsClosed (cornerCarrier p) := by
  have hcont : Continuous fun a : A => p * a * p :=
    (continuous_const.mul continuous_id).mul continuous_const
  exact isClosed_eq hcont continuous_id

instance cornerAlgebra_isClosed (p : A) (hp : IsStarProjection p) :
    IsClosed ((cornerAlgebra p hp : NonUnitalStarSubalgebra ℂ A) : Set A) :=
  isClosed_cornerCarrier p

/-! ### The unital C-star structure, built as an explicit ladder

The non-unital C-star structure is Mathlib's
`NonUnitalStarSubalgebra.nonUnitalCStarAlgebra`, available from the `IsClosed` instance
above.  Everything below adds the unit `p`. -/

instance cornerOne (p : A) (hp : IsStarProjection p) : One (Corner p hp) :=
  ⟨⟨p, self_mem_cornerAlgebra p hp⟩⟩

@[simp]
theorem coe_cornerOne (p : A) (hp : IsStarProjection p) :
    ((1 : Corner p hp) : A) = p := rfl

@[simp]
theorem coe_corner_mul (p : A) (hp : IsStarProjection p) (a b : Corner p hp) :
    ((a * b : Corner p hp) : A) = (a : A) * (b : A) := rfl

@[simp]
theorem coe_corner_add (p : A) (hp : IsStarProjection p) (a b : Corner p hp) :
    ((a + b : Corner p hp) : A) = (a : A) + (b : A) := rfl

@[simp]
theorem coe_corner_star (p : A) (hp : IsStarProjection p) (a : Corner p hp) :
    ((star a : Corner p hp) : A) = star (a : A) := rfl

@[simp]
theorem coe_corner_zero (p : A) (hp : IsStarProjection p) :
    ((0 : Corner p hp) : A) = 0 := rfl

@[simp]
theorem coe_corner_smul (p : A) (hp : IsStarProjection p) (c : ℂ) (a : Corner p hp) :
    ((c • a : Corner p hp) : A) = c • (a : A) := rfl

theorem corner_ext {p : A} {hp : IsStarProjection p} {a b : Corner p hp}
    (h : (a : A) = (b : A)) : a = b := Subtype.ext h

/-- The corner is a ring with unit `p`. -/
noncomputable instance cornerRing (p : A) (hp : IsStarProjection p) : Ring (Corner p hp) :=
  { (inferInstance : NonUnitalRing (Corner p hp)) with
    one := (1 : Corner p hp)
    one_mul := fun a => Subtype.ext
      (show p * (a : A) = (a : A) from corner_left_unit hp (mem_cornerAlgebra_iff.mp a.2))
    mul_one := fun a => Subtype.ext
      (show (a : A) * p = (a : A) from corner_right_unit hp (mem_cornerAlgebra_iff.mp a.2)) }

noncomputable instance cornerNormedRing (p : A) (hp : IsStarProjection p) :
    NormedRing (Corner p hp) :=
  { (inferInstance : NonUnitalNormedRing (Corner p hp)), (cornerRing p hp) with }

noncomputable instance cornerAlgebraInstance (p : A) (hp : IsStarProjection p) :
    Algebra ℂ (Corner p hp) where
  algebraMap :=
    { toFun := fun c => c • (1 : Corner p hp)
      map_one' := one_smul ℂ _
      map_mul' := fun c c' => by
        show (c * c') • (1 : Corner p hp)
          = (c • (1 : Corner p hp)) * (c' • (1 : Corner p hp))
        rw [smul_mul_smul_comm, mul_one]
      map_zero' := zero_smul ℂ _
      map_add' := fun c c' => add_smul c c' _ }
  commutes' := fun c a => by
    show (c • (1 : Corner p hp)) * a = a * (c • (1 : Corner p hp))
    rw [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  smul_def' := fun c a => by
    show c • a = (c • (1 : Corner p hp)) * a
    rw [smul_mul_assoc, one_mul]

noncomputable instance cornerNormedAlgebra (p : A) (hp : IsStarProjection p) :
    NormedAlgebra ℂ (Corner p hp) where
  norm_smul_le c a := norm_smul_le c a

/-- **The corner is a unital C-star algebra**, with unit `p`, in the norm inherited from
the ambient algebra. -/
noncomputable instance cornerCStarAlgebra (p : A) (hp : IsStarProjection p) :
    CStarAlgebra (Corner p hp) where

theorem corner_norm_coe (p : A) (hp : IsStarProjection p) (a : Corner p hp) :
    ‖a‖ = ‖(a : A)‖ := rfl

/-- The C-star identity in the corner. -/
theorem corner_norm_star_mul_self (p : A) (hp : IsStarProjection p) (a : Corner p hp) :
    ‖star a * a‖ = ‖a‖ * ‖a‖ :=
  CStarRing.norm_star_mul_self

theorem corner_complete (p : A) (hp : IsStarProjection p) :
    CompleteSpace (Corner p hp) := inferInstance

end Corner

/-! ### The ambient section algebra of the LIX tower -/

/-- The ambient homogeneous algebra `M_ι(C(X))`, realized as continuous matrix-valued
functions so that Mathlib's C-star instances apply directly.  It is a unital
C-star algebra whenever `X` is compact. -/
abbrev SectionAlgebra (X : Type*) [TopologicalSpace X] (ι : Type*) [Fintype ι]
    [DecidableEq ι] := C(X, CStarMatrix ι ι ℂ)

/-! ### Instance diagnostics for the ambient algebra

These `example`s pin down exactly which link of the instance chain is present at the pin;
they are cheap and are kept because the chain runs through `open scoped ComplexOrder`
(which supplies `PartialOrder ℂ` and `RCLike.toStarOrderedRing`, hence the C-star
structure on `CStarMatrix ι ι ℂ`) and a silent break there produces a wall of unrelated
errors.  The last three are the ones that failed in the pre-abstraction version of this
file; they are the reason the corner is developed over an abstract `A`. -/

section Diagnostics

example (ι : Type*) [Fintype ι] [DecidableEq ι] : Mul (CStarMatrix ι ι ℂ) := inferInstance

example (ι : Type*) [Fintype ι] [DecidableEq ι] :
    NonUnitalNonAssocSemiring (CStarMatrix ι ι ℂ) := inferInstance

example (ι : Type*) [Fintype ι] [DecidableEq ι] : ContinuousMul (CStarMatrix ι ι ℂ) :=
  inferInstance

example (ι : Type*) [Fintype ι] [DecidableEq ι] : IsTopologicalSemiring (CStarMatrix ι ι ℂ) :=
  inferInstance

example (ι : Type*) [Fintype ι] [DecidableEq ι] : CStarAlgebra (CStarMatrix ι ι ℂ) :=
  inferInstance

example (X : Type*) [TopologicalSpace X] (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Ring C(X, CStarMatrix ι ι ℂ) := inferInstance

example (X : Type*) [TopologicalSpace X] (ι : Type*) [Fintype ι] [DecidableEq ι] :
    StarRing C(X, CStarMatrix ι ι ℂ) := inferInstance

example (X : Type*) [TopologicalSpace X] [CompactSpace X] (ι : Type*) [Fintype ι]
    [DecidableEq ι] : CStarAlgebra C(X, CStarMatrix ι ι ℂ) := inferInstance

example (X : Type*) [TopologicalSpace X] [CompactSpace X] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (a b c : SectionAlgebra X ι) : a * (b + c) = a * b + a * c :=
  mul_add a b c

example (X : Type*) [TopologicalSpace X] [CompactSpace X] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (a b c : SectionAlgebra X ι) : a * b * c = a * (b * c) :=
  mul_assoc a b c

example (X : Type*) [TopologicalSpace X] [CompactSpace X] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (a b : SectionAlgebra X ι) : star (a * b) = star b * star a :=
  star_mul a b

end Diagnostics

/-! ### Passing between matrices of functions and functions of matrices -/

section Bridge

variable {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A matrix of continuous scalar functions, viewed as a continuous matrix-valued
function.  This is the identification `M_ι(C(X)) ≅ C(X, M_ι)`. -/
def ofFunctionMatrix (M : Matrix ι ι C(X, ℂ)) : SectionAlgebra X ι :=
  ⟨fun x => CStarMatrix.ofMatrix (matEval x M), by
    show Continuous fun x => (matEval x M : Matrix ι ι ℂ)
    exact continuous_matrix fun i j => (M i j).continuous⟩

@[simp]
theorem ofFunctionMatrix_apply (M : Matrix ι ι C(X, ℂ)) (x : X) (i j : ι) :
    ofFunctionMatrix M x i j = M i j x := rfl

theorem ofFunctionMatrix_mul (M N : Matrix ι ι C(X, ℂ)) :
    ofFunctionMatrix (M * N) = ofFunctionMatrix M * ofFunctionMatrix N := by
  refine ContinuousMap.ext fun x => CStarMatrix.ext fun i j => ?_
  show (matEval x (M * N)) i j = ((ofFunctionMatrix M * ofFunctionMatrix N) x) i j
  rw [matEval_mul]
  rfl

theorem ofFunctionMatrix_star (M : Matrix ι ι C(X, ℂ)) :
    ofFunctionMatrix (star M) = star (ofFunctionMatrix M) := by
  refine ContinuousMap.ext fun x => CStarMatrix.ext fun i j => ?_
  show (matEval x (star M)) i j = ((star (ofFunctionMatrix M)) x) i j
  rw [Matrix.star_eq_conjTranspose, matEval_conjTranspose, Matrix.conjTranspose_apply]
  rfl

theorem ofFunctionMatrix_one : ofFunctionMatrix (1 : Matrix ι ι C(X, ℂ)) = 1 := by
  refine ContinuousMap.ext fun x => CStarMatrix.ext fun i j => ?_
  show (matEval x (1 : Matrix ι ι C(X, ℂ))) i j = ((1 : SectionAlgebra X ι) x) i j
  rw [matEval_one]
  rfl

theorem isStarProjection_ofFunctionMatrix {M : Matrix ι ι C(X, ℂ)}
    (h : IsStarProjection M) : IsStarProjection (ofFunctionMatrix M) where
  isIdempotentElem := by
    show ofFunctionMatrix M * ofFunctionMatrix M = ofFunctionMatrix M
    rw [← ofFunctionMatrix_mul, h.isIdempotentElem.eq]
  isSelfAdjoint := by
    show star (ofFunctionMatrix M) = ofFunctionMatrix M
    rw [← ofFunctionMatrix_star, h.isSelfAdjoint.star_eq]

/-- Murray–von Neumann equivalence transports from the matrix-over-functions picture to
the C-star picture: "bundle isomorphism" is the same relation in both. -/
theorem murrayVonNeumannEquiv_ofFunctionMatrix {P Q : Matrix ι ι C(X, ℂ)}
    (h : MurrayVonNeumannEquiv P Q) :
    MurrayVonNeumannEquiv (ofFunctionMatrix P) (ofFunctionMatrix Q) := by
  obtain ⟨v, hv₁, hv₂⟩ := h
  refine ⟨ofFunctionMatrix v, ?_, ?_⟩
  · rw [← ofFunctionMatrix_star, ← ofFunctionMatrix_mul, hv₁]
  · rw [← ofFunctionMatrix_star, ← ofFunctionMatrix_mul, hv₂]

end Bridge

end

end STW59
end GroupApproximation
