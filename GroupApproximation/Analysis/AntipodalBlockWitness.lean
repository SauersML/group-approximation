import GroupApproximation.Analysis.AntipodalHomogeneousBlock
import GroupApproximation.Analysis.CStarStatePullback

/-!
# The distinguished state and trace-zero witness in an antipodal block

The counterexample uses a rank-one trivial summand and an increasingly large
tautological complement.  In the real-projective fixed-point model the
projection onto the trivial summand is the polynomial `(1 + u) / 2` in the
antipodal involution.  This makes the relevant elements available without a
vector-bundle API.

This file constructs:

* constant covariant elements;
* fibre evaluation as a unital star-algebra homomorphism;
* the corner state at the trivial coordinate;
* the diagonal trace-zero witness, with eigenvalue `1` on the trivial line and
  `-1/s` on each of the `s` complementary coordinates.
-/

namespace GroupApproximation
namespace STW22

open CStarState
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

open scoped CStarAlgebra ComplexOrder Matrix

noncomputable section

/-- A constant matrix fixed by conjugation with the antipodal involution gives
an element of the projective block. -/
def constantCovariantElement (d s : ℕ)
    (a : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (ha : blockInvolution s * a * blockInvolution s = a) :
    RealProjectiveBlock d s :=
  ⟨ContinuousMap.const _ a, fun _ ↦ ha.symm⟩

@[simp]
theorem constantCovariantElement_apply (d s : ℕ)
    (a : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (ha : blockInvolution s * a * blockInvolution s = a) (x : Sphere d) :
    (constantCovariantElement d s a ha : SphereMatrixFunctions d s) x = a :=
  rfl

/-- Evaluation at one point of the sphere. -/
def antipodalBlockEval (d s : ℕ) (x : Sphere d) :
    RealProjectiveBlock d s →⋆ₐ[ℂ] CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ where
  toFun a := a.1 x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
theorem antipodalBlockEval_apply (d s : ℕ) (x : Sphere d)
    (a : RealProjectiveBlock d s) : antipodalBlockEval d s x a = a.1 x :=
  rfl

/-- The state of a matrix algebra given by its distinguished diagonal entry. -/
def matrixCornerState (s : ℕ) :
    State (CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ) where
  toCLM := LinearMap.mkContinuous
    { toFun := fun a ↦ a 0 0
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 fun a ↦ by
      rw [one_mul]
      exact CStarMatrix.norm_entry_le_norm (M := a) (i := 0) (j := 0)
  map_one := CStarMatrix.one_apply_eq 0
  norm_le := LinearMap.mkContinuous_norm_le _ zero_le_one _

@[simp]
theorem matrixCornerState_apply (s : ℕ)
    (a : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ) :
    (matrixCornerState s).toCLM a = a 0 0 :=
  rfl

/-- The fibre state at the trivial line. -/
def trivialLineState (d s : ℕ) (x : Sphere d) : State (RealProjectiveBlock d s) :=
  (matrixCornerState s).comp (antipodalBlockEval d s x)

@[simp]
theorem trivialLineState_apply (d s : ℕ) (x : Sphere d)
    (a : RealProjectiveBlock d s) :
    (trivialLineState d s x).toCLM a = a.1 x 0 0 :=
  rfl

/-- Projection onto the distinguished trivial coordinate, as a polynomial in
the antipodal involution. -/
def trivialProjectionMatrix (s : ℕ) :
    CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ :=
  (2 : ℂ)⁻¹ • (1 + blockInvolution s)

theorem blockInvolution_conj_trivialProjection (s : ℕ) :
    blockInvolution s * trivialProjectionMatrix s * blockInvolution s =
      trivialProjectionMatrix s := by
  rw [trivialProjectionMatrix]
  simp only [mul_smul_comm, smul_mul_assoc]
  rw [mul_add, add_mul, blockInvolution_sq]
  simp [mul_assoc]

/-- The block projection onto the trivial summand. -/
def trivialProjection (d s : ℕ) : RealProjectiveBlock d s :=
  constantCovariantElement d s (trivialProjectionMatrix s)
    (blockInvolution_conj_trivialProjection s)

/-- A trace-zero diagonal witness: `1` on the trivial line and `-1/s` on
each of the `s` complementary coordinates. -/
def witnessMatrix (s : ℕ) : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ :=
  trivialProjectionMatrix s - (s : ℂ)⁻¹ • (1 - trivialProjectionMatrix s)

theorem blockInvolution_conj_witness (s : ℕ) :
    blockInvolution s * witnessMatrix s * blockInvolution s = witnessMatrix s := by
  rw [witnessMatrix]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
  rw [blockInvolution_conj_trivialProjection, mul_one, blockInvolution_sq,
    blockInvolution_conj_trivialProjection]

@[simp]
theorem trivialProjectionMatrix_zero_zero (s : ℕ) : trivialProjectionMatrix s 0 0 = 1 := by
  simp [trivialProjectionMatrix, blockInvolution, blockSign, CStarMatrix.one_apply_eq]

@[simp]
theorem witnessMatrix_zero_zero (s : ℕ) : witnessMatrix s 0 0 = 1 := by
  simp [witnessMatrix]

/-- The trace-zero witness as an element of the projective block. -/
def blockWitness (d s : ℕ) : RealProjectiveBlock d s :=
  constantCovariantElement d s (witnessMatrix s) (blockInvolution_conj_witness s)

@[simp]
theorem trivialLineState_blockWitness (d s : ℕ) (x : Sphere d) :
    (trivialLineState d s x).toCLM (blockWitness d s) = 1 := by
  exact witnessMatrix_zero_zero s

end

end STW22
end GroupApproximation
