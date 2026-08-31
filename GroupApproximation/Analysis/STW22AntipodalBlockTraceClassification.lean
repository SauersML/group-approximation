import GroupApproximation.Analysis.STW22AntipodalTraceBoundary
import GroupApproximation.Analysis.STW22RealProjectiveBlockTypeI

/-!
# Traces on a concrete real-projective block

This file proves the algebraic part of the literal trace classification for
the antipodal blocks.  The key point is that a tracial state only sees the
normalized fibre trace: off-diagonal generators have trace zero, while all
diagonal matrix units have the same trace, even after multiplication by a
central scalar section.
-/

namespace GroupApproximation
namespace STW22AntipodalBlockTraceClassification

open STW22
open STW22AntipodalTraceBoundary
open CuntzPedersenCoronaObstruction
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

open scoped ComplexOrder

/-- Multiplication by a central coefficient preserves trace-zero of a
self-commutator. -/
theorem tracialState_central_mul_selfCommutator_eq_zero
    {A : Type*} [CStarAlgebra A] (tau : TracialState A) (c z : A)
    (hc : forall a : A, c * a = a * c) :
    tau (c * selfCommutator z) = 0 := by
  rw [selfCommutator_apply, mul_sub, tau.map_sub]
  apply sub_eq_zero.mpr
  calc
    tau (c * (star z * z)) = tau ((c * star z) * z) := by rw [mul_assoc]
    _ = tau (z * (c * star z)) := tau.map_mul_comm _ _
    _ = tau ((z * c) * star z) := by rw [mul_assoc]
    _ = tau ((c * z) * star z) := by rw [hc z]
    _ = tau (c * (z * star z)) := by rw [mul_assoc]

/-- The type-I distinguished matrix unit is the geometric trivial-line
projection used in the trace calculation. -/
theorem distinguishedMatrixUnit_eq_trivialProjection (d s : Nat) :
    distinguishedMatrixUnit d s = trivialProjection d s := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  apply CStarMatrix.ext
  intro i j
  simp [trivialProjection, trivialProjectionMatrix_eq_single,
    distinguishedMatrixUnit_apply, Matrix.single_apply]

/-- A lower diagonal matrix unit is the corresponding geometric diagonal
coordinate projection. -/
theorem lowerBlockMatrixUnit_self_eq_diagonalCoordinateProjection
    (d s : Nat) (i : Fin s) :
    lowerBlockMatrixUnit d s i i = diagonalCoordinateProjection d s i := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  apply CStarMatrix.ext
  intro a b
  simp [diagonalCoordinateProjection_apply, lowerBlockMatrixUnit_apply,
    Matrix.single_apply]

/-- Central coefficients do not disturb equality of the traces of the
distinguished and lower diagonal rank-one projections. -/
theorem tracialState_central_mul_diagonal_eq
    (d s : Nat) (tau : TracialState (RealProjectiveBlock d s))
    (c : C(Sphere d, Complex)) (hc : forall x : Sphere d, c (-x) = c x)
    (i : Fin s) :
    tau (evenScalarElement (s := s) c hc * distinguishedMatrixUnit d s) =
      tau (evenScalarElement (s := s) c hc * lowerBlockMatrixUnit d s i i) := by
  rw [distinguishedMatrixUnit_eq_trivialProjection,
    lowerBlockMatrixUnit_self_eq_diagonalCoordinateProjection]
  apply sub_eq_zero.mp
  rw [← tau.map_sub, ← mul_sub]
  rw [← sum_selfCommutator_coordinateLowerSection d s i, Finset.mul_sum,
    map_sum tau.toLinearMap]
  exact Finset.sum_eq_zero fun r _ =>
    tracialState_central_mul_selfCommutator_eq_zero tau _ _
      (evenScalarElement_mul_comm c hc)

/-- Left and right multiplication identities detecting a lower-block
off-diagonal matrix unit as a commutator. -/
theorem lowerBlockMatrixUnit_projection_mul
    (d s : Nat) (i j : Fin s) :
    lowerBlockMatrixUnit d s i i * lowerBlockMatrixUnit d s i j =
      lowerBlockMatrixUnit d s i j := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (lowerBlockMatrixUnit d s i i).1 x *
      (lowerBlockMatrixUnit d s i j).1 x =
    (lowerBlockMatrixUnit d s i j).1 x
  rw [show (lowerBlockMatrixUnit d s i i).1 x =
      CStarMatrix.ofMatrix (Matrix.single i.succ i.succ 1) by
        apply CStarMatrix.ext; simp [Matrix.single_apply],
    show (lowerBlockMatrixUnit d s i j).1 x =
      CStarMatrix.ofMatrix (Matrix.single i.succ j.succ 1) by
        apply CStarMatrix.ext; simp [Matrix.single_apply]]
  apply CStarMatrix.ext
  intro a b
  rw [CStarMatrix.mul_apply]
  rw [Finset.sum_eq_single i.succ]
  · by_cases ha : i.succ = a <;> by_cases hb : j.succ = b <;>
      simp [ha, hb]
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

theorem lowerBlockMatrixUnit_mul_projection_of_ne
    (d s : Nat) (i j : Fin s) (hij : i ≠ j) :
    lowerBlockMatrixUnit d s i j * lowerBlockMatrixUnit d s i i = 0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (lowerBlockMatrixUnit d s i j).1 x *
      (lowerBlockMatrixUnit d s i i).1 x =
    (0 : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) Complex)
  rw [show (lowerBlockMatrixUnit d s i i).1 x =
      CStarMatrix.ofMatrix (Matrix.single i.succ i.succ 1) by
        apply CStarMatrix.ext; simp [Matrix.single_apply],
    show (lowerBlockMatrixUnit d s i j).1 x =
      CStarMatrix.ofMatrix (Matrix.single i.succ j.succ 1) by
        apply CStarMatrix.ext; simp [Matrix.single_apply]]
  change Matrix.single i.succ j.succ (1 : Complex) *
      Matrix.single i.succ i.succ 1 = 0
  exact Matrix.single_mul_single_of_ne (1 : Complex)
    i.succ j.succ i.succ (fun h => hij (Fin.succ_inj.mp h.symm)) 1

/-- Every central multiple of an off-diagonal lower-block generator has trace
zero. -/
theorem tracialState_central_mul_lowerBlockMatrixUnit_eq_zero
    (d s : Nat) (tau : TracialState (RealProjectiveBlock d s))
    (c : C(Sphere d, Complex)) (hc : forall x : Sphere d, c (-x) = c x)
    (i j : Fin s) (hij : i ≠ j) :
    tau (evenScalarElement (s := s) c hc * lowerBlockMatrixUnit d s i j) = 0 := by
  let q := lowerBlockMatrixUnit d s i i
  let e := lowerBlockMatrixUnit d s i j
  let z := evenScalarElement (s := s) c hc
  calc
    tau (z * e) = tau ((z * q) * e) := by
      rw [mul_assoc, lowerBlockMatrixUnit_projection_mul]
    _ = tau (e * (z * q)) := tau.map_mul_comm _ _
    _ = tau ((e * z) * q) := by rw [mul_assoc]
    _ = tau ((z * e) * q) := by rw [evenScalarElement_mul_comm c hc e]
    _ = tau (z * (e * q)) := by rw [mul_assoc]
    _ = 0 := by rw [lowerBlockMatrixUnit_mul_projection_of_ne d s i j hij,
      mul_zero, tau.map_zero]

/-- The lower coordinate generator is the `(i,0)` corner. -/
theorem lowerProjection_mul_typeICoordinateLowerSection
    (d s : Nat) (i : Fin s) (r : Fin (d + 1)) :
    lowerBlockMatrixUnit d s i i * typeICoordinateLowerSection d s i r =
      typeICoordinateLowerSection d s i r := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (lowerBlockMatrixUnit d s i i).1 x *
      (typeICoordinateLowerSection d s i r).1 x =
    (typeICoordinateLowerSection d s i r).1 x
  rw [show (lowerBlockMatrixUnit d s i i).1 x =
      CStarMatrix.ofMatrix (Matrix.single i.succ i.succ 1) by
        apply CStarMatrix.ext; simp [Matrix.single_apply],
    show (typeICoordinateLowerSection d s i r).1 x =
      CStarMatrix.ofMatrix
        (Matrix.single i.succ 0 (typeISphereCoordinate d r x)) by
        apply CStarMatrix.ext; simp [Matrix.single_apply]]
  change Matrix.single i.succ i.succ (1 : Complex) *
      Matrix.single i.succ 0 (typeISphereCoordinate d r x) =
    Matrix.single i.succ 0 (typeISphereCoordinate d r x)
  rw [Matrix.single_mul_single_same, one_mul]

theorem typeICoordinateLowerSection_mul_lowerProjection
    (d s : Nat) (i : Fin s) (r : Fin (d + 1)) :
    typeICoordinateLowerSection d s i r * lowerBlockMatrixUnit d s i i = 0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (typeICoordinateLowerSection d s i r).1 x *
      (lowerBlockMatrixUnit d s i i).1 x =
    (0 : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) Complex)
  rw [show (lowerBlockMatrixUnit d s i i).1 x =
      CStarMatrix.ofMatrix (Matrix.single i.succ i.succ 1) by
        apply CStarMatrix.ext; simp [Matrix.single_apply],
    show (typeICoordinateLowerSection d s i r).1 x =
      CStarMatrix.ofMatrix
        (Matrix.single i.succ 0 (typeISphereCoordinate d r x)) by
        apply CStarMatrix.ext; simp [Matrix.single_apply]]
  change Matrix.single i.succ 0 (typeISphereCoordinate d r x) *
      Matrix.single i.succ i.succ (1 : Complex) = 0
  exact Matrix.single_mul_single_of_ne (typeISphereCoordinate d r x)
    i.succ 0 i.succ (Fin.succ_ne_zero i).symm 1

/-- Every central multiple of a lower coordinate generator has trace zero. -/
theorem tracialState_central_mul_typeICoordinateLowerSection_eq_zero
    (d s : Nat) (tau : TracialState (RealProjectiveBlock d s))
    (c : C(Sphere d, Complex)) (hc : forall x : Sphere d, c (-x) = c x)
    (i : Fin s) (r : Fin (d + 1)) :
    tau (evenScalarElement (s := s) c hc * typeICoordinateLowerSection d s i r) = 0 := by
  let q := lowerBlockMatrixUnit d s i i
  let v := typeICoordinateLowerSection d s i r
  let z := evenScalarElement (s := s) c hc
  calc
    tau (z * v) = tau ((z * q) * v) := by
      rw [mul_assoc, lowerProjection_mul_typeICoordinateLowerSection]
    _ = tau (v * (z * q)) := tau.map_mul_comm _ _
    _ = tau ((v * z) * q) := by rw [mul_assoc]
    _ = tau ((z * v) * q) := by rw [evenScalarElement_mul_comm c hc v]
    _ = tau (z * (v * q)) := by rw [mul_assoc]
    _ = 0 := by rw [typeICoordinateLowerSection_mul_lowerProjection,
      mul_zero, tau.map_zero]

/-- The upper coordinate generator is the `(0,i)` corner. -/
theorem distinguishedProjection_mul_typeICoordinateUpperSection
    (d s : Nat) (i : Fin s) (r : Fin (d + 1)) :
    distinguishedMatrixUnit d s * typeICoordinateUpperSection d s i r =
      typeICoordinateUpperSection d s i r := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (distinguishedMatrixUnit d s).1 x *
      (typeICoordinateUpperSection d s i r).1 x =
    (typeICoordinateUpperSection d s i r).1 x
  rw [show (distinguishedMatrixUnit d s).1 x =
      CStarMatrix.ofMatrix (Matrix.single (0 : Fin (s + 1)) 0 1) by
        apply CStarMatrix.ext; simp [Matrix.single_apply],
    show (typeICoordinateUpperSection d s i r).1 x =
      CStarMatrix.ofMatrix
        (Matrix.single (0 : Fin (s + 1)) i.succ (typeISphereCoordinate d r x)) by
        apply CStarMatrix.ext; simp [Matrix.single_apply]]
  apply CStarMatrix.ext
  intro a b
  rw [CStarMatrix.mul_apply]
  rw [Finset.sum_eq_single (0 : Fin (s + 1))]
  · by_cases ha : (0 : Fin (s + 1)) = a <;>
      by_cases hb : i.succ = b <;> simp [ha, hb]
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

theorem typeICoordinateUpperSection_mul_distinguishedProjection
    (d s : Nat) (i : Fin s) (r : Fin (d + 1)) :
    typeICoordinateUpperSection d s i r * distinguishedMatrixUnit d s = 0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (typeICoordinateUpperSection d s i r).1 x *
      (distinguishedMatrixUnit d s).1 x =
    (0 : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) Complex)
  rw [show (distinguishedMatrixUnit d s).1 x =
      CStarMatrix.ofMatrix (Matrix.single (0 : Fin (s + 1)) 0 1) by
        apply CStarMatrix.ext; simp [Matrix.single_apply],
    show (typeICoordinateUpperSection d s i r).1 x =
      CStarMatrix.ofMatrix
        (Matrix.single (0 : Fin (s + 1)) i.succ (typeISphereCoordinate d r x)) by
        apply CStarMatrix.ext; simp [Matrix.single_apply]]
  change Matrix.single (0 : Fin (s + 1)) i.succ (typeISphereCoordinate d r x) *
      Matrix.single 0 0 (1 : Complex) = 0
  exact Matrix.single_mul_single_of_ne (typeISphereCoordinate d r x)
    0 i.succ 0 (Fin.succ_ne_zero i) 1

/-- Every central multiple of an upper coordinate generator has trace zero. -/
theorem tracialState_central_mul_typeICoordinateUpperSection_eq_zero
    (d s : Nat) (tau : TracialState (RealProjectiveBlock d s))
    (c : C(Sphere d, Complex)) (hc : forall x : Sphere d, c (-x) = c x)
    (i : Fin s) (r : Fin (d + 1)) :
    tau (evenScalarElement (s := s) c hc * typeICoordinateUpperSection d s i r) = 0 := by
  let p := distinguishedMatrixUnit d s
  let v := typeICoordinateUpperSection d s i r
  let z := evenScalarElement (s := s) c hc
  calc
    tau (z * v) = tau ((z * p) * v) := by
      rw [mul_assoc, distinguishedProjection_mul_typeICoordinateUpperSection]
    _ = tau (v * (z * p)) := tau.map_mul_comm _ _
    _ = tau ((v * z) * p) := by rw [mul_assoc]
    _ = tau ((z * v) * p) := by rw [evenScalarElement_mul_comm c hc v]
    _ = tau (z * (v * p)) := by rw [mul_assoc]
    _ = 0 := by rw [typeICoordinateUpperSection_mul_distinguishedProjection,
      mul_zero, tau.map_zero]

/-- A central coefficient times one rank-one diagonal corner carries exactly
`1/(s+1)` of the trace of that central coefficient. -/
theorem tracialState_central_mul_distinguishedMatrixUnit
    (d s : Nat) (tau : TracialState (RealProjectiveBlock d s))
    (c : C(Sphere d, Complex)) (hc : forall x : Sphere d, c (-x) = c x) :
    tau (evenScalarElement (s := s) c hc * distinguishedMatrixUnit d s) =
      ((s + 1 : Nat) : Complex)⁻¹ * tau (evenScalarElement (s := s) c hc) := by
  let z := evenScalarElement (s := s) c hc
  let p := distinguishedMatrixUnit d s
  have hone := congrArg (fun a : RealProjectiveBlock d s => tau (z * a))
    (trivialProjection_add_sum_diagonalCoordinateProjection d s)
  rw [← distinguishedMatrixUnit_eq_trivialProjection] at hone
  simp_rw [← lowerBlockMatrixUnit_self_eq_diagonalCoordinateProjection] at hone
  rw [mul_add, Finset.mul_sum, tau.map_add, map_sum tau.toLinearMap, mul_one] at hone
  dsimp only [z, p] at hone
  simp_rw [← tracialState_central_mul_diagonal_eq d s tau c hc] at hone
  have hcount :
      tau (z * p) + ∑ _i : Fin s, tau (z * p) =
        ((s + 1 : Nat) : Complex) * tau (z * p) := by
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hcount] at hone
  have hs1 : ((s + 1 : Nat) : Complex) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero s
  change tau (z * p) = _
  calc
    tau (z * p) = ((s + 1 : Nat) : Complex)⁻¹ *
        (((s + 1 : Nat) : Complex) * tau (z * p)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hs1, one_mul]
    _ = _ := by rw [hone]

/-- The even scalar function obtained by summing all diagonal entries. -/
def diagonalCoefficientSum {d s : Nat} (a : RealProjectiveBlock d s) :
    C(Sphere d, Complex) :=
  distinguishedCoefficient a + ∑ i : Fin s, lowerBlockCoefficient a i i

theorem diagonalCoefficientSum_neg {d s : Nat} (a : RealProjectiveBlock d s)
    (x : Sphere d) : diagonalCoefficientSum a (-x) = diagonalCoefficientSum a x := by
  simp only [diagonalCoefficientSum, ContinuousMap.add_apply]
  rw [distinguishedCoefficient_neg]
  congr 1
  let evNeg : C(Sphere d, Complex) →+ Complex :=
    { toFun := fun f => f (-x)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let ev : C(Sphere d, Complex) →+ Complex :=
    { toFun := fun f => f x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  rw [show (∑ i : Fin s, lowerBlockCoefficient a i i) (-x) =
      ∑ i : Fin s, lowerBlockCoefficient a i i (-x) from
        map_sum evNeg (fun i => lowerBlockCoefficient a i i) Finset.univ,
    show (∑ i : Fin s, lowerBlockCoefficient a i i) x =
      ∑ i : Fin s, lowerBlockCoefficient a i i x from
        map_sum ev (fun i => lowerBlockCoefficient a i i) Finset.univ]
  exact Finset.sum_congr rfl fun i _ => lowerBlockCoefficient_neg a i i x

/-- The center-valued normalized matrix trace of a block section. -/
def blockCenterTrace {d s : Nat} (a : RealProjectiveBlock d s) :
    RealProjectiveBlock d s :=
  evenScalarElement (s := s)
    (((((s + 1 : Nat) : Complex)⁻¹) • diagonalCoefficientSum a))
    (fun x => by simp [diagonalCoefficientSum_neg])

@[simp] theorem blockCenterTrace_apply {d s : Nat}
    (a : RealProjectiveBlock d s) (x : Sphere d) :
    (blockCenterTrace a).1 x =
      (((s + 1 : Nat) : Complex)⁻¹ *
        (∑ i : Fin (s + 1), a.1 x i i)) • 1 := by
  apply CStarMatrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [blockCenterTrace, diagonalCoefficientSum, Fin.sum_univ_succ,
      distinguishedCoefficient_apply, lowerBlockCoefficient_apply]
    ring
  · simp [blockCenterTrace, diagonalCoefficientSum, Fin.sum_univ_succ,
      distinguishedCoefficient_apply, lowerBlockCoefficient_apply, hij]

theorem evenScalarElement_diagonalCoefficientSum_mul_distinguished
    {d s : Nat} (a : RealProjectiveBlock d s) :
    evenScalarElement (s := s) (diagonalCoefficientSum a)
        (diagonalCoefficientSum_neg a) * distinguishedMatrixUnit d s =
      evenScalarElement (s := s) (distinguishedCoefficient a)
          (distinguishedCoefficient_neg a) * distinguishedMatrixUnit d s +
        ∑ i : Fin s,
          evenScalarElement (s := s) (lowerBlockCoefficient a i i)
              (lowerBlockCoefficient_neg a i i) * distinguishedMatrixUnit d s := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  apply CStarMatrix.ext
  intro i j
  by_cases h : 0 = i ∧ 0 = j
  · rcases h with ⟨rfl, rfl⟩
    simp [diagonalCoefficientSum, distinguishedMatrixUnit_apply]
  · simp [diagonalCoefficientSum, distinguishedMatrixUnit_apply, h]

theorem blockCenterTrace_eq_smul_evenScalarElement
    {d s : Nat} (a : RealProjectiveBlock d s) :
    blockCenterTrace a =
      (((s + 1 : Nat) : Complex)⁻¹) •
        evenScalarElement (s := s) (diagonalCoefficientSum a)
          (diagonalCoefficientSum_neg a) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  apply CStarMatrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [blockCenterTrace, diagonalCoefficientSum]
    ring
  · simp [blockCenterTrace, diagonalCoefficientSum, hij]

set_option maxHeartbeats 600000 in
/-- Every tracial state on a concrete block factors through the literal
center-valued normalized fibre trace. -/
theorem tracialState_apply_eq_blockCenterTrace
    {d s : Nat} (tau : TracialState (RealProjectiveBlock d s))
    (a : RealProjectiveBlock d s) :
    tau a = tau (blockCenterTrace a) := by
  classical
  have hlower :
      tau (∑ i : Fin s, ∑ j : Fin s,
        evenScalarElement (s := s) (lowerBlockCoefficient a i j)
          (lowerBlockCoefficient_neg a i j) * lowerBlockMatrixUnit d s i j) =
      ∑ i : Fin s,
        tau (evenScalarElement (s := s) (lowerBlockCoefficient a i i)
          (lowerBlockCoefficient_neg a i i) * lowerBlockMatrixUnit d s i i) := by
    rw [map_sum tau.toLinearMap]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_sum tau.toLinearMap, Finset.sum_eq_single i]
    · intro j _ hji
      exact tracialState_central_mul_lowerBlockMatrixUnit_eq_zero d s tau
        (lowerBlockCoefficient a i j) (lowerBlockCoefficient_neg a i j) i j hji.symm
    · simp
  have hlowerCoordinate :
      tau (∑ i : Fin s, ∑ r : Fin (d + 1),
        evenScalarElement (s := s) (lowerCoordinateCoefficient a i r)
          (lowerCoordinateCoefficient_neg a i r) *
            typeICoordinateLowerSection d s i r) = 0 := by
    rw [map_sum tau.toLinearMap]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_sum tau.toLinearMap]
    exact Finset.sum_eq_zero fun r _ =>
      tracialState_central_mul_typeICoordinateLowerSection_eq_zero d s tau
        (lowerCoordinateCoefficient a i r) (lowerCoordinateCoefficient_neg a i r) i r
  have hupperCoordinate :
      tau (∑ i : Fin s, ∑ r : Fin (d + 1),
        evenScalarElement (s := s) (upperCoordinateCoefficient a i r)
          (upperCoordinateCoefficient_neg a i r) *
            typeICoordinateUpperSection d s i r) = 0 := by
    rw [map_sum tau.toLinearMap]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_sum tau.toLinearMap]
    exact Finset.sum_eq_zero fun r _ =>
      tracialState_central_mul_typeICoordinateUpperSection_eq_zero d s tau
        (upperCoordinateCoefficient a i r) (upperCoordinateCoefficient_neg a i r) i r
  conv_lhs => rw [← finiteCentralExpansion_eq a]
  simp only [finiteCentralExpansion, tau.map_add]
  rw [hlower, hlowerCoordinate, hupperCoordinate, add_zero]
  simp_rw [← tracialState_central_mul_diagonal_eq d s tau]
  rw [← map_sum tau.toLinearMap, ← tau.map_add,
    ← evenScalarElement_diagonalCoefficientSum_mul_distinguished a]
  rw [blockCenterTrace_eq_smul_evenScalarElement a, map_smul]
  simpa [smul_eq_mul] using
    tracialState_central_mul_distinguishedMatrixUnit d s tau
      (diagonalCoefficientSum a) (diagonalCoefficientSum_neg a)

end

end STW22AntipodalBlockTraceClassification
end GroupApproximation
