import GroupApproximation.KOne.AryOppositeTranspose
import GroupApproximation.Leavitt.FamilyDiagonalClass
import GroupApproximation.Meta.AxiomGuard

/-!
# The transpose anti-automorphism preserves the class groups, at arbitrary arity

`KOne/ThetaStable.lean` for `L_k(1,d)`.  The entrywise-`θ̂` transpose of a two-by-two
matrix is an anti-homomorphism sending `x_{ij}(a)` to `x_{ji}(θ̂ a)`, so it preserves the
elementary group, and `diag(u,1)` transposes to `diag(θ̂u, 1)`: `θ̂` preserves
`stableUnits`, in both directions since it is an involution.  Central units transpose to
central units, so `θ̂` preserves `centralClassGroup` as well, which is the receptacle at
arity `d`.
-/

namespace GroupApproximation
namespace AryLeavitt

open MatrixDiagonalization
open scoped Matrix

variable (k : Type) [Field k] (d : ℕ)

/-- Entrywise-`θ̂` transpose on two-by-two matrices. -/
noncomputable def thetaMat (M : Matrix (Fin 2) (Fin 2) (AryLeavittAlgebra k d)) :
    Matrix (Fin 2) (Fin 2) (AryLeavittAlgebra k d) :=
  (M.map (thetaHat k d))ᵀ

theorem thetaHat_sum {γι : Type*} (s : Finset γι) (f : γι → AryLeavittAlgebra k d) :
    thetaHat k d (∑ i ∈ s, f i) = ∑ i ∈ s, thetaHat k d (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact thetaHat_zero k d
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, thetaHat_add, ih]

theorem thetaMat_mul (X Y : Matrix (Fin 2) (Fin 2) (AryLeavittAlgebra k d)) :
    thetaMat k d (X * Y) = thetaMat k d Y * thetaMat k d X := by
  ext i j
  show thetaHat k d ((X * Y) j i) = _
  rw [Matrix.mul_apply, thetaHat_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [thetaHat_mul]
  rfl

theorem thetaMat_one :
    thetaMat k d (1 : Matrix (Fin 2) (Fin 2) (AryLeavittAlgebra k d)) = 1 := by
  ext i j
  show thetaHat k d ((1 : Matrix (Fin 2) (Fin 2) (AryLeavittAlgebra k d)) j i) = _
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq]
    exact thetaHat_one k d
  · rw [Matrix.one_apply_ne (Ne.symm h), Matrix.one_apply_ne h]
    exact thetaHat_zero k d

theorem thetaMat_add (X Y : Matrix (Fin 2) (Fin 2) (AryLeavittAlgebra k d)) :
    thetaMat k d (X + Y) = thetaMat k d X + thetaMat k d Y := by
  ext i j
  show thetaHat k d ((X + Y) j i) = _
  rw [Matrix.add_apply, thetaHat_add]
  rfl

theorem thetaMat_single (i j : Fin 2) (a : AryLeavittAlgebra k d) :
    thetaMat k d (Matrix.single i j a) = Matrix.single j i (thetaHat k d a) := by
  ext i' j'
  show thetaHat k d (Matrix.single i j a j' i') = _
  by_cases h1 : i = j'
  · by_cases h2 : j = i'
    · subst h1; subst h2
      rw [Matrix.single_apply_same, Matrix.single_apply_same]
    · rw [Matrix.single_apply_of_ne _ _ _ _ _ (by tauto),
        Matrix.single_apply_of_ne _ _ _ _ _ (by tauto)]
      exact thetaHat_zero k d
  · rw [Matrix.single_apply_of_ne _ _ _ _ _ (by tauto),
      Matrix.single_apply_of_ne _ _ _ _ _ (by tauto)]
    exact thetaHat_zero k d

/-- The unit induced by the matrix transpose map. -/
noncomputable def thetaMatUnit (u : (Matrix (Fin 2) (Fin 2) (AryLeavittAlgebra k d))ˣ) :
    (Matrix (Fin 2) (Fin 2) (AryLeavittAlgebra k d))ˣ where
  val := thetaMat k d (u : Matrix (Fin 2) (Fin 2) (AryLeavittAlgebra k d))
  inv := thetaMat k d ((u⁻¹ : (Matrix (Fin 2) (Fin 2) (AryLeavittAlgebra k d))ˣ) :
    Matrix (Fin 2) (Fin 2) (AryLeavittAlgebra k d))
  val_inv := by rw [← thetaMat_mul, Units.inv_mul, thetaMat_one]
  inv_val := by rw [← thetaMat_mul, Units.mul_inv, thetaMat_one]

/-- The transpose map preserves the elementary group. -/
theorem thetaMatUnit_mem_elementaryGroup
    {u : (Matrix (Fin 2) (Fin 2) (AryLeavittAlgebra k d))ˣ}
    (hu : u ∈ elementaryGroup (Fin 2) (AryLeavittAlgebra k d)) :
    thetaMatUnit k d u ∈ elementaryGroup (Fin 2) (AryLeavittAlgebra k d) := by
  induction hu using Subgroup.closure_induction with
  | mem z hz =>
      obtain ⟨i, j, hij, a, rfl⟩ := hz
      have hval : (thetaMatUnit k d (elementaryUnit i j hij a) :
          Matrix (Fin 2) (Fin 2) (AryLeavittAlgebra k d)) =
          ((elementaryUnit j i (Ne.symm hij) (thetaHat k d a) :
            (Matrix (Fin 2) (Fin 2) (AryLeavittAlgebra k d))ˣ) :
            Matrix (Fin 2) (Fin 2) (AryLeavittAlgebra k d)) := by
        show thetaMat k d (1 + Matrix.single i j a) = _
        rw [thetaMat_add, thetaMat_one, thetaMat_single]
        rfl
      rw [show thetaMatUnit k d (elementaryUnit i j hij a) =
        elementaryUnit j i (Ne.symm hij) (thetaHat k d a) from Units.ext hval]
      exact elementaryUnit_mem _ _ _ _
  | one =>
      have h1 : thetaMatUnit k d 1 = 1 := by
        apply Units.ext
        show thetaMat k d ((1 : (Matrix (Fin 2) (Fin 2) (AryLeavittAlgebra k d))ˣ) :
          Matrix (Fin 2) (Fin 2) (AryLeavittAlgebra k d)) = _
        exact thetaMat_one k d
      rw [h1]
      exact one_mem _
  | mul x y _ _ hx hy =>
      have hmul : thetaMatUnit k d (x * y) = thetaMatUnit k d y * thetaMatUnit k d x := by
        apply Units.ext
        show thetaMat k d ((x : Matrix (Fin 2) (Fin 2) (AryLeavittAlgebra k d)) * y) = _
        exact thetaMat_mul k d _ _
      rw [hmul]
      exact mul_mem hy hx
  | inv x _ hx =>
      have hinv : thetaMatUnit k d x⁻¹ = (thetaMatUnit k d x)⁻¹ := by
        apply Units.ext
        rfl
      rw [hinv]
      exact inv_mem hx

/-- The transpose map matches the diagonal stabilization. -/
theorem thetaMatUnit_diagUnit (u : (AryLeavittAlgebra k d)ˣ) :
    thetaMatUnit k d (diagUnit u) = diagUnit (thetaUnit k d u) := by
  apply Units.ext
  show thetaMat k d (!![(u : AryLeavittAlgebra k d), 0; 0, 1]) = _
  ext i j
  fin_cases i <;> fin_cases j
  · show thetaHat k d (u : AryLeavittAlgebra k d) = _
    rfl
  · show thetaHat k d (0 : AryLeavittAlgebra k d) = _
    exact thetaHat_zero k d
  · show thetaHat k d (0 : AryLeavittAlgebra k d) = _
    exact thetaHat_zero k d
  · show thetaHat k d (1 : AryLeavittAlgebra k d) = _
    exact thetaHat_one k d

/-- **`θ̂` preserves the stably elementary subgroup.** -/
theorem thetaUnit_mem_stableUnits {u : (AryLeavittAlgebra k d)ˣ}
    (hu : u ∈ stableUnits (AryLeavittAlgebra k d)) :
    thetaUnit k d u ∈ stableUnits (AryLeavittAlgebra k d) := by
  rw [mem_stableUnits_iff] at hu ⊢
  rw [← thetaMatUnit_diagUnit]
  exact thetaMatUnit_mem_elementaryGroup k d hu

theorem thetaUnit_thetaUnit (u : (AryLeavittAlgebra k d)ˣ) :
    thetaUnit k d (thetaUnit k d u) = u := by
  apply Units.ext
  show thetaHat k d (thetaHat k d (u : AryLeavittAlgebra k d)) = _
  exact thetaHat_thetaHat k d _

theorem thetaUnit_mul (u v : (AryLeavittAlgebra k d)ˣ) :
    thetaUnit k d (u * v) = thetaUnit k d v * thetaUnit k d u :=
  Units.ext (thetaHat_mul k d _ _)

theorem thetaUnit_inv (u : (AryLeavittAlgebra k d)ˣ) :
    thetaUnit k d u⁻¹ = (thetaUnit k d u)⁻¹ := by
  apply Units.ext
  rfl

/-- `θ̂` of a central element is central. -/
theorem thetaHat_central {c : AryLeavittAlgebra k d} (hc : ∀ x, c * x = x * c) :
    ∀ x, thetaHat k d c * x = x * thetaHat k d c := by
  intro x
  have h2 := congrArg (thetaHat k d) (hc (thetaHat k d x))
  rw [thetaHat_mul, thetaHat_mul, thetaHat_thetaHat] at h2
  exact h2.symm

/-- **`θ̂` preserves the central class group.** -/
theorem thetaUnit_mem_centralClassGroup {u : (AryLeavittAlgebra k d)ˣ}
    (hu : u ∈ centralClassGroup (AryLeavittAlgebra k d)) :
    thetaUnit k d u ∈ centralClassGroup (AryLeavittAlgebra k d) := by
  obtain ⟨c, hc, hcu⟩ := hu
  have hθc : ∀ x, ((thetaUnit k d c : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) * x =
      x * ((thetaUnit k d c : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) :=
    thetaHat_central k d hc
  refine ⟨thetaUnit k d c, hθc, ?_⟩
  have h1 := thetaUnit_mem_stableUnits k d hcu
  rw [thetaUnit_mul, thetaUnit_inv] at h1
  have hcomm : (thetaUnit k d c)⁻¹ * thetaUnit k d u =
      thetaUnit k d u * (thetaUnit k d c)⁻¹ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    set θc : (AryLeavittAlgebra k d)ˣ := thetaUnit k d c
    set x : AryLeavittAlgebra k d := ((thetaUnit k d u : (AryLeavittAlgebra k d)ˣ) :
      AryLeavittAlgebra k d)
    calc ((θc⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) * x
        = ((θc⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) * x *
            ((θc : AryLeavittAlgebra k d) * ((θc⁻¹ : (AryLeavittAlgebra k d)ˣ) :
              AryLeavittAlgebra k d)) := by
          rw [Units.mul_inv, mul_one]
      _ = ((θc⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) *
            (x * (θc : AryLeavittAlgebra k d)) *
            ((θc⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) := by
          noncomm_ring
      _ = ((θc⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) *
            ((θc : AryLeavittAlgebra k d) * x) *
            ((θc⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) := by
          rw [hθc x]
      _ = x * ((θc⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [hcomm]
  exact h1

/-- Membership in the central class group transfers along `θ̂` in both directions. -/
theorem thetaUnit_mem_centralClassGroup_iff (u : (AryLeavittAlgebra k d)ˣ) :
    thetaUnit k d u ∈ centralClassGroup (AryLeavittAlgebra k d) ↔
      u ∈ centralClassGroup (AryLeavittAlgebra k d) := by
  constructor
  · intro h
    have h2 := thetaUnit_mem_centralClassGroup k d h
    rwa [thetaUnit_thetaUnit] at h2
  · exact thetaUnit_mem_centralClassGroup k d

end AryLeavitt
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.AryLeavitt.thetaMatUnit_mem_elementaryGroup
#audit_axioms GroupApproximation.AryLeavitt.thetaUnit_mem_stableUnits
#audit_axioms GroupApproximation.AryLeavitt.thetaUnit_mem_centralClassGroup
#audit_axioms GroupApproximation.AryLeavitt.thetaUnit_mem_centralClassGroup_iff
