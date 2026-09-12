import GroupApproximation.Kazhdan.KazhdanGNS

/-!
# The regular character detects every group element in GNS

The regular character is the delta function at the identity.  This file
proves directly, from finite quadratic forms, that it is positive definite
and that its GNS translation representation is faithful.  The result is the
group-level detection used in the repaired symmetric-amalgam argument: once a
trace on an amalgam restricts to the regular character, no nontrivial group
word can disappear in its GNS representation.

This is the classical left-regular/GNS calculation.  The implementation uses
the Moore--Aronszajn GNS construction already proved in
`GroupApproximation.Kazhdan.KazhdanGNS`; it assumes no C*-amalgamation or
von Neumann free-product theorem.
-/

namespace GroupApproximation
namespace RegularCharacterGNS

open KazhdanFiniteModel KazhdanGNS

universe u

variable {G : Type u} [Group G]

noncomputable local instance : DecidableEq G := Classical.decEq G

/-- The real regular character of a group: `1` at the identity and `0`
elsewhere. -/
noncomputable def regularCharacter (g : G) : ℝ := if g = 1 then 1 else 0

@[simp] theorem regularCharacter_one : regularCharacter (1 : G) = 1 := by
  classical
  simp [regularCharacter]

@[simp] theorem regularCharacter_eq_zero {g : G} (hg : g ≠ 1) :
    regularCharacter g = 0 := by
  classical
  simp [regularCharacter, hg]

theorem regularCharacter_inv_mul (g h : G) :
    regularCharacter (g⁻¹ * h) = if g = h then 1 else 0 := by
  classical
  simp only [regularCharacter, inv_mul_eq_one]

/-- The regular character is positive definite.  Its quadratic form is the
sum of the squares of the coefficients. -/
theorem regularCharacter_isPositiveDefinite :
    IsPositiveDefinite (regularCharacter : G → ℝ) := by
  classical
  constructor
  · intro g h
    rw [regularCharacter_inv_mul, regularCharacter_inv_mul]
    by_cases hgh : g = h
    · subst h
      rfl
    · rw [if_neg hgh, if_neg (Ne.symm hgh)]
  · intro F c
    have hdiag :
        ∑ i ∈ F, ∑ j ∈ F,
            c i * c j * regularCharacter (i⁻¹ * j) =
          ∑ i ∈ F, c i * c i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single i]
      · rw [regularCharacter_inv_mul, if_pos rfl]
        ring
      · intro j hj hji
        rw [regularCharacter_inv_mul, if_neg hji.symm, mul_zero]
      · simp [hi]
    rw [hdiag]
    exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (c i)

/-- The regular character bundled for the repository's GNS construction. -/
noncomputable def positiveDefiniteFunction : PositiveDefiniteFunction G where
  toFun := regularCharacter
  isPositiveDefinite := regularCharacter_isPositiveDefinite

@[simp] theorem inner_kernelVector (g h : G) :
    inner ℝ (kernelVector (positiveDefiniteFunction (G := G)) g)
        (kernelVector (positiveDefiniteFunction (G := G)) h) =
      if g = h then 1 else 0 := by
  classical
  rw [KazhdanGNS.inner_kernelVector]
  exact regularCharacter_inv_mul g h

/-- Distinct group elements give distinct regular GNS kernel vectors. -/
theorem kernelVector_injective :
    Function.Injective
      (kernelVector (positiveDefiniteFunction (G := G))) := by
  intro g h hv
  by_contra hne
  classical
  have hip : (1 : ℝ) = 0 := calc
    1 = inner ℝ (kernelVector (positiveDefiniteFunction (G := G)) g)
        (kernelVector (positiveDefiniteFunction (G := G)) g) := by
          rw [inner_kernelVector]
          simp
    _ = inner ℝ (kernelVector (positiveDefiniteFunction (G := G)) g)
        (kernelVector (positiveDefiniteFunction (G := G)) h) := by rw [hv]
    _ = 0 := by
      rw [inner_kernelVector]
      simp [hne]
  exact one_ne_zero hip

/-- The GNS translation representation of the regular character is
faithful. -/
theorem representation_injective :
    Function.Injective
      (representation (positiveDefiniteFunction (G := G))) := by
  intro g h hrep
  apply kernelVector_injective (G := G)
  have happ := congrArg
    (fun T ↦ T (kernelVector (positiveDefiniteFunction (G := G)) 1)) hrep
  simpa using happ

/-- A group element killed by the regular GNS representation is the
identity. -/
theorem eq_one_of_representation_eq_one {g : G}
    (hg : representation (positiveDefiniteFunction (G := G)) g = 1) :
    g = 1 := by
  exact representation_injective (G := G) (hg.trans (map_one _).symm)

end RegularCharacterGNS
end GroupApproximation
