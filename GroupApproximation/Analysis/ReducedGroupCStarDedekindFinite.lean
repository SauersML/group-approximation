import GroupApproximation.Analysis.ReducedGroupCStarStablyFinite
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Data.Matrix.Mul

/-!
# Ring-theoretic stable finiteness of the reduced group C⋆-algebra

`Analysis.ReducedGroupCStarStablyFinite` records stable finiteness of the
concrete reduced group C⋆-algebra in the *operator-algebraic* sense
(`IsStablyFiniteCStarAlgebra`): every isometry in every finite matrix
amplification is a unitary.  Its docstring explicitly declines to identify that
predicate with mathlib's purely ring-theoretic `IsStablyFiniteRing`, because the
bridge between the two is a polar-decomposition argument that was not formalized
there.

This module formalizes that bridge and closes the gap.  The analytic content is
`mul_eq_one_comm_of_isometry_unitary`: in a unital C⋆-algebra in which every
isometry is a unitary, a one-sided ring inverse is automatically two-sided.
Given `a * b = 1`, conjugating `a⋆ a ≤ ‖a‖ ^ 2` by `b` shows `1 ≤ ‖a⋆ a‖ • (b⋆ b)`,
so `b⋆ b` is a strictly positive (hence invertible) element; the continuous
functional calculus then produces `u := b * (b⋆ b) ^ (-1/2)` with `u⋆ u = 1`, the
hypothesis upgrades this to `u u⋆ = 1`, and the resulting right inverse of `b`
must coincide with the given left inverse `a`.

Combining this with the trace argument imported from
`Analysis.UniversalKazhdanCStarConsequences` yields
`reducedGroupCStar_isStablyFiniteRing`, an unconditional `IsStablyFiniteRing`
instance for `ReducedGroupCStar G`, valid for every group `G`.

A general `CStarAlgebra` carries no `PartialOrder`/`StarOrderedRing` instance, so
both proofs install `CStarAlgebra.spectralOrder` and
`CStarAlgebra.spectralOrderedRing` locally with `letI`, exactly as the rest of
the repository does; the statements themselves mention no order.

Note that `CStarMatrix m n A` is a type synonym for `Matrix m n A` whose
algebraic instances are all `inferInstanceAs` transports.  Rather than rely on
that definitional coincidence, the passage from the C⋆-matrix algebra to the
plain matrix ring is performed explicitly through mathlib's ring equivalence
`CStarMatrix.ofMatrixRingEquiv`.
-/

namespace GroupApproximation

universe u

/-- **Isometries unitary implies Dedekind finite.**  Let `A` be a unital
C⋆-algebra in which every isometry is a unitary, i.e. `star v * v = 1` forces
`v * star v = 1`.  Then any one-sided ring inverse in `A` is two-sided:
`a * b = 1` implies `b * a = 1`.

The proof is the standard polar-decomposition argument.  Conjugating the
C⋆-bound `a⋆ a ≤ ‖a⋆ a‖ • 1` by `b` and using `b⋆ (a⋆ a) b = (ab)⋆ (ab) = 1`
gives `1 ≤ ‖a⋆ a‖ • (b⋆ b)`, so `b⋆ b` is strictly positive and in particular
invertible.  Writing `c := (b⋆ b) ^ (-1/2)` for the continuous functional
calculus power, the element `u := b * c` satisfies `u⋆ u = c (b⋆ b) c = 1`, so by
hypothesis `u u⋆ = 1`.  Thus `c * (c * b⋆)` is a right inverse of `b`, and a
right inverse of an element with a left inverse coincides with that left
inverse. -/
theorem mul_eq_one_comm_of_isometry_unitary {A : Type u} [CStarAlgebra A]
    (hfin : ∀ v : A, star v * v = 1 → v * star v = 1)
    {a b : A} (hab : a * b = 1) : b * a = 1 := by
  nontriviality A
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  -- `b` conjugates `a⋆ a` onto the unit.
  have hconj : star b * (star a * a) * b = 1 := by
    have h : star b * (star a * a) * b = star (a * b) * (a * b) := by
      simp only [star_mul, mul_assoc]
    rw [h, hab, star_one, one_mul]
  -- Hence `b⋆ b` dominates a positive multiple of the unit, so it is invertible.
  have hunit : IsUnit (star b * b) := by
    have hle : (1 : A) ≤ ‖star a * a‖ • (star b * b) := by
      have h := CStarAlgebra.star_left_conjugate_le_norm_smul
        (a := b) (b := star a * a) (IsSelfAdjoint.star_mul_self a)
      rwa [hconj] at h
    have hbig : IsUnit (‖star a * a‖ • (star b * b)) :=
      CStarAlgebra.isUnit_of_le (1 : A) hle isStrictlyPositive_one
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hab
      exact not_subsingleton A (subsingleton_of_zero_eq_one hab)
    have hrpos : 0 < ‖star a * a‖ := by
      rw [CStarRing.norm_star_mul_self]
      exact mul_pos (norm_pos_iff.mpr ha0) (norm_pos_iff.mpr ha0)
    have hinv : IsUnit (algebraMap ℝ A (‖star a * a‖)⁻¹) :=
      (isUnit_iff_ne_zero.mpr (inv_ne_zero hrpos.ne')).map (algebraMap ℝ A)
    have heq : algebraMap ℝ A (‖star a * a‖)⁻¹ * (‖star a * a‖ • (star b * b))
        = star b * b := by
      rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hrpos.ne',
        map_one, one_mul]
    have hmul := hinv.mul hbig
    rwa [heq] at hmul
  have hpos : IsStrictlyPositive (star b * b) :=
    hunit.isStrictlyPositive (star_mul_self_nonneg b)
  -- The inverse square root of `b⋆ b` supplied by the continuous functional calculus.
  have hc : (star b * b) ^ (-(1 / 2) : ℝ) * (star b * b) *
      (star b * b) ^ (-(1 / 2) : ℝ) = 1 :=
    CFC.conjugate_rpow_neg_one_half (star b * b) hpos
  have hcsa : star ((star b * b) ^ (-(1 / 2) : ℝ)) = (star b * b) ^ (-(1 / 2) : ℝ) :=
    CFC.rpow_nonneg.star_eq
  obtain ⟨c, hcdef⟩ : ∃ c : A, c = (star b * b) ^ (-(1 / 2) : ℝ) := ⟨_, rfl⟩
  rw [← hcdef] at hc hcsa
  -- `b * c` is an isometry, hence a unitary.
  have hiso : star (b * c) * (b * c) = 1 := by
    rw [star_mul, hcsa]
    calc c * star b * (b * c) = c * (star b * b) * c := by simp only [mul_assoc]
      _ = 1 := hc
  have hright : b * (c * (c * star b)) = 1 := by
    have h := hfin (b * c) hiso
    rwa [star_mul, hcsa, mul_assoc] at h
  -- A left inverse and a right inverse of `b` agree.
  have haw : a = c * (c * star b) := by
    have h1 : a * (b * (c * (c * star b))) = a := by rw [hright, mul_one]
    rw [← mul_assoc, hab, one_mul] at h1
    exact h1.symm
  rw [haw]
  exact hright

/-- Operator-algebraic stable finiteness of a unital C⋆-algebra implies
mathlib's ring-theoretic `IsStablyFiniteRing`.

For `n = 0` the matrix ring has empty index type, so the required identity is
proved entrywise from `Fin.elim0`.  For `n ≥ 1` the hypothesis says every
isometry of `CStarMatrix (Fin n) (Fin n) A` is a unitary, and
`mul_eq_one_comm_of_isometry_unitary` upgrades that to Dedekind finiteness of the
C⋆-matrix algebra; the ring equivalence `CStarMatrix.ofMatrixRingEquiv` transports
the conclusion to the plain matrix ring `Matrix (Fin n) (Fin n) A` that
`IsStablyFiniteRing` speaks about. -/
theorem IsStablyFiniteCStarAlgebra.isStablyFiniteRing {A : Type u} [CStarAlgebra A]
    (h : IsStablyFiniteCStarAlgebra A) : IsStablyFiniteRing A := by
  refine ⟨fun n => ?_⟩
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hiso : ∀ v : CStarMatrix (Fin n) (Fin n) A, star v * v = 1 → v * star v = 1 := by
    cases n with
    | zero => exact fun _ _ => CStarMatrix.ext fun i => i.elim0
    | succ m => exact fun v hv => h m v hv
  haveI : IsDedekindFiniteMonoid (CStarMatrix (Fin n) (Fin n) A) :=
    ⟨fun hxy => mul_eq_one_comm_of_isometry_unitary hiso hxy⟩
  exact IsDedekindFiniteMonoid.of_injective
    (CStarMatrix.ofMatrixRingEquiv (n := Fin n) (A := A)) (EquivLike.injective _)

open ReducedGroupCStarTrace in
/-- The concrete reduced group C⋆-algebra of an arbitrary group is stably finite
in mathlib's ring-theoretic sense: every matrix ring over it is Dedekind finite.

This is `reducedGroupCStar_isStablyFiniteCStarAlgebra` — the canonical faithful
trace of `Analysis.ReducedGroupCStarTraceFaithful` read through the matrix
amplification — pushed across the polar-decomposition bridge above.  It holds for
every group, with no approximation, amenability, or Kazhdan hypothesis. -/
instance reducedGroupCStar_isStablyFiniteRing (G : Type u) [Group G] :
    IsStablyFiniteRing (ReducedGroupCStar G) :=
  (reducedGroupCStar_isStablyFiniteCStarAlgebra G).isStablyFiniteRing

end GroupApproximation

#print axioms GroupApproximation.mul_eq_one_comm_of_isometry_unitary
#print axioms GroupApproximation.IsStablyFiniteCStarAlgebra.isStablyFiniteRing
#print axioms GroupApproximation.reducedGroupCStar_isStablyFiniteRing
