import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.StabQComplexProjection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

/-!
# Equivalent orthogonal projections are homotopic

The converse half of `K₀(ℂ) = ℤ` in Cuntz's picture of Kasparov theory (J. Cuntz, *A new look
at KK-theory*, K-Theory 1 (1987), §2; Blackadar, *K-Theory for Operator Algebras*, 4.2 and 17.3):
if `p` and `q` are orthogonal star projections and `v` is a partial isometry with `v⋆v = p` and
`vv⋆ = q`, then the rotation
`P(t) = cos² θ • p + sin² θ • q + cos θ sin θ • (v + v⋆)`, `θ = πt/2`,
is a norm-continuous path of star projections from `p` to `q`.  Hence `p` and `q` define the same
homotopy class of `⋆`-homomorphisms `ℂ → B`.

* `OrthPartialIsometry p q v`: the algebraic relations of such a partial isometry;
* `rotProj_mul_self`: the multiplication rule for `a • p + b • q + m • (v + v⋆)`;
* `OrthPartialIsometry.projectionPath : ProjectionPath p q`;
* `OrthPartialIsometry.projectionClass_eq`.

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(lane TWWKK-Complex, work order WO-TWWKK-C: `stabQ.Hom ℂ ℂ ≃+ ℤ`).
-/

namespace GroupApproximation.Full.TWWKK

universe u

noncomputable section

section Rotation

variable {B : Type u} [NonUnitalCStarAlgebra B]

/-- A **partial isometry `v` between orthogonal projections**: `p ⊥ q`, `v⋆v = p`, `vv⋆ = q`,
together with the relations `vp = v` and `qv = v` (automatic in a C⋆-algebra). -/
structure OrthPartialIsometry (p q v : B) : Prop where
  /-- The source projection. -/
  isStarProjection_left : IsStarProjection p
  /-- The range projection. -/
  isStarProjection_right : IsStarProjection q
  /-- The two projections are orthogonal. -/
  orth : p * q = 0
  /-- `v⋆v = p`. -/
  star_mul_self : star v * v = p
  /-- `vv⋆ = q`. -/
  mul_star_self : v * star v = q
  /-- `vp = v`. -/
  mul_left : v * p = v
  /-- `qv = v`. -/
  left_mul : q * v = v

namespace OrthPartialIsometry

variable {p q v : B} (h : OrthPartialIsometry p q v)
include h

theorem orth' : q * p = 0 := by
  have e := congrArg star h.orth
  rwa [star_mul, h.isStarProjection_right.isSelfAdjoint.star_eq,
    h.isStarProjection_left.isSelfAdjoint.star_eq, star_zero] at e

theorem left_mul_zero : p * v = 0 := by
  rw [← h.left_mul, ← mul_assoc, h.orth, zero_mul]

theorem mul_right_zero : v * q = 0 := by
  rw [← h.mul_left, mul_assoc, h.orth, mul_zero]

theorem mul_self_zero : v * v = 0 :=
  calc v * v = v * p * v := by rw [h.mul_left]
    _ = v * (p * v) := mul_assoc v p v
    _ = 0 := by rw [h.left_mul_zero, mul_zero]

theorem star_mul_left_zero : star v * p = 0 := by
  have e := congrArg star h.left_mul_zero
  rwa [star_mul, h.isStarProjection_left.isSelfAdjoint.star_eq, star_zero] at e

theorem left_mul_star : p * star v = star v := by
  have e := congrArg star h.mul_left
  rwa [star_mul, h.isStarProjection_left.isSelfAdjoint.star_eq] at e

theorem star_mul_right : star v * q = star v := by
  have e := congrArg star h.left_mul
  rwa [star_mul, h.isStarProjection_right.isSelfAdjoint.star_eq] at e

theorem right_mul_star_zero : q * star v = 0 := by
  have e := congrArg star h.mul_right_zero
  rwa [star_mul, h.isStarProjection_right.isSelfAdjoint.star_eq, star_zero] at e

theorem star_mul_star_zero : star v * star v = 0 := by
  have e := congrArg star h.mul_self_zero
  rwa [star_mul, star_zero] at e

end OrthPartialIsometry

/-- The **rotation element** `a • p + b • q + m • (v + v⋆)`. -/
def rotProj (p q v : B) (a b m : ℂ) : B :=
  a • p + b • q + m • (v + star v)

/-- **Multiplication rule for rotation elements.** -/
theorem rotProj_mul_self {p q v : B} (h : OrthPartialIsometry p q v) (a b m : ℂ) :
    rotProj p q v a b m * rotProj p q v a b m =
      rotProj p q v (a * a + m * m) (b * b + m * m) (m * (a + b)) := by
  have hpp : p * p = p := h.isStarProjection_left.isIdempotentElem.eq
  have hqq : q * q = q := h.isStarProjection_right.isIdempotentElem.eq
  simp only [rotProj, add_mul, mul_add, smul_mul_smul_comm, hpp, hqq, h.orth, h.orth',
    h.left_mul_zero, h.left_mul_star, h.left_mul, h.right_mul_star_zero, h.mul_left,
    h.mul_right_zero, h.mul_self_zero, h.mul_star_self, h.star_mul_left_zero, h.star_mul_right,
    h.star_mul_self, h.star_mul_star_zero, smul_zero, add_zero, zero_add]
  module

/-- A rotation element with real coefficients is self-adjoint. -/
theorem rotProj_isSelfAdjoint {p q v : B} (h : OrthPartialIsometry p q v) (r s k : ℝ) :
    IsSelfAdjoint (rotProj p q v (r : ℂ) (s : ℂ) (k : ℂ)) := by
  have hr : IsSelfAdjoint (r : ℂ) := Complex.conj_ofReal r
  have hs : IsSelfAdjoint (s : ℂ) := Complex.conj_ofReal s
  have hk : IsSelfAdjoint (k : ℂ) := Complex.conj_ofReal k
  exact ((hr.smul h.isStarProjection_left.isSelfAdjoint).add
    (hs.smul h.isStarProjection_right.isSelfAdjoint)).add
      (hk.smul (IsSelfAdjoint.add_star_self v))

/-- **A rotation element with `c² + s² = 1` is a star projection.** -/
theorem rotProj_isStarProjection {p q v : B} (h : OrthPartialIsometry p q v) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    IsStarProjection (rotProj p q v ((c ^ 2 : ℝ) : ℂ) ((s ^ 2 : ℝ) : ℂ) ((c * s : ℝ) : ℂ)) := by
  refine ⟨?_, rotProj_isSelfAdjoint h _ _ _⟩
  show rotProj p q v ((c ^ 2 : ℝ) : ℂ) ((s ^ 2 : ℝ) : ℂ) ((c * s : ℝ) : ℂ) *
      rotProj p q v ((c ^ 2 : ℝ) : ℂ) ((s ^ 2 : ℝ) : ℂ) ((c * s : ℝ) : ℂ) =
    rotProj p q v ((c ^ 2 : ℝ) : ℂ) ((s ^ 2 : ℝ) : ℂ) ((c * s : ℝ) : ℂ)
  rw [rotProj_mul_self h]
  have ha : c ^ 2 * c ^ 2 + c * s * (c * s) = c ^ 2 := by linear_combination c ^ 2 * hcs
  have hb : s ^ 2 * s ^ 2 + c * s * (c * s) = s ^ 2 := by linear_combination s ^ 2 * hcs
  have hm : c * s * (c ^ 2 + s ^ 2) = c * s := by linear_combination c * s * hcs
  have ha' : ((c ^ 2 : ℝ) : ℂ) * ((c ^ 2 : ℝ) : ℂ) + ((c * s : ℝ) : ℂ) * ((c * s : ℝ) : ℂ) =
      ((c ^ 2 : ℝ) : ℂ) := by exact_mod_cast ha
  have hb' : ((s ^ 2 : ℝ) : ℂ) * ((s ^ 2 : ℝ) : ℂ) + ((c * s : ℝ) : ℂ) * ((c * s : ℝ) : ℂ) =
      ((s ^ 2 : ℝ) : ℂ) := by exact_mod_cast hb
  have hm' : ((c * s : ℝ) : ℂ) * (((c ^ 2 : ℝ) : ℂ) + ((s ^ 2 : ℝ) : ℂ)) = ((c * s : ℝ) : ℂ) := by
    exact_mod_cast hm
  rw [ha', hb', hm']

/-- **The rotation path** from `p` to `q` along `v`. -/
def rotPath (p q v : B) (t : ℝ) : B :=
  rotProj p q v ((Real.cos (Real.pi / 2 * t) ^ 2 : ℝ) : ℂ)
    ((Real.sin (Real.pi / 2 * t) ^ 2 : ℝ) : ℂ)
    ((Real.cos (Real.pi / 2 * t) * Real.sin (Real.pi / 2 * t) : ℝ) : ℂ)

theorem continuous_rotPath (p q v : B) : Continuous (rotPath p q v) := by
  have hc : Continuous fun t : ℝ => Real.cos (Real.pi / 2 * t) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hs : Continuous fun t : ℝ => Real.sin (Real.pi / 2 * t) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  show Continuous fun t : ℝ =>
    ((Real.cos (Real.pi / 2 * t) ^ 2 : ℝ) : ℂ) • p +
      ((Real.sin (Real.pi / 2 * t) ^ 2 : ℝ) : ℂ) • q +
      ((Real.cos (Real.pi / 2 * t) * Real.sin (Real.pi / 2 * t) : ℝ) : ℂ) • (v + star v)
  refine (Continuous.add ?_ ?_).add ?_
  · exact (Complex.continuous_ofReal.comp (hc.pow 2)).smul continuous_const
  · exact (Complex.continuous_ofReal.comp (hs.pow 2)).smul continuous_const
  · exact (Complex.continuous_ofReal.comp (hc.mul hs)).smul continuous_const

theorem rotPath_isStarProjection {p q v : B} (h : OrthPartialIsometry p q v) (t : ℝ) :
    IsStarProjection (rotPath p q v t) :=
  rotProj_isStarProjection h _ _ (Real.cos_sq_add_sin_sq (Real.pi / 2 * t))

theorem rotPath_zero (p q v : B) : rotPath p q v 0 = p := by
  unfold rotPath rotProj
  rw [mul_zero, Real.cos_zero, Real.sin_zero]
  simp

theorem rotPath_one (p q v : B) : rotPath p q v 1 = q := by
  unfold rotPath rotProj
  rw [mul_one, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- **Equivalent orthogonal projections are joined by a projection path.** -/
theorem OrthPartialIsometry.projectionPath {p q v : B} (h : OrthPartialIsometry p q v) :
    ProjectionPath p q :=
  ⟨rotPath p q v, continuous_rotPath p q v, rotPath_isStarProjection h, rotPath_zero p q v,
    rotPath_one p q v⟩

/-- **Equivalent orthogonal projections define the same homotopy class.** -/
theorem OrthPartialIsometry.projectionClass_eq {p q v : B} (h : OrthPartialIsometry p q v) :
    projectionClass p h.isStarProjection_left = projectionClass q h.isStarProjection_right :=
  projectionClass_eq_of_path h.projectionPath

/-- **Equivalent orthogonal projections give homotopic homomorphisms.** -/
theorem OrthPartialIsometry.nHomotopic {p q v : B} (h : OrthPartialIsometry p q v) :
    NHomotopic (complexHom p h.isStarProjection_left) (complexHom q h.isStarProjection_right) :=
  (nHomotopic_complexHom_iff p q _ _).mpr h.projectionPath

end Rotation

end

end GroupApproximation.Full.TWWKK
