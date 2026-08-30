import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.NoncommRing
import GroupApproximation.Analysis.FaithfulTracialState

/-!
# A proper isometry from a proper projection compression

This file formalizes the purely algebraic calculation behind the proper
isometry in the maximal group C-star algebra of an ascending HNN extension.

Suppose `p` is a projection, `u` is unitary, and

`p < q := u * p * star u`.

Then

`s := p * star u + (1 - q)`

satisfies `star s * s = 1` but `s * star s != 1`.  Consequently the ambient
ring is neither directly finite nor stably finite.  No topology, norm, or
C-star-algebra API is needed for this calculation.

The intended application takes `p` to be the image of a Kazhdan projection
and `u` to be the canonical unitary of the HNN stable letter.  Constructing
the maximal group C-star algebra and its Kazhdan projection is deliberately
kept separate: Mathlib currently has no maximal-group-C-star-algebra API.
-/

namespace GroupApproximation

universe u

noncomputable section

/-- Algebraic data saying that a unitary conjugate `q = u p u*` of a
projection `p` properly contains `p`.  The two absorption identities are the
ring-theoretic form of `p <= q`; spelling them out avoids importing an order
on projections. -/
structure ProperProjectionCompression (A : Type u) [Ring A] [StarRing A] where
  /-- The smaller projection. -/
  p : A
  /-- The unitary implementing the shift. -/
  u : A
  /-- Self-adjointness of `p`. -/
  p_star : star p = p
  /-- Idempotence of `p`. -/
  p_mul_p : p * p = p
  /-- One unitary identity. -/
  u_star_mul : star u * u = 1
  /-- The other unitary identity. -/
  u_mul_star : u * star u = 1
  /-- Left absorption, one half of `p <= u p u*`. -/
  p_mul_conjugate : p * (u * p * star u) = p
  /-- Right absorption, the other half of `p <= u p u*`. -/
  conjugate_mul_p : (u * p * star u) * p = p
  /-- Properness of the containment. -/
  conjugate_ne : u * p * star u ≠ p

namespace ProperProjectionCompression

variable {A : Type u} [Ring A] [StarRing A]

/-- The larger projection `u p u*`. -/
def q (D : ProperProjectionCompression A) : A := D.u * D.p * star D.u

/-- The canonical isometry associated to the proper projection inclusion. -/
def isometry (D : ProperProjectionCompression A) : A :=
  D.p * star D.u + (1 - D.q)

@[simp]
theorem q_star (D : ProperProjectionCompression A) : star D.q = D.q := by
  unfold q
  rw [star_mul, star_mul, star_star, D.p_star]
  noncomm_ring

@[simp]
theorem q_mul_q (D : ProperProjectionCompression A) : D.q * D.q = D.q := by
  unfold q
  calc
    (D.u * D.p * star D.u) * (D.u * D.p * star D.u) =
        D.u * D.p * (star D.u * D.u) * D.p * star D.u := by
      noncomm_ring
    _ = D.u * D.p * D.p * star D.u := by rw [D.u_star_mul]; simp
    _ = D.u * (D.p * D.p) * star D.u := by noncomm_ring
    _ = D.u * D.p * star D.u := by rw [D.p_mul_p]

theorem p_mul_q (D : ProperProjectionCompression A) : D.p * D.q = D.p :=
  D.p_mul_conjugate

theorem q_mul_p (D : ProperProjectionCompression A) : D.q * D.p = D.p :=
  D.conjugate_mul_p

theorem q_ne_p (D : ProperProjectionCompression A) : D.q ≠ D.p :=
  D.conjugate_ne

@[simp]
theorem one_sub_q_mul_one_sub_q (D : ProperProjectionCompression A) :
    (1 - D.q) * (1 - D.q) = 1 - D.q := by
  rw [sub_mul, one_mul, mul_sub, mul_one, q_mul_q, sub_self, sub_zero]

theorem p_mul_one_sub_q (D : ProperProjectionCompression A) :
    D.p * (1 - D.q) = 0 := by
  rw [mul_sub, mul_one, p_mul_q, sub_self]

/-- The first cross term in the manuscript's expansion of `s⋆s` vanishes. -/
theorem u_mul_p_mul_one_sub_q (D : ProperProjectionCompression A) :
    (D.u * D.p) * (1 - D.q) = 0 := by
  rw [mul_assoc, D.p_mul_one_sub_q, mul_zero]

theorem one_sub_q_mul_p (D : ProperProjectionCompression A) :
    (1 - D.q) * D.p = 0 := by
  rw [sub_mul, one_mul, q_mul_p, sub_self]

theorem q_mul_u_mul_p (D : ProperProjectionCompression A) :
    D.q * (D.u * D.p) = D.u * D.p := by
  unfold q
  calc
    (D.u * D.p * star D.u) * (D.u * D.p) =
        D.u * D.p * (star D.u * D.u) * D.p := by
      noncomm_ring
    _ = D.u * D.p * D.p := by rw [D.u_star_mul]; simp
    _ = D.u * (D.p * D.p) := by noncomm_ring
    _ = D.u * D.p := by rw [D.p_mul_p]

theorem one_sub_q_mul_u_mul_p (D : ProperProjectionCompression A) :
    (1 - D.q) * (D.u * D.p) = 0 := by
  rw [sub_mul, one_mul, q_mul_u_mul_p, sub_self]

theorem p_mul_star_u_mul_one_sub_q (D : ProperProjectionCompression A) :
    (D.p * star D.u) * (1 - D.q) = 0 := by
  have h := congrArg star D.one_sub_q_mul_u_mul_p
  simpa [D.p_star] using h

@[simp]
theorem isometry_star (D : ProperProjectionCompression A) :
    star D.isometry = D.u * D.p + (1 - D.q) := by
  simp [isometry, D.p_star]

/-- The constructed element is an isometry. -/
theorem star_isometry_mul_isometry (D : ProperProjectionCompression A) :
    star D.isometry * D.isometry = 1 := by
  have h₁ : (D.u * D.p) * (D.p * star D.u) = D.q := by
    calc
      (D.u * D.p) * (D.p * star D.u) =
          D.u * (D.p * D.p) * star D.u := by noncomm_ring
      _ = D.q := by rw [D.p_mul_p]; rfl
  have h₂ : (D.u * D.p) * (1 - D.q) = 0 := by
    exact D.u_mul_p_mul_one_sub_q
  have h₃ : (1 - D.q) * (D.p * star D.u) = 0 := by
    calc
      (1 - D.q) * (D.p * star D.u) =
          ((1 - D.q) * D.p) * star D.u := by noncomm_ring
      _ = 0 := by rw [one_sub_q_mul_p, zero_mul]
  rw [isometry_star]
  unfold isometry
  rw [show (D.u * D.p + (1 - D.q)) *
        (D.p * star D.u + (1 - D.q)) =
        (D.u * D.p) * (D.p * star D.u) +
          (D.u * D.p) * (1 - D.q) +
          (1 - D.q) * (D.p * star D.u) +
          (1 - D.q) * (1 - D.q) by noncomm_ring,
      h₁, h₂, h₃, one_sub_q_mul_one_sub_q]
  noncomm_ring

/-- The final projection of the constructed isometry is exactly
`1 - (q - p)`. -/
theorem isometry_mul_star_isometry (D : ProperProjectionCompression A) :
    D.isometry * star D.isometry = 1 - (D.q - D.p) := by
  have h₁ : (D.p * star D.u) * (D.u * D.p) = D.p := by
    calc
      (D.p * star D.u) * (D.u * D.p) =
          D.p * (star D.u * D.u) * D.p := by noncomm_ring
      _ = D.p * D.p := by rw [D.u_star_mul]; simp
      _ = D.p := D.p_mul_p
  rw [isometry_star]
  unfold isometry
  rw [show (D.p * star D.u + (1 - D.q)) *
        (D.u * D.p + (1 - D.q)) =
        (D.p * star D.u) * (D.u * D.p) +
          (D.p * star D.u) * (1 - D.q) +
          (1 - D.q) * (D.u * D.p) +
          (1 - D.q) * (1 - D.q) by noncomm_ring,
      h₁, p_mul_star_u_mul_one_sub_q, one_sub_q_mul_u_mul_p,
      one_sub_q_mul_one_sub_q]
  noncomm_ring

/-- Properness of the projection inclusion makes the isometry nonunitary. -/
theorem isometry_mul_star_ne_one (D : ProperProjectionCompression A) :
    D.isometry * star D.isometry ≠ 1 := by
  rw [isometry_mul_star_isometry]
  intro h
  apply D.q_ne_p
  apply sub_eq_zero.mp
  calc
    D.q - D.p = -(1 - (D.q - D.p) - 1) := by noncomm_ring
    _ = 0 := by rw [h]; simp

/-- The proper isometry provides explicit one-sided inverses in the opposite
order. -/
theorem star_isometry_mul_eq_one_and_reverse_ne
    (D : ProperProjectionCompression A) :
    star D.isometry * D.isometry = 1 ∧
      D.isometry * star D.isometry ≠ 1 :=
  ⟨D.star_isometry_mul_isometry, D.isometry_mul_star_ne_one⟩

/-- Existential formulation of the explicit failure of direct finiteness. -/
theorem exists_one_sided_inverse (D : ProperProjectionCompression A) :
    ∃ a b : A, a * b = 1 ∧ b * a ≠ 1 :=
  ⟨star D.isometry, D.isometry,
    D.star_isometry_mul_isometry, D.isometry_mul_star_ne_one⟩

/-- The proper isometry `s` is not invertible: if it were a unit, its given
left inverse `star s` would coincide with the two-sided inverse and hence
`s * star s = 1`, contradicting properness. -/
theorem isometry_not_isUnit :
    ∀ {A : Type u} [Ring A] [StarRing A] (D : ProperProjectionCompression A),
      ¬ IsUnit D.isometry := by
  intro A _ _ D
  rintro ⟨u, hu⟩
  have hleft : star D.isometry * (u : A) = 1 := by
    rw [hu]
    exact D.star_isometry_mul_isometry
  have hstar : star D.isometry = ((u⁻¹ : Aˣ) : A) := by
    calc
      star D.isometry = star D.isometry * 1 := (mul_one _).symm
      _ = star D.isometry * ((u : A) * ((u⁻¹ : Aˣ) : A)) := by
        rw [Units.mul_inv]
      _ = (star D.isometry * (u : A)) * ((u⁻¹ : Aˣ) : A) := by
        rw [mul_assoc]
      _ = 1 * ((u⁻¹ : Aˣ) : A) := by rw [hleft]
      _ = ((u⁻¹ : Aˣ) : A) := one_mul _
  apply D.isometry_mul_star_ne_one
  calc
    D.isometry * star D.isometry =
        D.isometry * ((u⁻¹ : Aˣ) : A) := by rw [hstar]
    _ = (u : A) * ((u⁻¹ : Aˣ) : A) := by rw [hu]
    _ = 1 := Units.mul_inv u

/-- There is explicitly a nonunit with a left inverse: take `a = s` and
`b = star s`. -/
theorem exists_leftInvertible_not_isUnit (D : ProperProjectionCompression A) :
    ∃ a b : A, b * a = 1 ∧ ¬ IsUnit a :=
  ⟨D.isometry, star D.isometry,
    D.star_isometry_mul_isometry, D.isometry_not_isUnit⟩

/-- A ring containing the compression data is not directly finite (also
called Dedekind finite or von Neumann finite). -/
theorem not_isDedekindFiniteMonoid (D : ProperProjectionCompression A) :
    ¬ IsDedekindFiniteMonoid A := by
  intro hfinite
  letI : IsDedekindFiniteMonoid A := hfinite
  exact D.isometry_mul_star_ne_one
    (mul_eq_one_symm D.star_isometry_mul_isometry)

/-- **Stable-finite projection pinning.**  In a directly finite star ring,
a projection cannot be properly contained in a unitarily conjugate copy of
itself.  The two absorption identities are the ring-theoretic form of
`p ≤ u p u⋆`.

This is the algebraic core of the norm-corona pinning step: stable finiteness
supplies direct finiteness, while the Kazhdan fixed-space argument supplies
the absorption identities. -/
theorem unitary_conjugate_eq_of_absorbs [IsDedekindFiniteMonoid A]
    {p u : A}
    (p_star : star p = p)
    (p_mul_p : p * p = p)
    (u_star_mul : star u * u = 1)
    (u_mul_star : u * star u = 1)
    (p_mul_conjugate : p * (u * p * star u) = p)
    (conjugate_mul_p : (u * p * star u) * p = p) :
    u * p * star u = p := by
  by_contra conjugate_ne
  let D : ProperProjectionCompression A :=
    { p := p
      u := u
      p_star := p_star
      p_mul_p := p_mul_p
      u_star_mul := u_star_mul
      u_mul_star := u_mul_star
      p_mul_conjugate := p_mul_conjugate
      conjugate_mul_p := conjugate_mul_p
      conjugate_ne := conjugate_ne }
  exact D.not_isDedekindFiniteMonoid inferInstance

/-- In particular the ambient ring is not stably finite. -/
theorem not_isStablyFiniteRing :
    ∀ {A : Type u} [Ring A] [StarRing A] (_D : ProperProjectionCompression A),
      ¬ IsStablyFiniteRing A := by
  intro A _ _ D hstable
  letI : IsStablyFiniteRing A := hstable
  exact D.not_isDedekindFiniteMonoid inferInstance

/-- No injective multiplicative unital map can send the compression algebra
into a directly finite monoid.  This is the exact algebraic embedding
obstruction used for matrix coronas. -/
theorem no_injective_monoidHom_to_dedekindFinite
    (D : ProperProjectionCompression A)
    {B : Type*} [MulOneClass B] [IsDedekindFiniteMonoid B]
    (f : A →* B) : ¬ Function.Injective f := by
  intro hf
  haveI : IsDedekindFiniteMonoid A :=
    IsDedekindFiniteMonoid.of_injective f hf
  exact D.not_isDedekindFiniteMonoid inferInstance

/-- A C-star algebra carrying a proper projection compression cannot admit a
faithful tracial state. -/
theorem no_faithfulTracialState :
    ∀ {B : Type*} [CStarAlgebra B] (_D : ProperProjectionCompression B),
      ¬ Nonempty (FaithfulTracialState B) := by
  intro B _ D
  rintro ⟨τ⟩
  exact D.isometry_mul_star_ne_one
    (τ.mul_star_eq_one_of_star_mul_eq_one D.star_isometry_mul_isometry)

end ProperProjectionCompression

end

end GroupApproximation
