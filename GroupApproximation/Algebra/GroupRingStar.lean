import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Unitary

/-!
# The involution on the group ring

The appendix defines `Cmax(H)` as a completion of the group ring `ℂ[H]`, which
presupposes the `*`-algebra structure on `ℂ[H]`:

  `(Σ_g c_g · g)^* = Σ_g conj(c_g) · g⁻¹`.

At the pinned Mathlib (`905b95818eb3`) `MonoidAlgebra` carries **no** star: there
is no `Star` instance anywhere under `Mathlib/Algebra/MonoidAlgebra/`, no
`Mathlib/Algebra/Star/MonoidAlgebra.lean`, and nothing in `Mathlib/Algebra/Star/`
or `Mathlib/Data/Finsupp/` that supplies one.  This module builds it.

## Contents

* `instStar`, `instStarRing` --- the involution and the `*`-ring structure.
  `InvolutiveStar` and `StarMul` come with `StarRing` by inheritance, so they are
  not declared separately; declaring them too would put two paths to the same
  `Star` instance in the graph.
* `instStarModule` --- `star (r • x) = star r • star x`.
* `lift_star` and `starLift` --- a `*`-representation of `G` in a `*`-algebra
  extends to a `*`-algebra homomorphism from the group ring, and `unitaryLift`
  is the case of a unitary representation `G →* unitary B`.

Everything is stated for an arbitrary coefficient `*`-ring rather than `ℂ`
alone.  No commutativity of the coefficients is needed for the involution
itself: anti-multiplicativity of `star` on `R` is exactly what compensates for
the order reversal in `(gh)⁻¹ = h⁻¹g⁻¹`.  `ℂ` instantiates every statement here.

## The shape of the construction

`star` is defined coefficientwise, so that

  `(star x).coeff g = star (x.coeff g⁻¹)`

holds by `rfl` (`coeff_star`), and every additive fact --- additivity,
involutivity, the behaviour on `0` --- is then a one-line coefficient
computation.  This follows `Kazhdan/ExactHodgeCertificate.adjoint`, which is the
same construction over `ℚ` (where there is nothing to conjugate) and is already
green in this development.

Anti-multiplicativity is the one law that is not coefficientwise, and it is
proved the only way it can be: reduce to `single`s by linearity in each
argument, where it is `(gh)⁻¹ = h⁻¹g⁻¹` together with `star (cd) = star d star c`.
-/

namespace GroupApproximation
namespace GroupRingStar

open scoped MonoidAlgebra

universe u v w

/-! ## The involution -/

section Involution

variable {R : Type u} {G : Type v} [Semiring R] [StarRing R] [Group G]

/-- The involution of the group ring: `(Σ c_g g)^* = Σ (star c_g) g⁻¹`.  It is
defined coefficientwise, by inverting the domain and conjugating the values, so
that `coeff_star` below is definitional. -/
noncomputable instance instStar : Star (MonoidAlgebra R G) where
  star x :=
    .ofCoeff (Finsupp.mapRange star (star_zero R) (x.coeff.equivMapDomain (Equiv.inv G)))

/-- The defining property: the coefficient of `star x` at `g` is the conjugate
of the coefficient of `x` at `g⁻¹`. -/
@[simp] theorem coeff_star (x : MonoidAlgebra R G) (g : G) :
    (star x).coeff g = star (x.coeff g⁻¹) := rfl

/-- The involution on a single term.

Proved coefficientwise rather than by rewriting the definition: the `Equiv.inv`
inside the definition does not reduce at `rw`'s reducible transparency, so a
route through `Finsupp.equivMapDomain_single` would end on a goal that `rw`
closes or does not close depending on that transparency.  Reading both sides at
a point avoids the question. -/
@[simp] theorem star_single (g : G) (c : R) :
    star (MonoidAlgebra.single g c) = MonoidAlgebra.single g⁻¹ (star c) := by
  ext h
  rw [coeff_star, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single]
  by_cases hgh : g⁻¹ = h
  · rw [← hgh, inv_inv, Finsupp.single_eq_same, Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne (fun hcon => hgh (by rw [← hcon, inv_inv])),
      Finsupp.single_eq_of_ne (Ne.symm hgh), star_zero]

theorem star_zero' : star (0 : MonoidAlgebra R G) = 0 := by
  ext g
  simp

theorem star_add' (x y : MonoidAlgebra R G) : star (x + y) = star x + star y := by
  ext g
  simp

theorem star_involutive' :
    Function.Involutive (star : MonoidAlgebra R G → MonoidAlgebra R G) := by
  intro x
  ext g
  simp

/-- Anti-multiplicativity, with the left factor a single term.  This is the
inner half of the induction: `star` is additive, so both sides are additive in
the right factor, and on a pair of single terms the statement is
`(gh)⁻¹ = h⁻¹g⁻¹` together with anti-multiplicativity in `R`. -/
theorem star_single_mul (g : G) (c : R) (y : MonoidAlgebra R G) :
    star (MonoidAlgebra.single g c * y) = star y * star (MonoidAlgebra.single g c) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => rw [mul_zero, star_zero', zero_mul]
  | add a b ha hb => rw [mul_add, star_add', ha, hb, star_add', add_mul]
  | single h d =>
      rw [MonoidAlgebra.single_mul_single, star_single, star_single, star_single,
        MonoidAlgebra.single_mul_single, mul_inv_rev, star_mul]

/-- **The involution is anti-multiplicative.** -/
theorem star_mul' (x y : MonoidAlgebra R G) : star (x * y) = star y * star x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [zero_mul, star_zero', mul_zero]
  | add a b ha hb => rw [add_mul, star_add', ha, hb, star_add', mul_add]
  | single g c => exact star_single_mul g c y

/-- **The group ring is a `*`-ring.**  `InvolutiveStar` and `StarMul` are the
parents of `StarRing`, so they come with this instance; the `Star` parent is the
one declared above. -/
noncomputable instance instStarRing : StarRing (MonoidAlgebra R G) where
  star_involutive := star_involutive'
  star_mul := star_mul'
  star_add := star_add'

end Involution

/-! ## Compatibility with the scalars -/

section Scalars

variable {R : Type u} {G : Type v} [CommSemiring R] [StarRing R] [Group G]

/-- **`star` is conjugate-linear.**  Over `ℂ` this is the statement that
`(c · x)^* = conj(c) · x^*`. -/
instance instStarModule : StarModule R (MonoidAlgebra R G) where
  star_smul r x := by
    ext g
    rw [coeff_star, MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_smul_apply,
      coeff_star, smul_eq_mul, smul_eq_mul, star_mul, mul_comm]

end Scalars

/-! ## Lifting a `*`-representation

`MonoidAlgebra.lift` extends a monoid homomorphism `G →* B` to an algebra
homomorphism on the group ring.  If the homomorphism is a `*`-representation ---
`star (f g) = f g⁻¹`, which is exactly unitarity of the values --- then the
extension is a `*`-algebra homomorphism. -/

section Lift

variable {R : Type u} {G : Type v} {B : Type w}
variable [CommSemiring R] [StarRing R] [Group G]
variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

/-- **The lift of a `*`-representation commutes with the involution.**  This is
the mathematical content of `starLift`, kept separate so that it can be used
without building the bundled homomorphism. -/
theorem lift_star (f : G →* B) (hf : ∀ g : G, star (f g) = f g⁻¹)
    (x : MonoidAlgebra R G) :
    MonoidAlgebra.lift R B G f (star x) = star (MonoidAlgebra.lift R B G f x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [star_zero', map_zero, star_zero]
  | add a b ha hb => rw [star_add', map_add, map_add, ha, hb, star_add]
  | single g c =>
      rw [star_single, MonoidAlgebra.lift_single, MonoidAlgebra.lift_single,
        star_smul, hf]

/-- **A `*`-representation of `G` extends to a `*`-algebra homomorphism on the
group ring.** -/
noncomputable def starLift (f : G →* B) (hf : ∀ g : G, star (f g) = f g⁻¹) :
    MonoidAlgebra R G →⋆ₐ[R] B :=
  { MonoidAlgebra.lift R B G f with map_star' := lift_star f hf }

@[simp] theorem starLift_single (f : G →* B) (hf : ∀ g : G, star (f g) = f g⁻¹)
    (g : G) (c : R) : starLift f hf (MonoidAlgebra.single g c) = c • f g := by
  show MonoidAlgebra.lift R B G f (MonoidAlgebra.single g c) = c • f g
  exact MonoidAlgebra.lift_single f g c

/-- The inverse of a unitary, read in the ambient ring, is its star.  A local
copy of `Sofic/TorsionSpectralCollapse.unitary_coe_inv`, which this module does
not import because that file sits above it in the layering. -/
theorem coe_unitary_inv {A : Type w} [Monoid A] [StarMul A] (u : unitary A) :
    ((u⁻¹ : unitary A) : A) = star (u : A) := by
  have hba : ((u⁻¹ : unitary A) : A) * (u : A) = 1 := by
    have h0 : (((u⁻¹ * u : unitary A)) : A) = ((1 : unitary A) : A) :=
      congrArg (fun z : unitary A ↦ (z : A)) (inv_mul_cancel u)
    calc ((u⁻¹ : unitary A) : A) * (u : A) =
        (((u⁻¹ * u : unitary A)) : A) := rfl
      _ = ((1 : unitary A) : A) := h0
      _ = 1 := rfl
  exact left_inv_eq_right_inv hba u.prop.2

/-- **The `*`-algebra homomorphism induced by a unitary representation.**  This
is the map the appendix uses to define `Cmax(H)`: every unitary representation
of `H` extends to `ℂ[H]`, compatibly with the involution. -/
noncomputable def unitaryLift (rho : G →* unitary B) : MonoidAlgebra R G →⋆ₐ[R] B :=
  starLift ((unitary B).subtype.comp rho) (fun g => by
    show star ((rho g : B)) = ((rho g⁻¹ : unitary B) : B)
    rw [map_inv, coe_unitary_inv])

@[simp] theorem unitaryLift_single (rho : G →* unitary B) (g : G) (c : R) :
    unitaryLift (R := R) rho (MonoidAlgebra.single g c) = c • (rho g : B) := by
  show MonoidAlgebra.lift R B G ((unitary B).subtype.comp rho)
      (MonoidAlgebra.single g c) = c • (rho g : B)
  exact MonoidAlgebra.lift_single _ g c

end Lift

end GroupRingStar
end GroupApproximation
