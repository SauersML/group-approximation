import GroupApproximation.Algebra.CornerRing
import GroupApproximation.Meta.AxiomGuard

/-!
# A corner unit extends to a unit of the whole ring

`non_mf_groups_exist.tex`'s `eq:corner-units` display, for a ring isomorphism
`θ : M_m(eRe) → PRP` and `A ∈ EL_m(eRe)`, packages `θ(A)` as the *unit*
`1 - P + θ(A)` of `R`.  This module isolates the piece of that packaging that
has nothing to do with `θ`, `EL_m`, or `eRe`: for **any** idempotent `P` and
**any** unit `z` of the corner `Corner R P hP`, `1 - P + z` is a unit of `R`,
with inverse `1 - P + z⁻¹`.

## Why this holds

For `a, b` in the corner (so `P * a = a = a * P`, likewise `b`),

    `(1 - P + a) * (1 - P + b) = (1 - P) * (1 - P) + (1 - P) * b + a * (1 - P) + a * b`
      `= (1 - P) + 0 + 0 + a * b = 1 - P + a * b`,

using `(1-P)*(1-P) = 1-P` (idempotent), `(1-P)*b = b - P*b = 0`, and
`a*(1-P) = a - a*P = 0`.  So `a ↦ 1 - P + a` is a monoid homomorphism from the
corner's multiplicative monoid into `R`'s (it sends the corner's own unit `P`
to `1`), and `Units.map` turns that into a group homomorphism on units.
-/

namespace GroupApproximation
namespace MFQuotientUnits

variable {R : Type*} [Ring R]

/-- **`a ↦ 1 - P + a`, as a monoid homomorphism from the corner.**  Sends the
corner's own unit `P` to `1`, and is multiplicative on corner elements because
`P` absorbs on both sides. -/
def oneSubAddCornerHom (P : R) (hP : IsIdempotentElem P) :
    Corner R P hP →* R where
  toFun a := 1 - P + (a : R)
  map_one' := by simp
  map_mul' a b := by
    have hPa : P * (a : R) = (a : R) := a.2.1
    have haP : (a : R) * P = (a : R) := a.2.2
    have hPb : P * (b : R) = (b : R) := b.2.1
    show 1 - P + ((a : R) * (b : R)) = (1 - P + (a : R)) * (1 - P + (b : R))
    have h1 : (1 - P + (a : R)) * (1 - P + (b : R))
        = (1 - P) * (1 - P) + (1 - P) * (b : R) + (a : R) * (1 - P)
          + (a : R) * (b : R) := by noncomm_ring
    rw [h1]
    have h2 : (1 - P) * (1 - P) = 1 - P := by
      have := IsIdempotentElem.one_sub hP
      exact this
    have h3 : (1 - P) * (b : R) = 0 := by
      have : (1 - P) * (b : R) = (b : R) - P * (b : R) := by noncomm_ring
      rw [this, hPb, sub_self]
    have h4 : (a : R) * (1 - P) = 0 := by
      have : (a : R) * (1 - P) = (a : R) - (a : R) * P := by noncomm_ring
      rw [this, haP, sub_self]
    rw [h2, h3, h4]
    abel

/-- **A corner unit extends to a unit of `R`.** -/
def unitOfCornerUnit (P : R) (hP : IsIdempotentElem P) :
    (Corner R P hP)ˣ →* Rˣ :=
  Units.map (oneSubAddCornerHom P hP)

@[simp] theorem coe_unitOfCornerUnit (P : R) (hP : IsIdempotentElem P)
    (z : (Corner R P hP)ˣ) :
    ((unitOfCornerUnit P hP z : Rˣ) : R) = 1 - P + ((z : Corner R P hP) : R) := rfl

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.unitOfCornerUnit
