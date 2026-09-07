import Mathlib.RingTheory.NonUnitalSubring.Basic
import Mathlib.Data.Countable.Basic
import GroupApproximation.Algebra.PurelyInfiniteSimpleRing

/-!
# The corner `eRe` of a ring at an idempotent

`non_mf_groups_exist.tex`, the proof of Theorem `thm:mf-quotient-units`, which
speaks of `eRe`, of `M_m(eRe)`, and of `EL_m(eRe)` throughout:

> every nonzero idempotent `e` of `R` is infinite, so `eRe` contains `s, t` with
> `ts = e ≠ st`, and `eRe` is simple …
> if `e` and `P` are nonzero idempotents and `θ : M_m(eRe) → PRP` is a ring
> isomorphism …

The corner is not a subring of `R`: it has a different unit, `e` rather than
`1`.  So it is built here as a `NonUnitalSubring` — which is what `eRe` is
inside `R` — and then given its own `One` and `Ring` structure on top, exactly
the ladder `Analysis.LIXCornerAlgebra` uses for the C⋆-corner at a projection.
`Function.Injective.ring` cannot be used for the same reason: it would demand
that the inclusion send `1` to `1`.

Kept deliberately small: the non-unital subring, the unit, the `Ring` instance,
the coercion lemmas that let a statement about `eRe` be read back in `R`,
countability inherited from `R`, and the inclusion as a non-unital ring
homomorphism.  Everything else the printed proof needs about corners --- that
they are simple, and that they carry a one-sided inverse pair --- is
Ara--Goodearl--Pardo Proposition 1.5 and is quoted as a named input rather than
proved here.
-/

namespace GroupApproximation
namespace MFQuotientUnits

variable {R : Type*} [Ring R]

/-! ### The corner as a non-unital subring -/

/-- **The corner `eRe`**, as a non-unital subring of `R`.

Closure under the ring operations does not use idempotency of `e`; the
hypothesis is carried so that it appears in the type `Corner R e he`, where the
`One` and `Ring` instances below do need it. -/
def cornerNonUnitalSubring (e : R) (_he : IsIdempotentElem e) : NonUnitalSubring R where
  carrier := {x : R | e * x = x ∧ x * e = x}
  zero_mem' := ⟨mul_zero e, zero_mul e⟩
  add_mem' := fun ha hb => ⟨by
      show e * (_ + _) = _
      rw [mul_add, ha.1, hb.1], by
      show (_ + _) * e = _
      rw [add_mul, ha.2, hb.2]⟩
  neg_mem' := fun ha => ⟨by
      show e * (-_) = _
      rw [mul_neg, ha.1], by
      show (-_) * e = _
      rw [neg_mul, ha.2]⟩
  mul_mem' := fun ha hb => ⟨by
      show e * (_ * _) = _
      rw [← mul_assoc, ha.1], by
      show (_ * _) * e = _
      rw [mul_assoc, hb.2]⟩

theorem mem_cornerNonUnitalSubring_iff {e : R} {he : IsIdempotentElem e} {x : R} :
    x ∈ cornerNonUnitalSubring e he ↔ e * x = x ∧ x * e = x := Iff.rfl

/-- The idempotent itself lies in its corner: this is the unit. -/
theorem self_mem_cornerNonUnitalSubring (e : R) (he : IsIdempotentElem e) :
    e ∈ cornerNonUnitalSubring e he := ⟨he, he⟩

/-- **`eRe`**, as a type. -/
abbrev Corner (R : Type*) [Ring R] (e : R) (he : IsIdempotentElem e) : Type _ :=
  ↥(cornerNonUnitalSubring e he)

/-! ### The unit and the ring structure -/

instance cornerOne (e : R) (he : IsIdempotentElem e) : One (Corner R e he) :=
  ⟨⟨e, self_mem_cornerNonUnitalSubring e he⟩⟩

@[simp] theorem coe_cornerOne (e : R) (he : IsIdempotentElem e) :
    ((1 : Corner R e he) : R) = e := rfl

@[simp] theorem coe_corner_mul (e : R) (he : IsIdempotentElem e)
    (a b : Corner R e he) : ((a * b : Corner R e he) : R) = (a : R) * (b : R) :=
  rfl

@[simp] theorem coe_corner_add (e : R) (he : IsIdempotentElem e)
    (a b : Corner R e he) : ((a + b : Corner R e he) : R) = (a : R) + (b : R) :=
  rfl

@[simp] theorem coe_corner_neg (e : R) (he : IsIdempotentElem e)
    (a : Corner R e he) : ((-a : Corner R e he) : R) = -(a : R) := rfl

@[simp] theorem coe_corner_zero (e : R) (he : IsIdempotentElem e) :
    ((0 : Corner R e he) : R) = 0 := rfl

theorem corner_ext {e : R} {he : IsIdempotentElem e} {a b : Corner R e he}
    (h : (a : R) = (b : R)) : a = b := Subtype.ext h

/-- **The corner is a ring with unit `e`.**  Everything except the unit comes
from the non-unital subring; the two unit laws are exactly the two defining
equations of the corner. -/
instance cornerRing (e : R) (he : IsIdempotentElem e) : Ring (Corner R e he) :=
  { (inferInstance : NonUnitalRing (Corner R e he)) with
    one := (1 : Corner R e he)
    one_mul := fun a => Subtype.ext (show e * (a : R) = (a : R) from a.2.1)
    mul_one := fun a => Subtype.ext (show (a : R) * e = (a : R) from a.2.2) }

/-! ### Transport from the ambient ring -/

instance cornerCountable {S : Type*} [Ring S] [Countable S] (e : S)
    (he : IsIdempotentElem e) : Countable (Corner S e he) := Subtype.countable

/-- The inclusion `eRe → R`, a homomorphism of non-unital rings.  It is not
a ring homomorphism: it sends the unit `e` of the corner to `e`, not to `1`. -/
def cornerInclusion (e : R) (he : IsIdempotentElem e) :
    Corner R e he →ₙ+* R :=
  NonUnitalSubringClass.subtype (cornerNonUnitalSubring e he)

@[simp] theorem cornerInclusion_apply (e : R) (he : IsIdempotentElem e)
    (a : Corner R e he) : cornerInclusion e he a = (a : R) := rfl

theorem cornerInclusion_injective (e : R) (he : IsIdempotentElem e) :
    Function.Injective (cornerInclusion e he) := Subtype.val_injective

/-- A nonzero idempotent has a nontrivial corner: the unit `e` is not `0`. -/
theorem corner_nontrivial (e : R) (he : IsIdempotentElem e) (hne : e ≠ 0) :
    Nontrivial (Corner R e he) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro hcon
  exact hne (by simpa using congrArg (fun z : Corner R e he ↦ (z : R)) hcon)

end MFQuotientUnits
end GroupApproximation
