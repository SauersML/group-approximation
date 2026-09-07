import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# Purely infinite simple rings, as printed

`non_mf_groups_exist.tex`, the paragraph preceding Theorem
`thm:mf-quotient-units`:

> Two idempotents `e, f` of a ring are *equivalent* if `e = xy` and `f = yx`
> for some `x, y`; an idempotent `e` is *infinite* if `e = f + g` for orthogonal
> idempotents `f, g` with `f` equivalent to `e` and `g ≠ 0`; and a simple ring
> is *purely infinite* if every nonzero right ideal contains an infinite
> idempotent (Ara--Goodearl--Pardo, Definitions 1.2).

This module carries those three definitions and the elementary facts about them
that the printed proof uses without citation.

## The right-ideal clause, in element form

`IsPurelyInfiniteSimpleRing` states the last clause as: every nonzero `a` has
`aR` containing an infinite idempotent.  That is equivalent to the printed
"every nonzero right ideal contains an infinite idempotent" and avoids
introducing right ideals over a noncommutative ring:

* a nonzero right ideal contains some `a ≠ 0`, and then `aR` is inside it;
* conversely `aR` is itself a nonzero right ideal when `a ≠ 0`, since `a ∈ aR`
  in a unital ring.

## Relation to the predicate already in the tree

`Manuscript.OneSidedMFRadical.IsPurelyInfiniteSimpleUnitalRing` names the same
class of rings by a different definition --- simple, not a division ring, and
every nonzero element sandwiching to `1`.  For a unital simple ring the two
agree, but that equivalence is a theorem of Ara--Goodearl--Pardo and not a
rewriting, so neither predicate is stated in terms of the other here.  Nothing
in the printed proof of `thm:mf-quotient-units` needs the bridge: pure
infiniteness enters it only through simplicity and through AGP Proposition 1.5,
which is quoted as a named input.
-/

namespace GroupApproximation
namespace MFQuotientUnits

variable {R : Type*} [Ring R]

/-! ### Equivalent idempotents -/

/-- **Printed:** two idempotents `e, f` are *equivalent* if `e = xy` and
`f = yx` for some `x, y`.

The definition is stated for arbitrary elements, exactly as printed; the two
displayed equations already force `e` and `f` to be idempotent whenever
`xyx = x`, and the printed proof only ever applies it to idempotents. -/
def IsEquivalentIdempotent (R : Type*) [Ring R] (e f : R) : Prop :=
  ∃ x y : R, e = x * y ∧ f = y * x

theorem IsEquivalentIdempotent.symm {e f : R}
    (h : IsEquivalentIdempotent R e f) : IsEquivalentIdempotent R f e := by
  obtain ⟨x, y, hx, hy⟩ := h
  exact ⟨y, x, hy, hx⟩

theorem isEquivalentIdempotent_refl (e : R) (he : IsIdempotentElem e) :
    IsEquivalentIdempotent R e e :=
  ⟨e, e, he.symm, he.symm⟩

/-- A nonzero idempotent is equivalent only to nonzero elements: from `e = xy`
and `f = yx` with `f = 0` one gets `e = e * e = x * (y * x) * y = 0`. -/
theorem ne_zero_of_isEquivalentIdempotent {e f : R} (he : IsIdempotentElem e)
    (hne : e ≠ 0) (h : IsEquivalentIdempotent R e f) : f ≠ 0 := by
  obtain ⟨x, y, hx, hy⟩ := h
  intro hf
  apply hne
  have hzero : y * x = 0 := by rw [← hy, hf]
  calc e = e * e := he.symm
    _ = (x * y) * (x * y) := by rw [hx]
    _ = x * ((y * x) * y) := by simp only [mul_assoc]
    _ = 0 := by rw [hzero, zero_mul, mul_zero]

/-! ### Infinite idempotents -/

/-- **Printed:** an idempotent `e` is *infinite* if `e = f + g` for orthogonal
idempotents `f, g` with `f` equivalent to `e` and `g ≠ 0`. -/
def IsInfiniteIdempotent (R : Type*) [Ring R] (e : R) : Prop :=
  ∃ f g : R, IsIdempotentElem f ∧ IsIdempotentElem g ∧
    f * g = 0 ∧ g * f = 0 ∧ e = f + g ∧ IsEquivalentIdempotent R e f ∧ g ≠ 0

theorem IsInfiniteIdempotent.ne_zero {e : R} (h : IsInfiniteIdempotent R e) :
    e ≠ 0 := by
  obtain ⟨f, g, -, hg, -, hgf, hsum, -, hgne⟩ := h
  intro hzero
  apply hgne
  have hgsum : g * e = g * f + g * g := by rw [hsum, mul_add]
  rw [hgf, zero_add, hg] at hgsum
  rw [hzero, mul_zero] at hgsum
  exact hgsum.symm

/-- The infinite half of the decomposition is itself equivalent to `e`, which
is the form in which the printed proof reads "`f` equivalent to `e`". -/
theorem IsInfiniteIdempotent.exists_proper_equivalent {e : R}
    (h : IsInfiniteIdempotent R e) :
    ∃ f : R, IsIdempotentElem f ∧ IsEquivalentIdempotent R e f ∧ f ≠ e := by
  obtain ⟨f, g, hf, hg, hfg, hgf, hsum, hequiv, hgne⟩ := h
  refine ⟨f, hf, hequiv, ?_⟩
  intro hfe
  apply hgne
  rw [hfe] at hsum
  have h2 : e + 0 = e + g := by
    rw [add_zero]
    exact hsum
  exact (add_left_cancel h2).symm

/-! ### Purely infinite simple rings -/

/-- **Printed (Ara--Goodearl--Pardo, Definitions 1.2):** a simple ring is
*purely infinite* if every nonzero right ideal contains an infinite idempotent.

The right-ideal clause is stated in element form; see the module docstring for
why that is the same condition. -/
def IsPurelyInfiniteSimpleRing (R : Type*) [Ring R] : Prop :=
  IsSimpleRing R ∧
    ∀ a : R, a ≠ 0 → ∃ e r : R, e = a * r ∧ IsIdempotentElem e ∧
      IsInfiniteIdempotent R e

theorem IsPurelyInfiniteSimpleRing.isSimpleRing
    (h : IsPurelyInfiniteSimpleRing R) : IsSimpleRing R := h.1

theorem IsPurelyInfiniteSimpleRing.exists_infiniteIdempotent
    (h : IsPurelyInfiniteSimpleRing R) {a : R} (ha : a ≠ 0) :
    ∃ e r : R, e = a * r ∧ IsIdempotentElem e ∧ IsInfiniteIdempotent R e :=
  h.2 a ha

/-- A purely infinite simple ring contains an infinite idempotent outright:
apply the definition to `a = 1`. -/
theorem IsPurelyInfiniteSimpleRing.exists_infiniteIdempotent_of_nontrivial
    [Nontrivial R] (h : IsPurelyInfiniteSimpleRing R) :
    ∃ e : R, IsIdempotentElem e ∧ IsInfiniteIdempotent R e := by
  obtain ⟨e, r, -, he, hinf⟩ := h.exists_infiniteIdempotent (one_ne_zero (α := R))
  exact ⟨e, he, hinf⟩

/-! ### The order on idempotents -/

/-- `e ≤ P` for idempotents, in the form the printed proof uses it: `e` is
absorbed by `P` on both sides. -/
def IdempotentLE (e P : R) : Prop := P * e = e ∧ e * P = e

theorem idempotentLE_refl (e : R) (he : IsIdempotentElem e) :
    IdempotentLE e e := ⟨he, he⟩

theorem IdempotentLE.trans {e f g : R} (hef : IdempotentLE e f)
    (hfg : IdempotentLE f g) : IdempotentLE e g := by
  constructor
  · calc g * e = g * (f * e) := by rw [hef.1]
      _ = (g * f) * e := by rw [mul_assoc]
      _ = f * e := by rw [hfg.1]
      _ = e := hef.1
  · calc e * g = (e * f) * g := by rw [hef.2]
      _ = e * (f * g) := by rw [mul_assoc]
      _ = e * f := by rw [hfg.2]
      _ = e := hef.2

/-- The complement of an idempotent below another is again idempotent and
orthogonal to it, which is the step the printed proof takes when it writes
`1 - P + θ(A)`. -/
theorem isIdempotentElem_sub {e P : R} (hP : IsIdempotentElem P)
    (he : IsIdempotentElem e) (hle : IdempotentLE e P) :
    IsIdempotentElem (P - e) := by
  have hexp : (P - e) * (P - e) = P * P - P * e - e * P + e * e := by
    noncomm_ring
  rw [IsIdempotentElem, hexp, hP, he, hle.1, hle.2]
  abel

theorem sub_mul_self_eq_zero {e P : R} (he : IsIdempotentElem e)
    (hle : IdempotentLE e P) : (P - e) * e = 0 := by
  rw [sub_mul, hle.1, he]
  abel

theorem mul_sub_self_eq_zero {e P : R} (he : IsIdempotentElem e)
    (hle : IdempotentLE e P) : e * (P - e) = 0 := by
  rw [mul_sub, hle.2, he]
  abel

end MFQuotientUnits
end GroupApproximation
