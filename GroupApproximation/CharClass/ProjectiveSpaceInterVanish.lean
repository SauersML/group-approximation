import GroupApproximation.CharClass.LerayHirschChart

/-!
# The intersection of the projective cover carries no even classes

The intersection of the chart with the punctured space is an odd sphere, so it has
cohomology only in degrees `0` and `2d+1`.  In particular every class of positive
even degree on it vanishes, which is what makes the tautological class and all its
positive powers die there.

That is the fact the projective-factor Künneth needs, and it needs **no commuting
square**: the vanishing is a property of the intersection alone, so any class of
that degree is zero, however it was obtained.  For a product with another factor
the same follows by factoring the projection, since the projection to the
projective factor restricted to the intersection is literally the projection
followed by the inclusion.

## Main declarations

* `eq_zero_interSpace` — the sphere's vanishing, in element form.
* `eq_zero_interSpace_two` — degree two, the tautological class itself.
* `eq_zero_interSpace_even` — **every positive even degree**, so every positive
  power of the tautological class.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace CPn

open CategoryTheory

noncomputable section

/-- Every class on the intersection outside degrees `0` and `2d+1` vanishes. -/
theorem eq_zero_interSpace (d k : ℕ) (hk0 : k ≠ 0) (hk : k ≠ 2 * d + 1)
    (a : Hmod2 (interSpace d) k) : a = 0 :=
  (hasSphereCohomology_interSpace d).2.2 k hk0 hk a

/-- **Every degree-two class on the intersection vanishes**, since an odd sphere has
none.  This is what kills the tautological class there. -/
theorem eq_zero_interSpace_two (d : ℕ) (a : Hmod2 (interSpace d) 2) : a = 0 :=
  eq_zero_interSpace d 2 (by omega) (by omega) a

/-- **Every class of positive even degree on the intersection vanishes.**  The
degree `2i` is even and `2d+1` is odd, so they never meet, which is why no
hypothesis relating `i` to `d` appears.  This kills every positive power of the
tautological class on the intersection. -/
theorem eq_zero_interSpace_even (d i : ℕ) (hi : i ≠ 0)
    (a : Hmod2 (interSpace d) (2 * i)) : a = 0 :=
  eq_zero_interSpace d (2 * i) (by omega) (by omega) a

/-- The same, as a zero object. -/
theorem isZero_interSpace_even (d i : ℕ) (hi : i ≠ 0) :
    Limits.IsZero (Hmod2 (interSpace d) (2 * i)) :=
  isZero_of_forall_eq_zero (eq_zero_interSpace_even d i hi)

end

end CPn
end CharClass
end GroupApproximation
