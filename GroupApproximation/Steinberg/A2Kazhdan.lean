import GroupApproximation.Steinberg.A2System
import GroupApproximation.PropertyT.A2MagicHilbert
import GroupApproximation.Leavitt.UniversalLeavitt
import Mathlib.Algebra.CharP.Algebra

/-!
# The Steinberg root union is a Kazhdan subset

The generic `A₂` magic-graph theorem applies directly to the Steinberg
presentation.  In positive characteristic every additive root subgroup has
bounded exponent, so the union of the six roots in `St₃(R)` is a genuine
Kazhdan subset.  This is the relative-property-`(T)` half of the direct
Steinberg argument; upgrading the infinite root union to a finite Kazhdan
set is kept separate.
-/

namespace GroupApproximation
namespace SteinbergGroup

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

/-- Powers in a Steinberg root subgroup are additive multiples of the root
coefficient. -/
theorem x_pow (i j : I) (hij : i ≠ j) (a : R) (n : ℕ) :
    x i j hij a ^ n = x i j hij (n • a) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, x_mul, succ_nsmul]

/-- In characteristic `p`, every Steinberg root element has exponent
dividing `p`. -/
theorem x_pow_char (p : ℕ) [CharP R p]
    (i j : I) (hij : i ≠ j) (a : R) :
    x i j hij a ^ p = 1 := by
  rw [x_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, x_zero]

/-- Every element of a Steinberg root subgroup has exponent dividing the
characteristic. -/
theorem rootSubgroup_pow_char (p : ℕ) [CharP R p]
    (i j : I) (hij : i ≠ j) (g : SteinbergGroup I R)
    (hg : g ∈ rootSubgroup i j hij) :
    g ^ p = 1 := by
  obtain ⟨a, rfl⟩ := hg
  exact x_pow_char p i j hij a

/-- The six Steinberg roots in rank three form a Kazhdan subset over every
ring of positive characteristic. -/
theorem exists_rootSet_isKazhdan
    (R : Type*) [Ring R] (p : ℕ) (hp : 0 < p) [CharP R p] :
    ∃ kappa : ℝ,
      IsKazhdanSubset
        (SteinbergGroup (Fin 3) R)
        (a2System (R := R)).rootSet kappa := by
  apply A2MagicHilbert.exists_rootSet_isKazhdan
    (a2System (R := R)) p hp
  intro i j hij g hg
  exact rootSubgroup_pow_char p i j hij g hg

/-- In particular, the root union of the concrete binary-Leavitt
`St₃` is a Kazhdan subset. -/
theorem binaryLeavitt_exists_rootSet_isKazhdan :
    ∃ kappa : ℝ,
      IsKazhdanSubset
        (SteinbergGroup (Fin 3) UniversalLeavitt.BinaryLeavittAlgebra)
        (a2System
          (R := UniversalLeavitt.BinaryLeavittAlgebra)).rootSet kappa := by
  letI : CharP UniversalLeavitt.BinaryLeavittAlgebra 2 :=
    charP_of_injective_algebraMap (R := ZMod 2)
      (RingHom.injective
        (algebraMap (ZMod 2) UniversalLeavitt.BinaryLeavittAlgebra)) 2
  exact exists_rootSet_isKazhdan
    UniversalLeavitt.BinaryLeavittAlgebra 2 (by omega)

end SteinbergGroup
end GroupApproximation
