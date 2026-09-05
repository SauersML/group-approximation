import GroupApproximation.AlgTop.ChernPowerSums

/-!
# Naturality of a total Chern class in the coefficient ring

At the level of `GroupApproximation.AlgTop.TotalChern`, "natural under pullback"
becomes "natural in the coefficient ring": a ring homomorphism `f : A →+* B` of
cohomology rings carries a total Chern class over `A` to one over `B`, and every
piece of the API commutes with it.

The case the STW Problem LIX parity chain actually uses is the *integral-to-
rational* comparison `ι : S →+* R`.  The manuscript's remark that "the integral
cohomology of `S¹ × S⁵ × Y` is torsion-free, so the calculation in rational
cohomology identifies the integral coefficients uniquely" is exactly injectivity
of such an `ι`; this file supplies the transport in the other direction, so that
a statement proved over `R` can be pulled back along `ι`.

Because `TotalChern.map f` is a **monoid homomorphism of groups**, it
automatically commutes with inversion and division — so the total Chern class of
a virtual difference transports without a separate argument, and in particular
`W / V` maps to `map f W / map f V`.

## Main declarations

* `TotalChern.map` — the induced map, as a `MonoidHom`.
* `TotalChern.chernClass_map`, `TotalChern.map_line`, `TotalChern.RankLE.map`.
* `TotalChern.newtonSeries_map`, `TotalChern.powerSum_map` — the power sums are
  natural too, because `X`, the formal derivative and the inverse all are.
-/

namespace GroupApproximation
namespace AlgTop
namespace TotalChern

open scoped PowerSeries

noncomputable section

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The underlying function of `TotalChern.map`: push the coefficients forward. -/
def mapFun (f : A →+* B) (c : TotalChern A) : TotalChern B :=
  ⟨PowerSeries.map f c.series, by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, c.constantCoeff_series, map_one]⟩

@[simp] theorem mapFun_series (f : A →+* B) (c : TotalChern A) :
    (mapFun f c).series = PowerSeries.map f c.series := rfl

/-- A ring homomorphism of coefficient rings carries total Chern classes to total
Chern classes, multiplicatively — so it also commutes with the inverse and the
quotient, which is what a virtual class is. -/
def map (f : A →+* B) : TotalChern A →* TotalChern B where
  toFun := mapFun f
  map_one' := ext (by simp)
  map_mul' _ _ := ext (by simp)

@[simp] theorem map_series (f : A →+* B) (c : TotalChern A) :
    (map f c).series = PowerSeries.map f c.series := rfl

@[simp] theorem chernClass_map (f : A →+* B) (c : TotalChern A) (k : ℕ) :
    (map f c).chernClass k = f (c.chernClass k) := by
  rw [chernClass, chernClass, map_series, PowerSeries.coeff_map]

theorem map_line (f : A →+* B) (a : A) : map f (line a) = line (f a) := by
  refine ext ?_
  rw [map_series, line_series, line_series, map_add, map_one, map_mul, PowerSeries.map_C,
    PowerSeries.map_X]

theorem RankLE.map {f : A →+* B} {c : TotalChern A} {n : ℕ} (h : c.RankLE n) :
    (TotalChern.map f c).RankLE n := by
  intro k hk
  rw [chernClass_map, h k hk, map_zero]

theorem newtonSeries_map (f : A →+* B) (c : TotalChern A) :
    newtonSeries (map f c) = PowerSeries.map f (newtonSeries c) := by
  have hderiv : PowerSeries.derivativeFun (PowerSeries.map f c.series)
      = PowerSeries.map f (PowerSeries.derivativeFun c.series) := by
    ext n
    rw [PowerSeries.coeff_derivativeFun, PowerSeries.coeff_map, PowerSeries.coeff_map,
      PowerSeries.coeff_derivativeFun, map_mul, map_add, map_natCast, map_one]
  have hinv : (map f c)⁻¹ = map f c⁻¹ := (map_inv (map f) c).symm
  rw [newtonSeries, newtonSeries, hinv]
  simp only [map_series]
  rw [hderiv, map_mul, map_mul, PowerSeries.map_X]

@[simp] theorem powerSum_map (f : A →+* B) (c : TotalChern A) (q : ℕ) :
    (map f c).powerSum q = f (c.powerSum q) := by
  rw [powerSum, powerSum, newtonSeries_map, PowerSeries.coeff_map, map_mul, map_pow,
    map_neg, map_one]

end

end TotalChern
end AlgTop
end GroupApproximation
