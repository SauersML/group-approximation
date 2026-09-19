import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2Finite
import Mathlib.FieldTheory.Finite.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Steinberg symbols over every finite field are trivial (k2-poly piece H.field, first step)

In Tulenbaev's Horrocks theorem (§4, Cor 4.2 and Prop 4.3; board `k2-poly.md`, piece H), the base
case is the residue field `k` of a local ring. For the local rings of `F_p[s₁..s_k]` this `k` is a
finite field `F_q`, not only `F_p` (the point was raised by pal-q111). The `F_p` inputs on main are:

* symbol triviality, `ElemFP.FieldK2.symbol_eq_one_zmod` (bh-met-15);
* the Bruhat big cell;
* Nagao, `K₂(N, F_p[X]) = 1` (bh-met-94e).

This module generalizes the first of them to every finite field. The argument follows bh-met-15,
with two changes:

* In odd characteristic, the nonsquare pair `u + v = 1` comes from writing a nonsquare `c` as a
  sum of two squares, which holds in every finite field of odd order
  (`FiniteField.exists_root_sum_quadratic`).
* In characteristic `2`, every element is a square, so that argument is unavailable. Instead,
  write `z = s(g, g)` for a generator `g` of `Fˣ`. Then `z² = 1` and
  `z ^ |Fˣ| = s(g^|Fˣ|, g) = s(1, g) = 1`,
  where `|Fˣ| = |F| − 1` is odd. So `z = 1`.

Results: `ff_exists_nonsquare_pair`, `ff_eq_one_of_bimul_steinberg`, `symbol_eq_one_finiteField`.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly

open GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h)
open Polynomial

variable {F : Type*} [Field F]

/-- A power of a unit whose value is not a square has an odd exponent. -/
theorem ff_odd_exp_of_not_isSquare (g : Fˣ) (m : ℕ)
    (hq : ¬IsSquare ((g ^ m : Fˣ) : F)) : Odd m := by
  rcases Nat.even_or_odd m with ⟨r, rfl⟩ | hm
  · exact (hq ⟨((g ^ r : Fˣ) : F), by rw [pow_add, Units.val_mul]⟩).elim
  · exact hm

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.ff_odd_exp_of_not_isSquare

/-- In a finite field of odd characteristic there are nonsquare units `u, v` with `u + v = 1`. -/
theorem ff_exists_nonsquare_pair [Fintype F] (hF : ringChar F ≠ 2) :
    ∃ u v : Fˣ, (u : F) + (v : F) = 1 ∧ ¬IsSquare (u : F) ∧ ¬IsSquare (v : F) := by
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare hF
  obtain ⟨a, b, hab0⟩ : ∃ a b : F, (X ^ 2 : F[X]).eval a + (X ^ 2 - C c).eval b = 0 :=
    FiniteField.exists_root_sum_quadratic (degree_X_pow 2) (degree_X_pow_sub_C (by decide) c)
      (FiniteField.odd_card_of_char_ne_two hF)
  have hab : a ^ 2 + b ^ 2 = c := by
    simp only [eval_pow, eval_X, eval_sub, eval_C] at hab0
    linear_combination hab0
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc ⟨0, (mul_zero 0).symm⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hc ⟨b, by linear_combination (-1 : F) * hab⟩
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hc ⟨a, by linear_combination (-1 : F) * hab⟩
  have hcc : c⁻¹ * c = 1 := inv_mul_cancel₀ hc0
  have key : ∀ q : F, q ≠ 0 → IsSquare (q ^ 2 / c) → IsSquare c := by
    rintro q hq0 ⟨d, hd⟩
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact div_ne_zero (pow_ne_zero 2 hq0) hc0 (hd.trans (mul_zero 0))
    have hdd : d * d⁻¹ = 1 := mul_inv_cancel₀ hd0
    exact ⟨q * d⁻¹, by
      linear_combination (-c * (d * d⁻¹ + 1)) * hdd - d⁻¹ * d⁻¹ * c * hd +
        d⁻¹ * d⁻¹ * q ^ 2 * hcc⟩
  refine ⟨Units.mk0 (a ^ 2 / c) (div_ne_zero (pow_ne_zero 2 ha0) hc0),
    Units.mk0 (b ^ 2 / c) (div_ne_zero (pow_ne_zero 2 hb0) hc0), ?_,
    fun h => hc (key a ha0 h), fun h => hc (key b hb0 h)⟩
  rw [Units.val_mk0, Units.val_mk0]
  linear_combination c⁻¹ * hab + hcc

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.ff_exists_nonsquare_pair

/-- In characteristic `2` the unit group of a finite field has odd order. -/
theorem ff_odd_card_units_of_char_two [Fintype F] [DecidableEq F] (hF : ringChar F = 2) :
    Odd (Fintype.card Fˣ) := by
  have h2 := FiniteField.even_card_of_char_two hF
  have hpos : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Fintype.card_units]
  exact Nat.odd_iff.mpr (by omega)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.ff_odd_card_units_of_char_two

/-- **Abstract vanishing over a finite field.**  A bimultiplicative, antisymmetric map on `Fˣ`
satisfying the Steinberg relation is identically `1`. -/
theorem ff_eq_one_of_bimul_steinberg [Fintype F] {G : Type*} [Group G] (s : Fˣ → Fˣ → G)
    (hr : ∀ u v₁ v₂, s u (v₁ * v₂) = s u v₁ * s u v₂)
    (hl : ∀ u₁ u₂ v, s (u₁ * u₂) v = s u₁ v * s u₂ v)
    (ha : ∀ u v, s v u = (s u v)⁻¹)
    (hst : ∀ u v : Fˣ, (u : F) + (v : F) = 1 → s u v = 1)
    (u v : Fˣ) : s u v = 1 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Fˣ)
  have hR : ∀ (x : Fˣ) (n : ℕ), s x (g ^ n) = s x g ^ n := fun x n =>
    map_pow (MonoidHom.mk' (s x) (hr x)) g n
  have hL : ∀ (x : Fˣ) (n : ℕ), s (g ^ n) x = s g x ^ n := fun x n =>
    map_pow (MonoidHom.mk' (fun y => s y x) (fun a b => hl a b x)) g n
  have hgg : ∀ m n : ℕ, s (g ^ m) (g ^ n) = s g g ^ (m * n) := by
    intro m n
    rw [hR, hL, pow_mul]
  have hz : s g g * s g g = 1 := mul_eq_one_iff_eq_inv.mpr (ha g g)
  have hz1 : s g g = 1 := by
    by_cases hF : ringChar F = 2
    · have h1g : s 1 g = 1 := by
        have e := hl 1 1 g
        rw [mul_one (1 : Fˣ)] at e
        exact mul_left_cancel (e.symm.trans (mul_one _).symm)
      have e : s g g ^ Fintype.card Fˣ = 1 := by
        rw [← hL, pow_card_eq_one, h1g]
      rw [pow_odd_of_mul_self_eq_one hz (ff_odd_card_units_of_char_two hF)] at e
      exact e
    · obtain ⟨u₀, v₀, huv₀, hu₀, hv₀⟩ := ff_exists_nonsquare_pair hF
      obtain ⟨m₀, hm₀⟩ := (Submonoid.mem_powers_iff u₀ g).mp (hg u₀)
      obtain ⟨n₀, hn₀⟩ := (Submonoid.mem_powers_iff v₀ g).mp (hg v₀)
      have hmo : Odd m₀ := ff_odd_exp_of_not_isSquare g m₀ (by rw [hm₀]; exact hu₀)
      have hno : Odd n₀ := ff_odd_exp_of_not_isSquare g n₀ (by rw [hn₀]; exact hv₀)
      have e := hst u₀ v₀ huv₀
      rw [← hm₀, ← hn₀, hgg, pow_odd_of_mul_self_eq_one hz (hmo.mul hno)] at e
      exact e
  obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff u g).mp (hg u)
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff v g).mp (hg v)
  rw [hgg, hz1, one_pow]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.ff_eq_one_of_bimul_steinberg

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- **Symbols over a finite field are trivial.**  With three distinct indices every Steinberg
symbol of `St_I(F)` is `1`, for every finite field `F`. -/
theorem symbol_eq_one_finiteField [Fintype F] (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u v : Fˣ) : symbol i j hij u v = 1 :=
  ff_eq_one_of_bimul_steinberg (symbol i j hij) (symbol_mul_right i j k hij hik hjk)
    (symbol_mul_left i j k hij hik hjk) (symbol_antisymm i j k hij hik hjk)
    (symbol_eq_one_of_add_eq_one i j k hij hik hjk) u v

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.symbol_eq_one_finiteField

/-- Over a finite field, `h_ij(c) h_ij(c') = h_ij(c' c)`, because symbols are trivial (the
finite-field form of `ElemFP.FieldK2.bruhatBigCell_h_mul_zmod`). -/
theorem h_mul_finiteField [Fintype F] (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (c c' : Fˣ) : h i j hij c * h i j hij c' = h i j hij (c' * c) := by
  have e := symbol_eq_one_finiteField i j k hij hik hjk c' c
  rw [symbol, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at e
  exact e.symm

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.h_mul_finiteField

end GroupApproximation.BooneHigmanLinear.K2Poly
