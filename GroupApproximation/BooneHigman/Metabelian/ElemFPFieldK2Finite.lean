import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2SteinbergRel
import Mathlib.FieldTheory.Finite.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Steinberg symbols over a prime field are trivial

Lane `bh-met-15`.  Take a group `G` and a map `s : (ZMod p)ˣ → (ZMod p)ˣ → G` that is
multiplicative in each variable, antisymmetric (`s v u = (s u v)⁻¹`) and satisfies the Steinberg
relation (`s u v = 1` when `u + v = 1`).  Then `s` is identically `1`
(`eq_one_of_bimul_steinberg`).  So every symbol of `St_I(ZMod p)` is trivial once `I` has three
distinct indices (`symbol_eq_one_zmod`).

Truth check (paper).  `(ZMod p)ˣ` is cyclic, say with generator `g`.  Put `z = s g g`.  Then
`s(g^m, g^n) = z^(mn)`, and antisymmetry gives `z² = 1`.  For odd `p`, choose a nonsquare `c`
and write `c = a² + b²`.  Then `u = a²/c` and `v = b²/c` are nonsquares with `u + v = 1`.  Their
exponents are odd, so `1 = s u v = z^(odd) = z`.  For `p = 2` the unit group is trivial and
`s 1 1 = s 1 1 · s 1 1` gives `s 1 1 = 1`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

/-- An element of order dividing two is fixed by odd powers. -/
theorem pow_odd_of_mul_self_eq_one {G : Type*} [Group G] {z : G} (hz : z * z = 1) {m : ℕ}
    (hm : Odd m) : z ^ m = z := by
  obtain ⟨r, rfl⟩ := hm
  rw [pow_succ, pow_mul, pow_two, hz, one_pow, one_mul]

/-- A power of a unit whose value is not a square has an odd exponent. -/
theorem odd_exp_of_not_isSquare {p : ℕ} [Fact p.Prime] (g : (ZMod p)ˣ) (m : ℕ)
    (hq : ¬IsSquare ((g ^ m : (ZMod p)ˣ) : ZMod p)) : Odd m := by
  rcases Nat.even_or_odd m with ⟨r, rfl⟩ | hm
  · exact (hq ⟨((g ^ r : (ZMod p)ˣ) : ZMod p), by rw [pow_add, Units.val_mul]⟩).elim
  · exact hm

/-- For an odd prime `p` there are nonsquare units `u, v` of `ZMod p` with `u + v = 1`. -/
theorem exists_nonsquare_pair (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ u v : (ZMod p)ˣ, (u : ZMod p) + (v : ZMod p) = 1 ∧ ¬IsSquare (u : ZMod p) ∧
      ¬IsSquare (v : ZMod p) := by
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p c
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc ⟨0, (mul_zero 0).symm⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hc ⟨b, by linear_combination (-1 : ZMod p) * hab⟩
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hc ⟨a, by linear_combination (-1 : ZMod p) * hab⟩
  have hcc : c⁻¹ * c = 1 := inv_mul_cancel₀ hc0
  have key : ∀ q : ZMod p, q ≠ 0 → IsSquare (q ^ 2 / c) → IsSquare c := by
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

/-- **Abstract vanishing.**  A bimultiplicative, antisymmetric map on `(ZMod p)ˣ` satisfying the
Steinberg relation is identically `1`. -/
theorem eq_one_of_bimul_steinberg {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    (s : (ZMod p)ˣ → (ZMod p)ˣ → G)
    (hr : ∀ u v₁ v₂, s u (v₁ * v₂) = s u v₁ * s u v₂)
    (hl : ∀ u₁ u₂ v, s (u₁ * u₂) v = s u₁ v * s u₂ v)
    (ha : ∀ u v, s v u = (s u v)⁻¹)
    (hst : ∀ u v : (ZMod p)ˣ, (u : ZMod p) + (v : ZMod p) = 1 → s u v = 1)
    (u v : (ZMod p)ˣ) : s u v = 1 := by
  by_cases hp2 : p = 2
  · subst hp2
    have hsub : Subsingleton (ZMod 2)ˣ :=
      Fintype.card_le_one_iff_subsingleton.mp ((ZMod.card_units 2).trans_le (by decide))
    rw [Subsingleton.elim u 1, Subsingleton.elim v 1]
    have h1 := hl 1 1 1
    rw [mul_one (1 : (ZMod 2)ˣ)] at h1
    exact mul_left_cancel (h1.symm.trans (mul_one _).symm)
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := (ZMod p)ˣ)
  have hR : ∀ (w : (ZMod p)ˣ) (n : ℕ), s w (g ^ n) = s w g ^ n := fun w n =>
    map_pow (MonoidHom.mk' (s w) (hr w)) g n
  have hL : ∀ (w : (ZMod p)ˣ) (n : ℕ), s (g ^ n) w = s g w ^ n := fun w n =>
    map_pow (MonoidHom.mk' (fun y => s y w) (fun a b => hl a b w)) g n
  have hgg : ∀ m n : ℕ, s (g ^ m) (g ^ n) = s g g ^ (m * n) := by
    intro m n
    rw [hR, hL, pow_mul]
  have hz : s g g * s g g = 1 := mul_eq_one_iff_eq_inv.mpr (ha g g)
  obtain ⟨u₀, v₀, huv₀, hu₀, hv₀⟩ := exists_nonsquare_pair p hp2
  obtain ⟨m₀, hm₀⟩ := (Submonoid.mem_powers_iff u₀ g).mp (hg u₀)
  obtain ⟨n₀, hn₀⟩ := (Submonoid.mem_powers_iff v₀ g).mp (hg v₀)
  have hmo : Odd m₀ := odd_exp_of_not_isSquare g m₀ (by rw [hm₀]; exact hu₀)
  have hno : Odd n₀ := odd_exp_of_not_isSquare g n₀ (by rw [hn₀]; exact hv₀)
  have hz1 : s g g = 1 := by
    have e := hst u₀ v₀ huv₀
    rw [← hm₀, ← hn₀, hgg, pow_odd_of_mul_self_eq_one hz (hmo.mul hno)] at e
    exact e
  obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff u g).mp (hg u)
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff v g).mp (hg v)
  rw [hgg, hz1, one_pow]

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- **Symbols over `ZMod p` are trivial.**  With three distinct indices every symbol is `1`. -/
theorem symbol_eq_one_zmod {p : ℕ} [Fact p.Prime] (i j k : I) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (u v : (ZMod p)ˣ) : symbol i j hij u v = 1 :=
  eq_one_of_bimul_steinberg (symbol i j hij) (symbol_mul_right i j k hij hik hjk)
    (symbol_mul_left i j k hij hik hjk) (symbol_antisymm i j k hij hik hjk)
    (symbol_eq_one_of_add_eq_one i j k hij hik hjk) u v

end GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.pow_odd_of_mul_self_eq_one
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.odd_exp_of_not_isSquare
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.exists_nonsquare_pair
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.eq_one_of_bimul_steinberg
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.symbol_eq_one_zmod
