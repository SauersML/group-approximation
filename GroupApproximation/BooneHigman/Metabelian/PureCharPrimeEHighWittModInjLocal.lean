import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittModInjBase
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import GroupApproximation.Meta.AxiomGuard

/-!
# `D = ZMod (p²)[σ]_(p)` is local with ideals `0 ⊂ pD ⊂ D` (bh-met-87f, part 2)

Write `D = eHighWittCoeff_D p σ`. Every `z = a / s ∈ D` either has `a ≢ 0 mod p`, so `a ∈ S`
and `z` is a unit, or has `a = p b`, so `z ∈ pD` (`eHighWittModInj_isUnit_or`). Since `p² = 0`
and `p ≠ 0` in `D`, `pD` is exactly the set of nonunits. Consequences:

* `eHighWittModInj_ann`: `p y = 0 → y ∈ pD` (the annihilator of `p` is `pD`);
* `eHighWittModInj_eq_p_mul_unit`: every nonzero element of `pD` is `p · unit`;
* `eHighWittModInj_ideal_trichotomy`: the ideals of `D` are `⊥`, `pD`, `⊤`;
* `eHighWittModInj_isLocalRing`, `eHighWittModInj_maximalIdeal`: `D` is local with maximal
  ideal `pD`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

variable (p : ℕ) (σ : Type)

/-- If `z · s = a` in `D` with `a ≡ 0 mod p`, then `z ∈ pD`. -/
theorem eHighWittModInj_eq_p_mul_of_red [Fact p.Prime] {z : eHighWittCoeff_D p σ}
    {a : MvPolynomial σ (ZMod (p ^ 2))} {s : eHighWittCoeff_S p σ}
    (h : z * algebraMap (MvPolynomial σ (ZMod (p ^ 2))) (eHighWittCoeff_D p σ) s =
      algebraMap (MvPolynomial σ (ZMod (p ^ 2))) (eHighWittCoeff_D p σ) a)
    (ha : eHighWittCoeff_red p σ a = 0) :
    ∃ w : eHighWittCoeff_D p σ, z = ((p : ℕ) : eHighWittCoeff_D p σ) * w := by
  obtain ⟨b, rfl⟩ := eHighWittCoeff_red_eq_zero p σ ha
  obtain ⟨u, hu⟩ := IsLocalization.map_units (eHighWittCoeff_D p σ) s
  refine ⟨algebraMap (MvPolynomial σ (ZMod (p ^ 2))) (eHighWittCoeff_D p σ) b * ↑u⁻¹, ?_⟩
  rw [← mul_assoc, Units.eq_mul_inv_iff_mul_eq, hu, h, map_mul, map_natCast]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_eq_p_mul_of_red

/-- **Every element of `D` is a unit or lies in `pD`.** -/
theorem eHighWittModInj_isUnit_or [Fact p.Prime] (z : eHighWittCoeff_D p σ) :
    IsUnit z ∨ ∃ w : eHighWittCoeff_D p σ, z = ((p : ℕ) : eHighWittCoeff_D p σ) * w := by
  obtain ⟨x, hx⟩ := IsLocalization.surj (eHighWittCoeff_S p σ) z
  by_cases ha : eHighWittCoeff_red p σ x.1 = 0
  · exact Or.inr (eHighWittModInj_eq_p_mul_of_red p σ hx ha)
  · left
    refine isUnit_of_mul_isUnit_left
      (y := algebraMap (MvPolynomial σ (ZMod (p ^ 2))) (eHighWittCoeff_D p σ) x.2) ?_
    rw [hx]
    exact IsLocalization.map_units (eHighWittCoeff_D p σ)
      ⟨x.1, eHighWittModInj_mem_of_red_ne_zero p σ ha⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_isUnit_or

/-- `p ≠ 0` in `D`. -/
theorem eHighWittModInj_p_ne_zero [Fact p.Prime] : ((p : ℕ) : eHighWittCoeff_D p σ) ≠ 0 := by
  intro h
  rw [← map_natCast (algebraMap (MvPolynomial σ (ZMod (p ^ 2))) (eHighWittCoeff_D p σ)) p,
    IsLocalization.map_eq_zero_iff (eHighWittCoeff_S p σ) (eHighWittCoeff_D p σ)] at h
  obtain ⟨t, ht⟩ := h
  exact eHighWittModInj_red_ne_zero_of_mem p σ t.2
    (eHighWittModInj_red_eq_zero_of_p_mul p σ ((mul_comm _ _).trans ht))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_p_ne_zero

/-- **The annihilator of `p` in `D` is `pD`.** -/
theorem eHighWittModInj_ann [Fact p.Prime] {y : eHighWittCoeff_D p σ}
    (h : ((p : ℕ) : eHighWittCoeff_D p σ) * y = 0) :
    ∃ c : eHighWittCoeff_D p σ, y = ((p : ℕ) : eHighWittCoeff_D p σ) * c := by
  obtain ⟨x, hx⟩ := IsLocalization.surj (eHighWittCoeff_S p σ) y
  have h0 : algebraMap (MvPolynomial σ (ZMod (p ^ 2))) (eHighWittCoeff_D p σ)
      (((p : ℕ) : MvPolynomial σ (ZMod (p ^ 2))) * x.1) = 0 := by
    rw [map_mul, map_natCast, ← hx, ← mul_assoc, h, zero_mul]
  obtain ⟨t, ht⟩ :=
    (IsLocalization.map_eq_zero_iff (eHighWittCoeff_S p σ) (eHighWittCoeff_D p σ) _).mp h0
  have h1 : eHighWittCoeff_red p σ ((t : MvPolynomial σ (ZMod (p ^ 2))) * x.1) = 0 :=
    eHighWittModInj_red_eq_zero_of_p_mul p σ (by rw [mul_left_comm]; exact ht)
  rw [map_mul] at h1
  exact eHighWittModInj_eq_p_mul_of_red p σ hx
    ((mul_eq_zero.mp h1).resolve_left (eHighWittModInj_red_ne_zero_of_mem p σ t.2))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_ann

/-- `p` is not a unit of `D`. -/
theorem eHighWittModInj_not_isUnit_p [Fact p.Prime] :
    ¬IsUnit ((p : ℕ) : eHighWittCoeff_D p σ) := fun hu =>
  eHighWittModInj_p_ne_zero p σ (hu.mul_left_eq_zero.mp (eHighWittModInj_p_mul_p p σ))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_not_isUnit_p

/-- No element of `pD` is a unit. -/
theorem eHighWittModInj_not_isUnit_p_mul [Fact p.Prime] (w : eHighWittCoeff_D p σ) :
    ¬IsUnit (((p : ℕ) : eHighWittCoeff_D p σ) * w) := fun hu =>
  eHighWittModInj_not_isUnit_p p σ (isUnit_of_mul_isUnit_left hu)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_not_isUnit_p_mul

/-- If `p w ≠ 0` then `w` is a unit. -/
theorem eHighWittModInj_isUnit_of_p_mul_ne_zero [Fact p.Prime] {w : eHighWittCoeff_D p σ}
    (h : ((p : ℕ) : eHighWittCoeff_D p σ) * w ≠ 0) : IsUnit w := by
  rcases eHighWittModInj_isUnit_or p σ w with hw | ⟨v, rfl⟩
  · exact hw
  · exact (h (by rw [← mul_assoc, eHighWittModInj_p_mul_p p σ, zero_mul])).elim

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_isUnit_of_p_mul_ne_zero

/-- `pD` is exactly the set of nonunits of `D`. -/
theorem eHighWittModInj_mem_span_p_iff [Fact p.Prime] (x : eHighWittCoeff_D p σ) :
    x ∈ Ideal.span {((p : ℕ) : eHighWittCoeff_D p σ)} ↔ ¬IsUnit x := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    rw [mul_comm]
    exact eHighWittModInj_not_isUnit_p_mul p σ a
  · intro hx
    rcases eHighWittModInj_isUnit_or p σ x with h | ⟨w, rfl⟩
    · exact absurd h hx
    · exact ⟨w, mul_comm w _⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_mem_span_p_iff

/-- **Every nonzero element of `pD` is `p · unit`.** -/
theorem eHighWittModInj_eq_p_mul_unit [Fact p.Prime] {x : eHighWittCoeff_D p σ}
    (hx : x ∈ Ideal.span {((p : ℕ) : eHighWittCoeff_D p σ)}) (hne : x ≠ 0) :
    ∃ u : (eHighWittCoeff_D p σ)ˣ, x = ((p : ℕ) : eHighWittCoeff_D p σ) * u := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  obtain ⟨u, hu⟩ := eHighWittModInj_isUnit_of_p_mul_ne_zero p σ (w := a)
    (by rwa [mul_comm] at hne)
  exact ⟨u, by rw [hu, mul_comm]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_eq_p_mul_unit

/-- An ideal without units containing a nonzero element contains `p`. -/
theorem eHighWittModInj_p_mem [Fact p.Prime] (I : Ideal (eHighWittCoeff_D p σ))
    (hU : ∀ u ∈ I, ¬IsUnit u) {x0 : eHighWittCoeff_D p σ} (hx0 : x0 ∈ I) (hne : x0 ≠ 0) :
    ((p : ℕ) : eHighWittCoeff_D p σ) ∈ I := by
  rcases eHighWittModInj_isUnit_or p σ x0 with hu | ⟨u, rfl⟩
  · exact absurd hu (hU _ hx0)
  · obtain ⟨v, rfl⟩ := eHighWittModInj_isUnit_of_p_mul_ne_zero p σ hne
    have h := Ideal.mul_mem_right (↑v⁻¹ : eHighWittCoeff_D p σ) I hx0
    rwa [mul_assoc, Units.mul_inv, mul_one] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_p_mem

/-- **The ideals of `D` are `⊥`, `pD` and `⊤`.** -/
theorem eHighWittModInj_ideal_trichotomy [Fact p.Prime] (I : Ideal (eHighWittCoeff_D p σ)) :
    I = ⊥ ∨ I = Ideal.span {((p : ℕ) : eHighWittCoeff_D p σ)} ∨ I = ⊤ := by
  by_cases hU : ∃ u ∈ I, IsUnit u
  · obtain ⟨u, hu, hunit⟩ := hU
    exact Or.inr (Or.inr (Ideal.eq_top_of_isUnit_mem I hu hunit))
  · push_neg at hU
    by_cases h0 : ∀ x ∈ I, x = 0
    · exact Or.inl ((Submodule.eq_bot_iff I).mpr h0)
    · push_neg at h0
      obtain ⟨x0, hx0, hne⟩ := h0
      have hp := eHighWittModInj_p_mem p σ I hU hx0 hne
      refine Or.inr (Or.inl (le_antisymm (fun x hx => ?_)
        ((Ideal.span_singleton_le_iff_mem I).mpr hp)))
      exact (eHighWittModInj_mem_span_p_iff p σ x).mpr (hU x hx)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_ideal_trichotomy

/-- **`D` is a local ring.** -/
instance eHighWittModInj_isLocalRing [Fact p.Prime] : IsLocalRing (eHighWittCoeff_D p σ) := by
  haveI : Nontrivial (eHighWittCoeff_D p σ) :=
    nontrivial_of_ne _ _ (eHighWittModInj_p_ne_zero p σ)
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases eHighWittModInj_isUnit_or p σ a with h | ⟨w, rfl⟩
  · exact Or.inl h
  · refine Or.inr (IsUnit.of_mul_eq_one (1 + ((p : ℕ) : eHighWittCoeff_D p σ) * w) ?_)
    have e : ∀ q v : eHighWittCoeff_D p σ, (1 - q * v) * (1 + q * v) = 1 - q * q * (v * v) :=
      fun q v => by ring
    rw [e, eHighWittModInj_p_mul_p p σ, zero_mul, sub_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_isLocalRing

/-- **The maximal ideal of `D` is `pD`.** -/
theorem eHighWittModInj_maximalIdeal [Fact p.Prime] :
    IsLocalRing.maximalIdeal (eHighWittCoeff_D p σ) =
      Ideal.span {((p : ℕ) : eHighWittCoeff_D p σ)} := by
  ext x
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, eHighWittModInj_mem_span_p_iff p σ x]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_maximalIdeal

end GroupApproximation.BooneHigman.Metabelian.Coprimary
