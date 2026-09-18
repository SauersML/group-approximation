import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.LinearCombination
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PullRelRing
import GroupApproximation.Meta.AxiomGuard

/-!
# The Karoubi square `P → A`, `P → L[X]`: ring facts

Lane `bh-met-91v`, ring module.  Notation: `L = A_s`, `λ = algebraMap A L`, and
`P = k2DilateSt_pullback s = {(a, h) : λ a = h(0)}`, with `fst`, `snd`, `const`, `lift` as in
`ElemFPK2PullRelRing`.

* `k2Karoubi_const_dvd_iff`: if `λ d` is invertible then `const d ∣ b ↔ d ∣ fst b`.  Hence
  `k2Karoubi_span_const_pow`: `s^N P = fst⁻¹ (s^N A)`, i.e. `P / s^N ≅ A / s^N`.
* `k2Karoubi_const_regular`: `s` regular on `A` makes `const s` regular on `P`.
* `k2Karoubi_snd_surj`: every `h ∈ L[X]` is `snd b / λ(s)^n`, i.e. `P_s = L[X]`.
* **LOUD truth check** (`k2Karoubi_not_injective_on_dvd`): the brief's slogan
  "`s^N P = s^N A` as non-unital rings" is **FALSE** whenever `L ≠ 0`.  `lift X` is a nonzero
  element of `s^N P` killed by `fst`.  What is true is `s^N P = fst⁻¹ (s^N A)` (above).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

section KaroubiRing

variable {A : Type*} [CommRing A] {s : A}

/-- **Divisibility in `P`**: if `w · λ d = 1` then `const d ∣ b ↔ d ∣ fst b`. -/
theorem k2Karoubi_const_dvd_iff {d : A} {w : Localization.Away s}
    (hw : w * algebraMap A (Localization.Away s) d = 1) (b : k2DilateSt_pullback s) :
    k2PullRel_const s d ∣ b ↔ d ∣ k2PullRel_fst s b := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨k2PullRel_fst s c, by rw [map_mul, k2PullRel_fst_const]⟩
  · rintro ⟨a, ha⟩
    refine ⟨k2PullRel_const s a + k2PullRel_lift s (Polynomial.C w * k2PullRel_snd s b), ?_⟩
    refine k2PullRel_ext ?_ ?_
    · simp only [map_mul, map_add, k2PullRel_fst_const, k2PullRel_fst_lift, add_zero, ha]
    · have hE : Polynomial.C w * Polynomial.C (algebraMap A (Localization.Away s) d) = 1 := by
        rw [← Polynomial.C_mul, hw, map_one]
      have h0 := k2PullRel_eval_snd b
      rw [ha] at h0
      simp only [map_mul, map_add, k2PullRel_snd_const, k2PullRel_snd_lift, Polynomial.eval_mul,
        Polynomial.eval_C, h0]
      linear_combination (Polynomial.C (algebraMap A (Localization.Away s) d) *
        Polynomial.C (algebraMap A (Localization.Away s) a) - k2PullRel_snd s b) * hE

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_const_dvd_iff

theorem k2Karoubi_inv_pow_mul (N : ℕ) :
    k2DilateSt_inv s ^ N * algebraMap A (Localization.Away s) (s ^ N) = 1 := by
  rw [map_pow, ← mul_pow, k2DilateSt_inv_mul, one_pow]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_inv_pow_mul

/-- `const (s^N) ∣ b ↔ s^N ∣ fst b`. -/
theorem k2Karoubi_const_pow_dvd_iff (N : ℕ) (b : k2DilateSt_pullback s) :
    k2PullRel_const s (s ^ N) ∣ b ↔ s ^ N ∣ k2PullRel_fst s b :=
  k2Karoubi_const_dvd_iff (k2Karoubi_inv_pow_mul N) b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_const_pow_dvd_iff

/-- **`s^N P = fst⁻¹ (s^N A)`**, as ideals of `P`. -/
theorem k2Karoubi_span_const_pow (N : ℕ) :
    Ideal.span {k2PullRel_const s (s ^ N)} = (Ideal.span {s ^ N}).comap (k2PullRel_fst s) := by
  ext b
  rw [Ideal.mem_span_singleton, Ideal.mem_comap, Ideal.mem_span_singleton]
  exact k2Karoubi_const_pow_dvd_iff N b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_span_const_pow

/-- **Regularity**: if `s` is a nonzerodivisor on `A`, then `const s` is one on `P`. -/
theorem k2Karoubi_const_regular (hs : ∀ a : A, s * a = 0 → a = 0) {b : k2DilateSt_pullback s}
    (hb : k2PullRel_const s s * b = 0) : b = 0 := by
  have h1 := congrArg (k2PullRel_fst s) hb
  have h2 := congrArg (k2PullRel_snd s) hb
  rw [map_mul, k2PullRel_fst_const, map_zero] at h1
  rw [map_mul, k2PullRel_snd_const, map_zero] at h2
  have hE : Polynomial.C (k2DilateSt_inv s) *
      Polynomial.C (algebraMap A (Localization.Away s) s) = 1 := by
    rw [← Polynomial.C_mul, k2DilateSt_inv_mul, map_one]
  refine k2PullRel_ext ?_ ?_
  · rw [map_zero]
    exact hs _ h1
  · rw [map_zero]
    linear_combination Polynomial.C (k2DilateSt_inv s) * h2 - k2PullRel_snd s b * hE

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_const_regular

/-- **`P_s = L[X]`**: every `h` is `snd b / λ(s)^n` for some `b ∈ P`. -/
theorem k2Karoubi_snd_surj (h : Polynomial (Localization.Away s)) :
    ∃ (n : ℕ) (b : k2DilateSt_pullback s),
      k2PullRel_snd s b = Polynomial.C (algebraMap A (Localization.Away s) s ^ n) * h := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj s (h.eval 0)
  refine ⟨n, k2PullRel_const s a +
    k2PullRel_lift s (Polynomial.C (algebraMap A (Localization.Away s) s ^ n) * h), ?_⟩
  have e : Polynomial.C (algebraMap A (Localization.Away s) a) =
      Polynomial.C (algebraMap A (Localization.Away s) s ^ n * h.eval 0) := by
    rw [← ha, mul_comm]
  simp only [map_add, k2PullRel_snd_const, k2PullRel_snd_lift, Polynomial.eval_mul,
    Polynomial.eval_C]
  rw [e]
  ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_snd_surj

/-- **LOUD truth check**: `fst` is not injective on `s^N P` once `L ≠ 0`.  So
"`s^N P = s^N A` as non-unital rings" is false; the witness is `lift X`. -/
theorem k2Karoubi_not_injective_on_dvd [Nontrivial (Localization.Away s)] (N : ℕ) :
    ∃ b : k2DilateSt_pullback s,
      k2PullRel_const s (s ^ N) ∣ b ∧ k2PullRel_fst s b = 0 ∧ b ≠ 0 := by
  refine ⟨k2PullRel_lift s Polynomial.X, (k2Karoubi_const_pow_dvd_iff N _).mpr ?_,
    k2PullRel_fst_lift s _, ?_⟩
  · rw [k2PullRel_fst_lift]
    exact dvd_zero _
  · intro h
    have e := congrArg (k2PullRel_snd s) h
    simp only [k2PullRel_snd_lift, Polynomial.eval_X, map_zero, sub_zero] at e
    exact Polynomial.X_ne_zero e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_not_injective_on_dvd

end KaroubiRing

end GroupApproximation.BooneHigman.Metabelian.ElemFP
