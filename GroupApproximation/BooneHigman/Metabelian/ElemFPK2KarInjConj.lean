import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KaroubiRing
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KaroubiWitness
import GroupApproximation.Meta.AxiomGuard

/-!
# The `x_ji(a/sⁿ)` conjugation step inside `St(M, L[X])`

Lane `bh-met-92b`, conjugation module.  Notation: `P = A ×_L L[X]`, `L = A_s`,
`K = ker (fst : St(M, P) → St(M, A))`, and `S = snd (K) ⊆ St(M, L[X])`
(`k2KarInj_sndKer`).

* `k2KarInj_conj_opp` (any ring, three distinct indices `i, j, k`):
  `x_ji(t) · x_ij(v w) · x_ji(t)⁻¹ = ⁅x_jk(t v) · x_ik(v), x_ki(-(w t)) · x_kj(w)⁆`.
* `k2KarInj_snd_conj_opp`: for `t = a / sⁿ ∈ L` and `h(0) = 0`, the conjugate
  `x_ji(C t) · x_ij(h) · x_ji(C t)⁻¹` lies in `S`.  Take `v = h / sⁿ` (the ideal `X L[X]` is
  `s`-divisible) and `w = sⁿ`; then `t v` and `v` have zero constant term, and `w t = a`,
  `w = sⁿ` are constants from `A`.  So the conjugate is `snd` of the explicit element
  `⁅x_jk(lift (t v)) · x_ik(lift v), x_ki(const (-a)) · x_kj(const sⁿ)⁆` of `K`.
* `k2KarInj_conj_mem` (`M ≥ 3`): for **every** root `x_kl(C t)`, `t ∈ L`, and every generator
  `x_ij(h)` with `h(0) = 0`, the conjugate lies in `S`.  The other root configurations are the
  Steinberg formulas behind `F1`–`F3`.

This is the generator-level surjectivity step of the Karoubi square.  It is **not** the
injectivity `R1` (`k2Karoubi_InjAt`); see `ElemFPK2KarInjStatement` for the status.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

section KarInjConjRing

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

/-- **The opposite-root conjugation identity** (three distinct indices, any ring). -/
theorem k2KarInj_conj_opp (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (t v w : R) :
    x j i hij.symm t * x i j hij (v * w) * (x j i hij.symm t)⁻¹ =
      ⁅x j k hjk (t * v) * x i k hik v, x k i hik.symm (-(w * t)) * x k j hjk.symm w⁆ := by
  have h1 : x j k hjk (t * v) * x i k hik v =
      x j i hij.symm t * x i k hik v * (x j i hij.symm t)⁻¹ := by
    rw [← x_commutator j i k hij.symm hik hjk t v, commutatorElement_def]
    group
  have h2 : x k i hik.symm (-(w * t)) * x k j hjk.symm w =
      x j i hij.symm t * x k j hjk.symm w * (x j i hij.symm t)⁻¹ := by
    rw [x_neg, ← x_commutator k j i hjk.symm hij.symm hik.symm w t, commutatorElement_def]
    group
  rw [h1, h2, ← x_commutator i k j hik hjk.symm hij v w]
  simp only [commutatorElement_def]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInj_conj_opp

end KarInjConjRing

section KarInjThird

/-- In `Fin M` with `M ≥ 3`, any two indices miss a third one. -/
theorem k2KarInj_exists_third {M : ℕ} (hM : 3 ≤ M) (i j : Fin M) :
    ∃ m : Fin M, m ≠ i ∧ m ≠ j := by
  have key : ∃ m : ℕ, m < 3 ∧ m ≠ i.val ∧ m ≠ j.val := by
    by_cases h0 : 0 ≠ i.val ∧ 0 ≠ j.val
    · exact ⟨0, by omega, h0⟩
    by_cases h1 : 1 ≠ i.val ∧ 1 ≠ j.val
    · exact ⟨1, by omega, h1⟩
    exact ⟨2, by omega, by omega, by omega⟩
  obtain ⟨m, hm3, hmi, hmj⟩ := key
  exact ⟨⟨m, by omega⟩, fun e ↦ hmi (congrArg Fin.val e), fun e ↦ hmj (congrArg Fin.val e)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInj_exists_third

end KarInjThird

section KarInjConj

variable {A : Type*} [CommRing A] {s : A} {M : ℕ}

/-- `S = snd (ker fst) ⊆ St(M, L[X])`. -/
def k2KarInj_sndKer (s : A) (M : ℕ) :
    Subgroup (SteinbergGroup (Fin M) (Polynomial (Localization.Away s))) :=
  (k2PullRel_ker s M).map (ringMap (k2PullRel_snd s))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInj_sndKer

theorem k2KarInj_mem_sndKer {z : SteinbergGroup (Fin M) (Polynomial (Localization.Away s))} :
    z ∈ k2KarInj_sndKer s M ↔ ∃ y ∈ k2PullRel_ker s M, ringMap (k2PullRel_snd s) y = z :=
  Subgroup.mem_map

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInj_mem_sndKer

/-- `x_ij(h) ∈ S` when `h(0) = 0`: it is `snd (x_ij (lift h))`. -/
theorem k2KarInj_x_mem (i j : Fin M) (hij : i ≠ j) {h : Polynomial (Localization.Away s)}
    (h0 : h.eval 0 = 0) : x i j hij h ∈ k2KarInj_sndKer s M := by
  refine k2KarInj_mem_sndKer.mpr
    ⟨x i j hij (k2PullRel_lift s h), k2PullRel_x_lift_mem i j hij h, ?_⟩
  rw [ringMap_x, k2PullRel_snd_lift, h0, map_zero, sub_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInj_x_mem

/-- **Opposite root, explicit witness.**  For `t = a / sⁿ` and `h(0) = 0`, the conjugate
`x_ji(C t) · x_ij(h) · x_ji(C t)⁻¹` is `snd` of an explicit commutator in `ker fst`. -/
theorem k2KarInj_snd_conj_opp (i j k : Fin M) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (t : Localization.Away s) {h : Polynomial (Localization.Away s)} (h0 : h.eval 0 = 0) :
    x j i hij.symm (Polynomial.C t) * x i j hij h * (x j i hij.symm (Polynomial.C t))⁻¹ ∈
      k2KarInj_sndKer s M := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj s t
  obtain ⟨h', hh'⟩ : ∃ h' : Polynomial (Localization.Away s),
      h' = Polynomial.C (k2DilateSt_inv s ^ n) * h := ⟨_, rfl⟩
  have e0 : h'.eval 0 = 0 := by
    rw [hh', Polynomial.eval_mul, Polynomial.eval_C, h0, mul_zero]
  have e1 : (Polynomial.C t * h').eval 0 = 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_C, e0, mul_zero]
  have hC : Polynomial.C (k2DilateSt_inv s ^ n) *
      Polynomial.C (algebraMap A (Localization.Away s) (s ^ n)) = 1 := by
    rw [← Polynomial.C_mul, k2Karoubi_inv_pow_mul, map_one]
  have eh : h = h' * Polynomial.C (algebraMap A (Localization.Away s) (s ^ n)) := by
    rw [hh']
    linear_combination (-h) * hC
  have ea : Polynomial.C (algebraMap A (Localization.Away s) (-a)) =
      -(Polynomial.C (algebraMap A (Localization.Away s) (s ^ n)) * Polynomial.C t) := by
    rw [map_neg, map_neg, ← ha, map_pow, Polynomial.C_mul]
    ring
  refine k2KarInj_mem_sndKer.mpr ⟨⁅x j k hjk (k2PullRel_lift s (Polynomial.C t * h')) *
      x i k hik (k2PullRel_lift s h'), x k i hik.symm (k2PullRel_const s (-a)) *
      x k j hjk.symm (k2PullRel_const s (s ^ n))⁆, ?_, ?_⟩
  · rw [k2PullRel_mem_ker]
    simp only [map_commutatorElement, map_mul, ringMap_x, k2PullRel_fst_lift, x_zero, one_mul,
      commutatorElement_one_left]
  · rw [eh, k2KarInj_conj_opp i j k hij hik hjk]
    simp only [map_commutatorElement, map_mul, ringMap_x, k2PullRel_snd_lift,
      k2PullRel_snd_const, e0, e1, map_zero, sub_zero, ea]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInj_snd_conj_opp

/-- The opposite-root case with the third index chosen automatically (`M ≥ 3`). -/
theorem k2KarInj_snd_conj_opp3 (hM : 3 ≤ M) (i j : Fin M) (hij : i ≠ j)
    (t : Localization.Away s) {h : Polynomial (Localization.Away s)} (h0 : h.eval 0 = 0) :
    x j i hij.symm (Polynomial.C t) * x i j hij h * (x j i hij.symm (Polynomial.C t))⁻¹ ∈
      k2KarInj_sndKer s M := by
  obtain ⟨m, hmi, hmj⟩ := k2KarInj_exists_third hM i j
  exact k2KarInj_snd_conj_opp i j m hij (Ne.symm hmi) (Ne.symm hmj) t h0

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInj_snd_conj_opp3

/-- Root `x_jl` against generator `x_ij`: the conjugate is `x_il(-(h t)) · x_ij(h)`. -/
theorem k2KarInj_conj_mem_right (i j l : Fin M) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (t : Localization.Away s) {h : Polynomial (Localization.Away s)} (h0 : h.eval 0 = 0) :
    x j l hjl (Polynomial.C t) * x i j hij h * (x j l hjl (Polynomial.C t))⁻¹ ∈
      k2KarInj_sndKer s M := by
  have e : x j l hjl (Polynomial.C t) * x i j hij h * (x j l hjl (Polynomial.C t))⁻¹ =
      x i l hil (-(h * Polynomial.C t)) * x i j hij h := by
    rw [x_neg, ← x_commutator i j l hij hjl hil h (Polynomial.C t), commutatorElement_def]
    group
  rw [e]
  refine mul_mem (k2KarInj_x_mem i l hil ?_) (k2KarInj_x_mem i j hij h0)
  rw [Polynomial.eval_neg, Polynomial.eval_mul, h0, zero_mul, neg_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInj_conj_mem_right

/-- Root `x_ki` against generator `x_ij`: the conjugate is `x_kj(t h) · x_ij(h)`. -/
theorem k2KarInj_conj_mem_left (i j k : Fin M) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (t : Localization.Away s) {h : Polynomial (Localization.Away s)} (h0 : h.eval 0 = 0) :
    x k i hki (Polynomial.C t) * x i j hij h * (x k i hki (Polynomial.C t))⁻¹ ∈
      k2KarInj_sndKer s M := by
  have e : x k i hki (Polynomial.C t) * x i j hij h * (x k i hki (Polynomial.C t))⁻¹ =
      x k j hkj (Polynomial.C t * h) * x i j hij h := by
    rw [← x_commutator k i j hki hij hkj (Polynomial.C t) h, commutatorElement_def]
    group
  rw [e]
  refine mul_mem (k2KarInj_x_mem k j hkj ?_) (k2KarInj_x_mem i j hij h0)
  rw [Polynomial.eval_mul, h0, mul_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInj_conj_mem_left

/-- **Generator-level conjugation closure** (`M ≥ 3`): every conjugate of a generator
`x_ij(h)`, `h(0) = 0`, by a constant root `x_kl(C t)`, `t ∈ L`, lies in `S = snd (ker fst)`.
The helpers are applied with `_` indices so the proof does not depend on `subst` naming. -/
theorem k2KarInj_conj_mem (hM : 3 ≤ M) (k l : Fin M) (hkl : k ≠ l) (t : Localization.Away s)
    (i j : Fin M) (hij : i ≠ j) {h : Polynomial (Localization.Away s)} (h0 : h.eval 0 = 0) :
    x k l hkl (Polynomial.C t) * x i j hij h * (x k l hkl (Polynomial.C t))⁻¹ ∈
      k2KarInj_sndKer s M := by
  by_cases hjk : j = k
  · subst hjk
    by_cases hli : l = i
    · subst hli
      exact k2KarInj_snd_conj_opp3 hM _ _ hij t h0
    · exact k2KarInj_conj_mem_right _ _ _ hij hkl (Ne.symm hli) t h0
  · by_cases hli : l = i
    · subst hli
      exact k2KarInj_conj_mem_left _ _ _ hij hkl (Ne.symm hjk) t h0
    · rw [(x_commute_of_ne k l i j hkl hij hli hjk (Polynomial.C t) h).eq,
        mul_inv_cancel_right]
      exact k2KarInj_x_mem i j hij h0

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInj_conj_mem

end KarInjConj

end GroupApproximation.BooneHigman.Metabelian.ElemFP
