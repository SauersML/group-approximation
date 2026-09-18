import GroupApproximation.BooneHigman.Metabelian.VdKStabRows
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import GroupApproximation.Meta.AxiomGuard

/-!
# Elementary Krull dimension via collapses, and boundary ideals

Lane `bh-met-90m`, part 1.  Route (Coquand–Lombardi, constructive Heitmann / Bass stable range):

* `vdkSR_collapse n x a m = x₀^{m₀} (x₁^{m₁} (⋯ (1 + a_{n-1} x_{n-1}) ⋯) + a₀ x₀)`.
* `vdkSR_KdimLE I n`: every `n`-tuple has a collapse lying in `I` ("`Kdim (R/I) < n`").
* `vdkSR_bdry I y = {w | ∃ t m, y^m (w - y t) ∈ I}`, the boundary ideal; `KdimLE I (n+1)`
  implies `KdimLE (bdry I y) n` (`vdkSR_kdimLE_bdry`).
* `vdkSR_UnimodMod I v`: `v` is unimodular modulo `I`.
* `vdkSR_quot_key`: the ring identity behind the induction step (the idempotent
  `E = 1 - (YT)^{m+1}` satisfies `Y^{m+1} E = 0` and `E ∈ (Y)`, hence `E = 0`, hence `Y = 0`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- The collapse `x₀^{m₀} (collapse (tail) + a₀ x₀)`, with `collapse` of the empty tuple `1`. -/
def vdkSR_collapse {R : Type*} [CommRing R] :
    (n : ℕ) → (Fin n → R) → (Fin n → R) → (Fin n → ℕ) → R
  | 0, _, _, _ => 1
  | n + 1, x, a, m =>
    x 0 ^ m 0 * (vdkSR_collapse n (Fin.tail x) (Fin.tail a) (Fin.tail m) + a 0 * x 0)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_collapse

section Collapse

variable {R : Type*} [CommRing R]

theorem vdkSR_collapse_zero (x a : Fin 0 → R) (m : Fin 0 → ℕ) :
    vdkSR_collapse 0 x a m = 1 :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_collapse_zero

theorem vdkSR_collapse_succ (n : ℕ) (x a : Fin (n + 1) → R) (m : Fin (n + 1) → ℕ) :
    vdkSR_collapse (n + 1) x a m =
      x 0 ^ m 0 * (vdkSR_collapse n (Fin.tail x) (Fin.tail a) (Fin.tail m) + a 0 * x 0) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_collapse_succ

/-- `Kdim (R / I) < n` in the elementary sense: every `n`-tuple has a collapse in `I`. -/
def vdkSR_KdimLE (I : Ideal R) (n : ℕ) : Prop :=
  ∀ x : Fin n → R, ∃ a : Fin n → R, ∃ m : Fin n → ℕ, vdkSR_collapse n x a m ∈ I

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_KdimLE

/-- The boundary ideal `{w | ∃ t m, y^m (w - y t) ∈ I}`. -/
def vdkSR_bdry (I : Ideal R) (y : R) : Ideal R where
  carrier := {w | ∃ t : R, ∃ m : ℕ, y ^ m * (w - y * t) ∈ I}
  add_mem' := by
    rintro w w' ⟨t, m, h⟩ ⟨t', m', h'⟩
    have key : y ^ (m + m') * (w + w' - y * (t + t')) ∈ I := by
      rw [show y ^ (m + m') * (w + w' - y * (t + t')) =
          y ^ m' * (y ^ m * (w - y * t)) + y ^ m * (y ^ m' * (w' - y * t')) by ring]
      exact I.add_mem (I.mul_mem_left _ h) (I.mul_mem_left _ h')
    exact ⟨t + t', m + m', key⟩
  zero_mem' := by
    have key : y ^ 0 * ((0 : R) - y * 0) ∈ I := by
      rw [show y ^ 0 * ((0 : R) - y * 0) = 0 by ring]
      exact I.zero_mem
    exact ⟨0, 0, key⟩
  smul_mem' := by
    rintro c w ⟨t, m, h⟩
    have key : y ^ m * (c • w - y * (c * t)) ∈ I := by
      rw [smul_eq_mul, show y ^ m * (c * w - y * (c * t)) = c * (y ^ m * (w - y * t)) by ring]
      exact I.mul_mem_left c h
    exact ⟨c * t, m, key⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_bdry

theorem vdkSR_mem_bdry {I : Ideal R} {y w : R} :
    w ∈ vdkSR_bdry I y ↔ ∃ t : R, ∃ m : ℕ, y ^ m * (w - y * t) ∈ I :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_mem_bdry

/-- Passing to the boundary ideal lowers the elementary dimension bound by one. -/
theorem vdkSR_kdimLE_bdry {I : Ideal R} {n : ℕ} (h : vdkSR_KdimLE I (n + 1)) (y : R) :
    vdkSR_KdimLE (vdkSR_bdry I y) n := by
  intro x
  obtain ⟨a, m, ha⟩ := h (Fin.cons y x : Fin (n + 1) → R)
  rw [vdkSR_collapse_succ, Fin.tail_cons, Fin.cons_zero] at ha
  have key : y ^ m 0 * (vdkSR_collapse n x (Fin.tail a) (Fin.tail m) - y * -a 0) ∈ I := by
    rw [show y ^ m 0 * (vdkSR_collapse n x (Fin.tail a) (Fin.tail m) - y * -a 0) =
        y ^ m 0 * (vdkSR_collapse n x (Fin.tail a) (Fin.tail m) + a 0 * y) by ring]
    exact ha
  exact ⟨Fin.tail a, Fin.tail m, vdkSR_mem_bdry.mpr ⟨-a 0, m 0, key⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_kdimLE_bdry

/-- The row `v` is unimodular modulo `I`. -/
def vdkSR_UnimodMod (I : Ideal R) {n : ℕ} (v : Fin n → R) : Prop :=
  ∃ w : Fin n → R, 1 - ∑ i, v i * w i ∈ I

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_UnimodMod

theorem vdkSR_unimodMod_of_one_mem {I : Ideal R} {n : ℕ} {v : Fin n → R}
    (h : (1 : R) ∈ Ideal.span (Set.range v) ⊔ I) : vdkSR_UnimodMod I v := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hy
  have e : ∑ i, v i * c i = y := by
    rw [← hc]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have key : 1 - ∑ i, v i * c i ∈ I := by
    rw [e, show (1 : R) - y = z by linear_combination (-1 : R) * hyz]
    exact hz
  exact ⟨c, key⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_unimodMod_of_one_mem

end Collapse

/-- The ring identity of the induction step: in a commutative ring, `Y^m (1 - YT) = 0`,
`YS + CU = 1` and `Y + U (1 - (YT)^{m+1}) C = 0` force `1 = 0`. -/
theorem vdkSR_quot_key {Q : Type*} [CommRing Q] (Y T S C U : Q) (m : ℕ)
    (h1 : Y ^ m * (1 - Y * T) = 0) (h2 : Y * S + C * U = 1)
    (h3 : Y + U * (1 - (Y * T) ^ (m + 1)) * C = 0) : (1 : Q) = 0 := by
  obtain ⟨E, hE⟩ : ∃ E : Q, E = 1 - (Y * T) ^ (m + 1) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ := one_sub_dvd_one_sub_pow (Y * T) (m + 1)
  have hP : (Y * T) ^ (m + 1) = Y ^ (m + 1) * T ^ (m + 1) := mul_pow Y T (m + 1)
  have hYE : Y ^ (m + 1) * E = 0 := by
    linear_combination Y ^ (m + 1) * hE + Y ^ (m + 1) * hG + G * Y * h1
  obtain ⟨D, hD⟩ : ∃ D : Q, D = S * E - 1 := ⟨_, rfl⟩
  have hEY : E = Y * D := by
    linear_combination h3 + U * C * hE - E * h2 - Y * hD
  have hidem : IsIdempotentElem E :=
    isIdempotentElem_iff.mpr (by linear_combination E * hE - T ^ (m + 1) * hYE - E * hP)
  have hp2 : E ^ (m + 1 + 1) = E := IsIdempotentElem.pow_succ_eq (m + 1) hidem
  have hpow : E ^ (m + 1) = Y ^ (m + 1) * D ^ (m + 1) := by
    rw [← mul_pow, ← hEY]
  have hE0 : E = 0 := by
    linear_combination (-1 : Q) * hp2 + E * hpow + D ^ (m + 1) * hYE
  have hY0 : Y = 0 := by
    linear_combination h3 + U * C * hE - U * C * hE0
  linear_combination hE0 - hE + Y ^ m * T ^ (m + 1) * hY0 + hP

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkSR_quot_key

end GroupApproximation.BooneHigman.Metabelian.ElemFP
