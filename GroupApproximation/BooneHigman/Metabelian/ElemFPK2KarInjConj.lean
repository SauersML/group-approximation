import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
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
