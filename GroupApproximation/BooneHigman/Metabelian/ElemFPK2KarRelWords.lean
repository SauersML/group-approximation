import Mathlib.Tactic.LinearCombination
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarRelBalance
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PullRelRing
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeDiagDilateSt
import GroupApproximation.Meta.AxiomGuard

/-!
# The `D`-words die after padding

Lane `bh-met-92u`, words module.  Notation: `P = k2DilateSt_pullback s`, `L = A_s`, `u = 1/s`.
Fix `t ∈ L`, `a ∈ A`, `n` with `t · λ(s^n) = λ a`, and `h ∈ L[X]`.  The witness word of
`ElemFPK2KarInjConj` (the element of `ker fst` whose `snd` is `x_ji(C t) x_ij(h') x_ji(C t)⁻¹`) is

`W(t, a, n; h) = ⁅col(k; lift(C uⁿ h), lift(C t · C uⁿ h)), row(k; const(-a), const(sⁿ))⁆`

(`k2KarRel_W`).  The pair `(a, n)` is not unique: `(s a, n + 1)` also works.  The `D`-word
`W(t, a, n; h) · W(t, s a, n + 1; h)⁻¹` measures that choice.

* `k2KarRel_W_succ`: with a fourth index, `W(t, a, n; h) = W(t, s a, n + 1; h)` exactly.  This is
  `k2KarRel_balance` with `σ = const s`, since `lift(C uⁿ⁺¹ h) · const s = lift(C uⁿ h)` and
  `const s · const(-a) = const(-(s a))`, `const s · const(sⁿ) = const(sⁿ⁺¹)`.
* `k2KarRel_D_dies`: in `St(M, P)` with only three indices `i, j, k` available, the `D`-word dies
  after padding `M ↦ M + 1`.  The new index `Fin.last M` is the fourth index.  (When `M ≥ 4` the
  `D`-word is already `1`.)
* `k2KarRel_W_fst`: `fst W = 1`, so every `W` lies in `ker fst`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

section KarRelRing

variable {A : Type*} [CommRing A] (s : A)

theorem k2KarRel_const_mul_lift (a : A) (f : Polynomial (Localization.Away s)) :
    k2PullRel_const s a * k2PullRel_lift s f =
      k2PullRel_lift s (Polynomial.C (algebraMap A (Localization.Away s) a) * f) := by
  refine k2PullRel_ext ?_ ?_
  · simp only [map_mul, k2PullRel_fst_const, k2PullRel_fst_lift, mul_zero]
  · simp only [map_mul, k2PullRel_snd_const, k2PullRel_snd_lift, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.C_mul]
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_const_mul_lift

theorem k2KarRel_lift_mul_const (f : Polynomial (Localization.Away s)) (a : A) :
    k2PullRel_lift s f * k2PullRel_const s a =
      k2PullRel_lift s (f * Polynomial.C (algebraMap A (Localization.Away s) a)) := by
  rw [mul_comm (k2PullRel_lift s f), k2KarRel_const_mul_lift, mul_comm (Polynomial.C _) f]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_lift_mul_const

/-- The row entries pair to zero with the column entries: `-a · c + sⁿ · (t c) = 0` in `P`. -/
theorem k2KarRel_rc_zero {t : Localization.Away s} {a : A} {n : ℕ}
    (ht : t * algebraMap A (Localization.Away s) (s ^ n) = algebraMap A (Localization.Away s) a)
    (f : Polynomial (Localization.Away s)) :
    k2PullRel_const s (-a) * k2PullRel_lift s f +
      k2PullRel_const s (s ^ n) * k2PullRel_lift s (Polynomial.C t * f) = 0 := by
  rw [k2KarRel_const_mul_lift, k2KarRel_const_mul_lift, k2PullRel_lift_add]
  have e : Polynomial.C (algebraMap A (Localization.Away s) (-a)) * f +
      Polynomial.C (algebraMap A (Localization.Away s) (s ^ n)) * (Polynomial.C t * f) =
        Polynomial.C 0 := by
    rw [map_neg, Polynomial.C_neg, ← ht, Polynomial.C_mul, Polynomial.C_0]
    ring
  rw [e, k2PullRel_lift_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_rc_zero

end KarRelRing

section KarRelWords

variable {A : Type*} [CommRing A] (s : A) {I : Type*} [Fintype I] [DecidableEq I]

/-- The witness word `W(t, a, n; h) ∈ ker fst` of `ElemFPK2KarInjConj`, in column/row form. -/
noncomputable def k2KarRel_W (i j k : I) (hik : i ≠ k) (hjk : j ≠ k) (t : Localization.Away s)
    (a : A) (n : ℕ) (h : Polynomial (Localization.Away s)) :
    SteinbergGroup I (k2DilateSt_pullback s) :=
  ⁅k2KarRel_col k i j hik hjk (k2PullRel_lift s (Polynomial.C (k2DilateSt_inv s ^ n) * h))
      (k2PullRel_lift s (Polynomial.C t * (Polynomial.C (k2DilateSt_inv s ^ n) * h))),
    k2KarRel_row k i j hik.symm hjk.symm (k2PullRel_const s (-a)) (k2PullRel_const s (s ^ n))⁆

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_W

theorem k2KarRel_W_fst (i j k : I) (hik : i ≠ k) (hjk : j ≠ k) (t : Localization.Away s)
    (a : A) (n : ℕ) (h : Polynomial (Localization.Away s)) :
    ringMap (k2PullRel_fst s) (k2KarRel_W s i j k hik hjk t a n h) = 1 := by
  rw [k2KarRel_W]
  simp only [map_commutatorElement, k2KarRel_col, map_mul, ringMap_x, k2PullRel_fst_lift,
    x_zero, one_mul, commutatorElement_one_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_W_fst

theorem k2KarRel_indexMap_W {J : Type*} [Fintype J] [DecidableEq J] (e : I ↪ J) (i j k : I)
    (hik : i ≠ k) (hjk : j ≠ k) (t : Localization.Away s) (a : A) (n : ℕ)
    (h : Polynomial (Localization.Away s)) :
    indexMap e (k2KarRel_W s i j k hik hjk t a n h) =
      k2KarRel_W s (e i) (e j) (e k) (e.injective.ne hik) (e.injective.ne hjk) t a n h := by
  rw [k2KarRel_W, k2KarRel_W, map_commutatorElement, k2KarRel_indexMap_col,
    k2KarRel_indexMap_row]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_indexMap_W

end KarRelWords

end GroupApproximation.BooneHigman.Metabelian.ElemFP
