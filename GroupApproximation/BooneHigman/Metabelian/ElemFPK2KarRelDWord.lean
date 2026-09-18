import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarRelWords
import GroupApproximation.Meta.AxiomGuard

/-!
# `W(t, a, n; h) = W(t, s a, n + 1; h)` with four indices; the `D`-word dies after padding

Lane `bh-met-92u`, `D`-word module.  See `ElemFPK2KarRelWords` for the notation.

* `k2KarRel_W_succ`: given a fourth index `l`, `W(t, a, n; h) = W(t, s a, n + 1; h)`.  This is
  `k2KarRel_balance` with `σ = const s` applied to the entries of `W(t, s a, n + 1; h)`.
* `k2KarRel_D_dies`: for `i, j, k ∈ Fin M`, the `D`-word
  `W(t, a, n; h) · W(t, s a, n + 1; h)⁻¹` dies after padding to `Fin (M + 1)`, with
  `Fin.last M` as the fourth index.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

section KarRelDWord

variable {A : Type*} [CommRing A] (s : A)

/-- **`W(t, a, n; h) = W(t, s a, n + 1; h)`** given a fourth index `l`. -/
theorem k2KarRel_W_succ {I : Type*} [Fintype I] [DecidableEq I] (i j k l : I) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l)
    {t : Localization.Away s} {a : A} {n : ℕ}
    (ht : t * algebraMap A (Localization.Away s) (s ^ n) = algebraMap A (Localization.Away s) a)
    (h : Polynomial (Localization.Away s)) :
    k2KarRel_W s i j k hik hjk t a n h = k2KarRel_W s i j k hik hjk t (s * a) (n + 1) h := by
  have hC : Polynomial.C (k2DilateSt_inv s ^ (n + 1)) *
      Polynomial.C (algebraMap A (Localization.Away s) s) =
        Polynomial.C (k2DilateSt_inv s ^ n) := by
    rw [← Polynomial.C_mul, pow_succ, mul_assoc, k2DilateSt_inv_mul, mul_one]
  have E1 : k2PullRel_lift s (Polynomial.C (k2DilateSt_inv s ^ (n + 1)) * h) *
      k2PullRel_const s s = k2PullRel_lift s (Polynomial.C (k2DilateSt_inv s ^ n) * h) := by
    rw [k2KarRel_lift_mul_const]
    exact congrArg (k2PullRel_lift s) (by linear_combination h * hC)
  have E2 : k2PullRel_lift s
      (Polynomial.C t * (Polynomial.C (k2DilateSt_inv s ^ (n + 1)) * h)) * k2PullRel_const s s =
        k2PullRel_lift s (Polynomial.C t * (Polynomial.C (k2DilateSt_inv s ^ n) * h)) := by
    rw [k2KarRel_lift_mul_const]
    exact congrArg (k2PullRel_lift s) (by linear_combination (Polynomial.C t * h) * hC)
  have E3 : k2PullRel_const s s * k2PullRel_const s (-a) = k2PullRel_const s (-(s * a)) := by
    rw [← map_mul, mul_neg]
  have E4 : k2PullRel_const s s * k2PullRel_const s (s ^ n) =
      k2PullRel_const s (s ^ (n + 1)) := by
    rw [← map_mul, pow_succ']
  have T := k2KarRel_balance i j k l hij hik hjk hil hjl hkl (k2PullRel_const s s)
    (k2KarRel_rc_zero s ht (Polynomial.C (k2DilateSt_inv s ^ (n + 1)) * h))
  rw [E1, E2, E3, E4] at T
  rw [k2KarRel_W, k2KarRel_W]
  exact T

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_W_succ

/-- **The `D`-word dies after padding.**  Only three indices `i, j, k` of `Fin M` are used; the
padding `Fin M ↪ Fin (M + 1)` supplies the fourth index `Fin.last M`. -/
theorem k2KarRel_D_dies {M : ℕ} (i j k : Fin M) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {t : Localization.Away s} {a : A} {n : ℕ}
    (ht : t * algebraMap A (Localization.Away s) (s ^ n) = algebraMap A (Localization.Away s) a)
    (h : Polynomial (Localization.Away s)) :
    cubeDiagDilate_StDies (k2KarRel_W s i j k hik hjk t a n h *
      (k2KarRel_W s i j k hik hjk t (s * a) (n + 1) h)⁻¹) := by
  refine ⟨M + 1, Nat.le_add_right M 1, ?_⟩
  have hl : ∀ m : Fin M, Fin.castLEEmb (Nat.le_add_right M 1) m ≠ Fin.last M :=
    fun m e => by
      have h1 : m.val = M := congrArg Fin.val e
      have h2 := m.isLt
      omega
  have hinj := (Fin.castLEEmb (Nat.le_add_right M 1)).injective
  rw [map_mul, map_inv, k2KarRel_indexMap_W, k2KarRel_indexMap_W,
    k2KarRel_W_succ s _ _ _ (Fin.last M) (hinj.ne hij) (hinj.ne hik) (hinj.ne hjk) (hl i)
      (hl j) (hl k) ht h, mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_D_dies

end KarRelDWord

end GroupApproximation.BooneHigman.Metabelian.ElemFP
