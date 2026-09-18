import Mathlib.Data.Fin.SuccPred
import GroupApproximation.Steinberg.Basic
import GroupApproximation.Leavitt.Leavitt

/-!
# Leavitt refinement of Steinberg generators

`simple_kazhdan_sofic_group.tex`, l.733-735 (`sec:questions`), cites Caprace--Rémy for infinite
finitely presented simple Kazhdan groups. On the Leavitt route to that claim, Khanh's Theorem 5.4
(arXiv:2609.08428, tex l.527-556) uses the refinement homomorphism `D_r : St_n(R) → St_{n+1}(R)`
attached to a binary Leavitt family `e = s0`, `f = s1`, `e* = t0`, `f* = t1`
(formula `eq:steinberg-refinement`).

We index the refined coordinate `r : Fin n` by `Fin.castSucc r` (coefficients `s0`, `t0`) and by
`Fin.last n` (coefficients `s1`, `t1`); every other coordinate `i` becomes `Fin.castSucc i`:

* `D X_{rj}(a) = x_{r j}(t0 a) · x_{∞ j}(t1 a)`,
* `D X_{ir}(a) = x_{i r}(a s0) · x_{i ∞}(a s1)`,
* `D X_{ij}(a) = x_{ij}(a)` otherwise.

This file defines these generator images (`refineRoot`) and checks the additivity and the
commutation Steinberg relations for them. The adjacent-root relation and the descended
homomorphism are in `LVRefine.Descend`.
-/

namespace GroupApproximation
namespace Full
namespace LVRefine

open SteinbergGroup

variable {R : Type*} [Ring R] (L : LeavittFamily R) {n : ℕ} (r : Fin n)

theorem cs_ne {i j : Fin n} (h : i ≠ j) : Fin.castSucc i ≠ Fin.castSucc j :=
  fun e => h (Fin.castSucc_inj.mp e)

/-- The image of the Steinberg generator `x_{ij}(a)` under Khanh's refinement `D_r`
(Khanh Thm 5.4, `eq:steinberg-refinement`; `sec:questions` l.733-735). -/
def refineRoot (i j : Fin n) (hij : i ≠ j) (a : R) : SteinbergGroup (Fin (n + 1)) R :=
  if hi : i = r then
    x (Fin.castSucc r) (Fin.castSucc j) (cs_ne fun e => hij (hi.trans e)) (L.t0 * a) *
      x (Fin.last n) (Fin.castSucc j) (Fin.castSucc_ne_last j).symm (L.t1 * a)
  else if j = r then
    x (Fin.castSucc i) (Fin.castSucc r) (cs_ne hi) (a * L.s0) *
      x (Fin.castSucc i) (Fin.last n) (Fin.castSucc_ne_last i) (a * L.s1)
  else x (Fin.castSucc i) (Fin.castSucc j) (cs_ne hij) a

theorem refineRoot_of_row {i j : Fin n} (hij : i ≠ j) (a : R) (hi : i = r) :
    refineRoot L r i j hij a =
      x (Fin.castSucc r) (Fin.castSucc j) (cs_ne fun e => hij (hi.trans e)) (L.t0 * a) *
        x (Fin.last n) (Fin.castSucc j) (Fin.castSucc_ne_last j).symm (L.t1 * a) := by
  rw [refineRoot]
  exact dif_pos hi

theorem refineRoot_of_col {i j : Fin n} (hij : i ≠ j) (a : R) (hi : i ≠ r) (hj : j = r) :
    refineRoot L r i j hij a =
      x (Fin.castSucc i) (Fin.castSucc r) (cs_ne hi) (a * L.s0) *
        x (Fin.castSucc i) (Fin.last n) (Fin.castSucc_ne_last i) (a * L.s1) := by
  rw [refineRoot]
  exact (dif_neg hi).trans (if_pos hj)

theorem refineRoot_of_plain {i j : Fin n} (hij : i ≠ j) (a : R) (hi : i ≠ r) (hj : j ≠ r) :
    refineRoot L r i j hij a = x (Fin.castSucc i) (Fin.castSucc j) (cs_ne hij) a := by
  rw [refineRoot]
  exact (dif_neg hi).trans (if_neg hj)

/-- The refined generators satisfy the additivity relation. -/
theorem refineRoot_add {i j : Fin n} (hij : i ≠ j) (a b : R) :
    refineRoot L r i j hij a * refineRoot L r i j hij b = refineRoot L r i j hij (a + b) := by
  by_cases hi : i = r
  · have hjr : j ≠ r := fun e => hij (hi.trans e.symm)
    rw [refineRoot_of_row L r hij a hi, refineRoot_of_row L r hij b hi,
      refineRoot_of_row L r hij (a + b) hi, mul_add, mul_add, ← x_mul, ← x_mul]
    exact (x_commute_of_ne _ _ _ _ _ _ (cs_ne hjr) (Fin.castSucc_ne_last j) _ _).mul_mul_mul_comm
      _ _
  · by_cases hj : j = r
    · rw [refineRoot_of_col L r hij a hi hj, refineRoot_of_col L r hij b hi hj,
        refineRoot_of_col L r hij (a + b) hi hj, add_mul, add_mul, ← x_mul, ← x_mul]
      exact (x_commute_of_ne _ _ _ _ _ _ (Fin.castSucc_ne_last i).symm
        (cs_ne fun e => hi e.symm) _ _).mul_mul_mul_comm _ _
    · rw [refineRoot_of_plain L r hij a hi hj, refineRoot_of_plain L r hij b hi hj,
        refineRoot_of_plain L r hij (a + b) hi hj, x_mul]

/-- The refined generators satisfy the commutation relation for non-adjacent roots. -/
theorem refineRoot_commute {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (a b : R) :
    Commute (refineRoot L r i j hij a) (refineRoot L r k l hkl b) := by
  by_cases hi : i = r
  · have hjr : j ≠ r := fun e => hij (hi.trans e.symm)
    have hlr : l ≠ r := fun e => hli (e.trans hi.symm)
    rw [refineRoot_of_row L r hij a hi]
    by_cases hk : k = r
    · rw [refineRoot_of_row L r hkl b hk]
      refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_)
      · exact x_commute_of_ne _ _ _ _ _ _ (cs_ne hjr) (cs_ne hlr) _ _
      · exact x_commute_of_ne _ _ _ _ _ _ (Fin.castSucc_ne_last j) (cs_ne hlr) _ _
      · exact x_commute_of_ne _ _ _ _ _ _ (cs_ne hjr) (Fin.castSucc_ne_last l) _ _
      · exact x_commute_of_ne _ _ _ _ _ _ (Fin.castSucc_ne_last j) (Fin.castSucc_ne_last l) _ _
    · by_cases hl : l = r
      · exact absurd hl hlr
      · rw [refineRoot_of_plain L r hkl b hk hl]
        refine Commute.mul_left ?_ ?_
        · exact x_commute_of_ne _ _ _ _ _ _ (cs_ne hjk) (cs_ne hlr) _ _
        · exact x_commute_of_ne _ _ _ _ _ _ (cs_ne hjk) (Fin.castSucc_ne_last l) _ _
  · have hri : r ≠ i := fun e => hi e.symm
    by_cases hj : j = r
    · have hkr : k ≠ r := fun e => hjk (hj.trans e.symm)
      have hrk : r ≠ k := fun e => hkr e.symm
      rw [refineRoot_of_col L r hij a hi hj]
      by_cases hk : k = r
      · exact absurd hk hkr
      · by_cases hl : l = r
        · rw [refineRoot_of_col L r hkl b hk hl]
          refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_)
          · exact x_commute_of_ne _ _ _ _ _ _ (cs_ne hrk) (cs_ne hri) _ _
          · exact x_commute_of_ne _ _ _ _ _ _ (cs_ne hrk) (Fin.castSucc_ne_last i).symm _ _
          · exact x_commute_of_ne _ _ _ _ _ _ (Fin.castSucc_ne_last k).symm (cs_ne hri) _ _
          · exact x_commute_of_ne _ _ _ _ _ _ (Fin.castSucc_ne_last k).symm
              (Fin.castSucc_ne_last i).symm _ _
        · rw [refineRoot_of_plain L r hkl b hk hl]
          refine Commute.mul_left ?_ ?_
          · exact x_commute_of_ne _ _ _ _ _ _ (cs_ne hrk) (cs_ne hli) _ _
          · exact x_commute_of_ne _ _ _ _ _ _ (Fin.castSucc_ne_last k).symm (cs_ne hli) _ _
    · rw [refineRoot_of_plain L r hij a hi hj]
      by_cases hk : k = r
      · rw [refineRoot_of_row L r hkl b hk]
        refine Commute.mul_right ?_ ?_
        · exact x_commute_of_ne _ _ _ _ _ _ (cs_ne hj) (cs_ne hli) _ _
        · exact x_commute_of_ne _ _ _ _ _ _ (Fin.castSucc_ne_last j) (cs_ne hli) _ _
      · by_cases hl : l = r
        · rw [refineRoot_of_col L r hkl b hk hl]
          refine Commute.mul_right ?_ ?_
          · exact x_commute_of_ne _ _ _ _ _ _ (cs_ne hjk) (cs_ne hri) _ _
          · exact x_commute_of_ne _ _ _ _ _ _ (cs_ne hjk) (Fin.castSucc_ne_last i).symm _ _
        · rw [refineRoot_of_plain L r hkl b hk hl]
          exact x_commute_of_ne _ _ _ _ _ _ (cs_ne hjk) (cs_ne hli) _ _

end LVRefine
end Full
end GroupApproximation
