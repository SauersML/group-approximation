import Mathlib.Data.Matrix.Basis
import GroupApproximation.Leavitt.Leavitt
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCentral.Stabilization

/-!
# Refinement and contraction of coordinate vectors

`simple_kazhdan_sofic_group.tex`, l.733-735 (`sec:questions`), cites Caprace--Rémy for infinite
finitely presented simple Kazhdan groups. On the Leavitt route to that claim, Khanh's Theorem 5.4
(arXiv:2609.08428, tex l.527-556) shows that the refinement `D_r : St_n(R) → St_{n+1}(R)` maps
`K₂(n, R)` onto `K₂(n+1, R)`.

We detect `K₂` through the action of `St_n(R)` on column vectors `Fin n → R`
(`vecAct g v = elMat (projection g) *ᵥ v`). The coordinate `r` of a vector is split along the
Leavitt family `L` (`splitVec`, with coefficients `t0`, `t1`), and joined back (`joinVec`, with
coefficients `s0`, `s1`). These two maps are mutually inverse bijections
(`joinVec_splitVec`, `splitVec_joinVec`), by the Leavitt relations. An element acting
trivially on all vectors lies in `K₂` (`projection_eq_one_of_vecAct`).
-/

namespace GroupApproximation
namespace Full
namespace LVRefine

open SteinbergGroup ElementarySimplicity
open scoped Matrix

variable {R : Type*} [Ring R] (L : LeavittFamily R) {n : ℕ} (r : Fin n)

/-- Split the coordinate `r` of `v` into `castSucc r` (coefficient `t0`) and `last` (coefficient
`t1`) (Khanh Thm 5.4; `sec:questions` l.733-735). -/
def splitVec (v : Fin n → R) (p : Fin (n + 1)) : R :=
  Fin.lastCases (motive := fun _ => R) (L.t1 * v r)
    (fun k => if k = r then L.t0 * v r else v k) p

theorem splitVec_last (v : Fin n → R) : splitVec L r v (Fin.last n) = L.t1 * v r := by
  simp only [splitVec, Fin.lastCases_last]

theorem splitVec_castSucc (v : Fin n → R) (k : Fin n) :
    splitVec L r v (Fin.castSucc k) = if k = r then L.t0 * v r else v k := by
  simp only [splitVec, Fin.lastCases_castSucc]

theorem splitVec_castSucc_self (v : Fin n → R) :
    splitVec L r v (Fin.castSucc r) = L.t0 * v r := by
  rw [splitVec_castSucc]
  exact if_pos rfl

theorem splitVec_castSucc_of_ne (v : Fin n → R) {k : Fin n} (hk : k ≠ r) :
    splitVec L r v (Fin.castSucc k) = v k := by
  rw [splitVec_castSucc]
  exact if_neg hk

/-- Join the coordinates `castSucc r` and `last` of `w` back into the coordinate `r`
(coefficients `s0`, `s1`). -/
def joinVec (w : Fin (n + 1) → R) (k : Fin n) : R :=
  if k = r then L.s0 * w (Fin.castSucc r) + L.s1 * w (Fin.last n) else w (Fin.castSucc k)

theorem joinVec_self (w : Fin (n + 1) → R) :
    joinVec L r w r = L.s0 * w (Fin.castSucc r) + L.s1 * w (Fin.last n) := by
  rw [joinVec]
  exact if_pos rfl

theorem joinVec_of_ne (w : Fin (n + 1) → R) {k : Fin n} (hk : k ≠ r) :
    joinVec L r w k = w (Fin.castSucc k) := by
  rw [joinVec]
  exact if_neg hk

/-- Contraction undoes refinement, by `s0 t0 + s1 t1 = 1`. -/
theorem joinVec_splitVec (v : Fin n → R) : joinVec L r (splitVec L r v) = v := by
  funext k
  by_cases hk : k = r
  · rw [hk, joinVec_self, splitVec_castSucc_self, splitVec_last, ← mul_assoc, ← mul_assoc,
      ← add_mul, L.sum_range, one_mul]
  · rw [joinVec_of_ne L r _ hk, splitVec_castSucc_of_ne L r v hk]

/-- Refinement undoes contraction, by `t_a s_b = δ_{ab}`. -/
theorem splitVec_joinVec (w : Fin (n + 1) → R) : splitVec L r (joinVec L r w) = w := by
  funext p
  induction p using Fin.lastCases with
  | last =>
      rw [splitVec_last, joinVec_self, mul_add, ← mul_assoc, ← mul_assoc, L.t1_s0, L.t1_s1,
        zero_mul, zero_add, one_mul]
  | cast k =>
      by_cases hk : k = r
      · rw [hk, splitVec_castSucc_self, joinVec_self, mul_add, ← mul_assoc, ← mul_assoc,
          L.t0_s0, L.t0_s1, zero_mul, add_zero, one_mul]
      · rw [splitVec_castSucc_of_ne L r _ hk, joinVec_of_ne L r w hk]

theorem splitVec_injective : Function.Injective (splitVec L r) := by
  intro v v' h
  rw [← joinVec_splitVec L r v, ← joinVec_splitVec L r v', h]

theorem joinVec_injective : Function.Injective (joinVec L r) := by
  intro w w' h
  rw [← splitVec_joinVec L r w, ← splitVec_joinVec L r w', h]

section Act

variable {m : ℕ}

/-- The action of `St_m(R)` on column vectors through the elementary projection. -/
def vecAct (g : SteinbergGroup (Fin m) R) (v : Fin m → R) : Fin m → R :=
  elMat (projection g) *ᵥ v

theorem vecAct_mul (g h : SteinbergGroup (Fin m) R) (v : Fin m → R) :
    vecAct (g * h) v = vecAct g (vecAct h v) := by
  change elMat (projection (g * h)) *ᵥ v = elMat (projection g) *ᵥ (elMat (projection h) *ᵥ v)
  rw [map_mul, elMat_mul, Matrix.mulVec_mulVec]

theorem vecAct_one (v : Fin m → R) : vecAct (1 : SteinbergGroup (Fin m) R) v = v := by
  change elMat (projection (1 : SteinbergGroup (Fin m) R)) *ᵥ v = v
  rw [map_one, elMat_one, Matrix.one_mulVec]

/-- The elementary transvection `x_{ij}(a)` adds `a v_j` to the coordinate `i`. -/
theorem vecAct_x_apply (i j : Fin m) (hij : i ≠ j) (a : R) (v : Fin m → R) (p : Fin m) :
    vecAct (x i j hij a) v p = v p + if p = i then a * v j else 0 := by
  change (elMat (projection (x i j hij a)) *ᵥ v) p = _
  rw [projection_x, LVCentral.elMat_elementaryRoot, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec, Pi.add_apply, Function.update_apply, Pi.zero_apply]

theorem vecAct_x_apply_self (i j : Fin m) (hij : i ≠ j) (a : R) (v : Fin m → R) :
    vecAct (x i j hij a) v i = v i + a * v j := by
  rw [vecAct_x_apply, if_pos rfl]

theorem vecAct_x_apply_of_ne (i j : Fin m) (hij : i ≠ j) (a : R) (v : Fin m → R) {p : Fin m}
    (hp : p ≠ i) : vecAct (x i j hij a) v p = v p := by
  rw [vecAct_x_apply, if_neg hp, add_zero]

/-- An element of `St_m(R)` fixing every column vector lies in `K₂(m, R)`. -/
theorem projection_eq_one_of_vecAct {g : SteinbergGroup (Fin m) R} (h : ∀ v, vecAct g v = v) :
    projection g = 1 := by
  refine elMat_injective (Matrix.mulVec_injective (funext fun v => ?_))
  rw [elMat_one, Matrix.one_mulVec]
  exact h v

theorem vecAct_eq_of_projection_eq_one {g : SteinbergGroup (Fin m) R} (h : projection g = 1)
    (v : Fin m → R) : vecAct g v = v := by
  change elMat (projection g) *ᵥ v = v
  rw [h, elMat_one, Matrix.one_mulVec]

end Act

end LVRefine
end Full
end GroupApproximation
