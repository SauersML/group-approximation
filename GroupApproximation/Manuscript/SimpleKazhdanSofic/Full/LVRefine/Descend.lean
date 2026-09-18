import Mathlib.Tactic.Group
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVRefine.Roots
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCentral.Stabilization

/-!
# The Leavitt refinement homomorphism `St_n(R) → St_{n+1}(R)`

`simple_kazhdan_sofic_group.tex`, l.733-735 (`sec:questions`), cites Caprace--Rémy for infinite
finitely presented simple Kazhdan groups. On the Leavitt route to that claim, Khanh's Theorem 5.4
(arXiv:2609.08428, tex l.527-556) uses the refinement homomorphism `D_r : St_n(R) → St_{n+1}(R)`
of `eq:steinberg-refinement`.

The generator images `refineRoot` of `LVRefine.Roots` satisfy the adjacent-root relation
(`refineRoot_adjacent`, using `s0 t0 + s1 t1 = 1`), so they descend to the homomorphism
`refineHom L r`. Refining the last coordinate after one stabilization is a second stabilization
(`refineHom_castSuccStab`).
-/

namespace GroupApproximation
namespace Full
namespace LVRefine

open SteinbergGroup
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem commutator_mul_left_eq (a1 a2 c : G) :
    ⁅a1 * a2, c⁆ = a1 * ⁅a2, c⁆ * a1⁻¹ * ⁅a1, c⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutator_mul_right_eq (c b1 b2 : G) :
    ⁅c, b1 * b2⁆ = ⁅c, b1⁆ * b1 * ⁅c, b2⁆ * b1⁻¹ := by
  simp only [commutatorElement_def]
  group

theorem mul_conj_mul {f1 b f2 : G} (h : Commute b f2) : f1 * b * f2 * b⁻¹ = f1 * f2 := by
  rw [mul_assoc f1, mul_assoc f1, h.mul_inv_cancel]

end Group

variable {R : Type*} [Ring R] (L : LeavittFamily R) {n : ℕ} (r : Fin n)

theorem split_coeff (a b : R) : a * L.s1 * (L.t1 * b) + a * L.s0 * (L.t0 * b) = a * b :=
  calc a * L.s1 * (L.t1 * b) + a * L.s0 * (L.t0 * b)
        = a * (L.s0 * L.t0 + L.s1 * L.t1) * b := by
          simp only [mul_add, add_mul, mul_assoc]
          exact add_comm _ _
    _ = a * b := by rw [L.sum_range, mul_one]

/-- The refined generators satisfy the adjacent-root Steinberg relation
(Khanh Thm 5.4, `eq:steinberg-refinement`; `sec:questions` l.733-735). -/
theorem refineRoot_adjacent {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) :
    ⁅refineRoot L r i j hij a, refineRoot L r j k hjk b⁆ = refineRoot L r i k hik (a * b) := by
  by_cases hi : i = r
  · have hjr : j ≠ r := fun e => hij (hi.trans e.symm)
    have hkr : k ≠ r := fun e => hik (hi.trans e.symm)
    have hrj : r ≠ j := fun e => hjr e.symm
    have hrk : r ≠ k := fun e => hkr e.symm
    rw [refineRoot_of_row L r hij a hi, refineRoot_of_plain L r hjk b hjr hkr,
      refineRoot_of_row L r hik (a * b) hi, commutator_mul_left_eq,
      x_commutator (Fin.last n) (Fin.castSucc j) (Fin.castSucc k) (Fin.castSucc_ne_last j).symm
        (cs_ne hjk) (Fin.castSucc_ne_last k).symm (L.t1 * a) b,
      x_commutator (Fin.castSucc r) (Fin.castSucc j) (Fin.castSucc k) (cs_ne hrj) (cs_ne hjk)
        (cs_ne hrk) (L.t0 * a) b,
      (x_commute_of_ne (Fin.castSucc r) (Fin.castSucc j) (Fin.last n) (Fin.castSucc k)
        (cs_ne hrj) (Fin.castSucc_ne_last k).symm (Fin.castSucc_ne_last j) (cs_ne hkr)
        (L.t0 * a) (L.t1 * a * b)).mul_inv_cancel,
      mul_assoc L.t1, mul_assoc L.t0]
    exact (x_commute_of_ne _ _ _ _ _ _ (cs_ne hkr) (Fin.castSucc_ne_last k) _ _).eq
  · have hri : r ≠ i := fun e => hi e.symm
    have hki : k ≠ i := fun e => hik e.symm
    by_cases hj : j = r
    · have hkr : k ≠ r := fun e => hjk (hj.trans e.symm)
      have hrk : r ≠ k := fun e => hkr e.symm
      rw [refineRoot_of_col L r hij a hi hj, refineRoot_of_row L r hjk b hj,
        refineRoot_of_plain L r hik (a * b) hi hkr, commutator_mul_left_eq,
        commutator_mul_right_eq, commutator_mul_right_eq,
        (x_commute_of_ne (Fin.castSucc i) (Fin.last n) (Fin.castSucc r) (Fin.castSucc k)
          (Fin.castSucc_ne_last i) (cs_ne hrk) (Fin.castSucc_ne_last r).symm (cs_ne hki)
          (a * L.s1) (L.t0 * b)).commutator_eq,
        x_commutator (Fin.castSucc i) (Fin.last n) (Fin.castSucc k) (Fin.castSucc_ne_last i)
          (Fin.castSucc_ne_last k).symm (cs_ne hik) (a * L.s1) (L.t1 * b),
        x_commutator (Fin.castSucc i) (Fin.castSucc r) (Fin.castSucc k) (cs_ne hi) (cs_ne hrk)
          (cs_ne hik) (a * L.s0) (L.t0 * b),
        (x_commute_of_ne (Fin.castSucc i) (Fin.castSucc r) (Fin.last n) (Fin.castSucc k)
          (cs_ne hi) (Fin.castSucc_ne_last k).symm (Fin.castSucc_ne_last r) (cs_ne hki)
          (a * L.s0) (L.t1 * b)).commutator_eq,
        one_mul, mul_one,
        (x_commute_of_ne (Fin.castSucc r) (Fin.castSucc k) (Fin.castSucc i) (Fin.castSucc k)
          (cs_ne hrk) (cs_ne hik) (cs_ne hki) (cs_ne hkr)
          (L.t0 * b) (a * L.s1 * (L.t1 * b))).mul_inv_cancel,
        mul_inv_cancel_right,
        (x_commute_of_ne (Fin.castSucc i) (Fin.castSucc r) (Fin.castSucc i) (Fin.castSucc k)
          (cs_ne hi) (cs_ne hik) (cs_ne hri) (cs_ne hki)
          (a * L.s0) (a * L.s1 * (L.t1 * b))).mul_inv_cancel,
        x_mul, split_coeff]
    · by_cases hk : k = r
      · rw [refineRoot_of_plain L r hij a hi hj, refineRoot_of_col L r hjk b hj hk,
          refineRoot_of_col L r hik (a * b) hi hk, commutator_mul_right_eq,
          x_commutator (Fin.castSucc i) (Fin.castSucc j) (Fin.castSucc r) (cs_ne hij) (cs_ne hj)
            (cs_ne hi) a (b * L.s0),
          x_commutator (Fin.castSucc i) (Fin.castSucc j) (Fin.last n) (cs_ne hij)
            (Fin.castSucc_ne_last j) (Fin.castSucc_ne_last i) a (b * L.s1),
          mul_conj_mul (x_commute_of_ne (Fin.castSucc j) (Fin.castSucc r) (Fin.castSucc i)
            (Fin.last n) (cs_ne hj) (Fin.castSucc_ne_last i) (cs_ne hri)
            (Fin.castSucc_ne_last j).symm (b * L.s0) (a * (b * L.s1))),
          mul_assoc a b L.s0, mul_assoc a b L.s1]
      · rw [refineRoot_of_plain L r hij a hi hj, refineRoot_of_plain L r hjk b hj hk,
          refineRoot_of_plain L r hik (a * b) hi hk]
        exact x_commutator _ _ _ _ _ _ a b

/-- The generator images as a function on Steinberg generators. -/
def refineGen (g : SteinbergGenerator (Fin n) R) : SteinbergGroup (Fin (n + 1)) R :=
  refineRoot L r g.row g.column g.row_ne_column g.coefficient

theorem refineGen_kills_relations (w : FreeGroup (SteinbergGenerator (Fin n) R))
    (hw : w ∈ relations (I := Fin n) (R := R)) : FreeGroup.lift (refineGen L r) w = 1 := by
  change IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [mul_inv_eq_one]
      exact refineRoot_add L r hij a b
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of]
      exact (refineRoot_commute L r hij hkl hjk hli a b).commutator_eq
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      rw [mul_inv_eq_one]
      exact refineRoot_adjacent L r hij hjk hik a b

/-- Khanh's refinement homomorphism `D_r : St_n(R) → St_{n+1}(R)` splitting the coordinate `r`
along the Leavitt family `L` (Khanh Thm 5.4, `eq:steinberg-refinement`;
`sec:questions` l.733-735). -/
def refineHom {n : ℕ} (r : Fin n) : SteinbergGroup (Fin n) R →* SteinbergGroup (Fin (n + 1)) R :=
  PresentedGroup.toGroup (f := refineGen L r) (refineGen_kills_relations L r)

theorem refineHom_x (i j : Fin n) (hij : i ≠ j) (a : R) :
    refineHom L r (x i j hij a) = refineRoot L r i j hij a := by
  exact PresentedGroup.toGroup.of _

/-- Refining the new last coordinate after a stabilization is a second stabilization. -/
theorem refineHom_castSuccStab (m : ℕ) (g : SteinbergGroup (Fin (m + 1)) R) :
    refineHom L (Fin.last (m + 1)) (LVCentral.castSuccStab (m + 1) R g) =
      LVCentral.castSuccStab (m + 2) R (LVCentral.castSuccStab (m + 1) R g) := by
  have h : (refineHom L (Fin.last (m + 1))).comp (LVCentral.castSuccStab (m + 1) R) =
      (LVCentral.castSuccStab (m + 2) R).comp (LVCentral.castSuccStab (m + 1) R) := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change refineHom L (Fin.last (m + 1)) (LVCentral.castSuccStab (m + 1) R (x i j hij a)) =
      LVCentral.castSuccStab (m + 2) R (LVCentral.castSuccStab (m + 1) R (x i j hij a))
    rw [LVCentral.castSuccStab_x, refineHom_x,
      refineRoot_of_plain L (Fin.last (m + 1)) (cs_ne hij) a (Fin.castSucc_ne_last i)
        (Fin.castSucc_ne_last j)]
    exact (LVCentral.castSuccStab_x _ _ _ a).symm
  exact DFunLike.congr_fun h g

end LVRefine
end Full
end GroupApproximation
