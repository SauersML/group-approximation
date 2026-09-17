import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2RefinementHom
import GroupApproximation.Meta.AxiomGuard

/-!
# The Leavitt refinement map descends to Steinberg groups

This file checks the adjacent Steinberg relation for `refineRoot`.  The case where the middle
index is the split index `r` is the only one that uses `s₀ t₀ + s₁ t₁ = 1`.  With it the map
descends to a group homomorphism `refineHom L r : St_n(R) →* St_{n+1}(R)`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

variable {R : Type*} [Ring R] (L : LeavittFamily R) {n : ℕ} (r : Fin n)

theorem refineRoot_adjacent {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) :
    ⁅refineRoot L r i j hij a, refineRoot L r j k hjk b⁆ = refineRoot L r i k hik (a * b) := by
  by_cases hi : i = r
  · have hj : ¬ j = r := fun h => hij (hi.trans h.symm)
    have hk : ¬ k = r := fun h => hik (hi.trans h.symm)
    rw [refineRoot_of_row L r hij a hi, refineRoot_of_plain L r hjk b hj hk,
      refineRoot_of_row L r hik (a * b) hi, comm_mul_left,
      refine_xcomm (Fin.castSucc_ne_last k).symm,
      refine_xcomm ((Fin.castSucc_injective n).ne hik),
      refine_conj (refine_xc (Fin.castSucc_ne_last j) ((Fin.castSucc_injective n).ne hik.symm)),
      mul_assoc L.t1 a b, mul_assoc L.t0 a b]
    exact (refine_xc ((Fin.castSucc_injective n).ne hik.symm) (Fin.castSucc_ne_last k)).eq
  · by_cases hj : j = r
    · have hk : ¬ k = r := fun h => hjk (hj.trans h.symm)
      have key : a * L.s1 * (L.t1 * b) + a * L.s0 * (L.t0 * b) = a * b := by
        calc a * L.s1 * (L.t1 * b) + a * L.s0 * (L.t0 * b)
            = a * (L.s1 * L.t1) * b + a * (L.s0 * L.t0) * b := by simp only [mul_assoc]
          _ = a * (L.s0 * L.t0 + L.s1 * L.t1) * b := by
            rw [add_comm (L.s0 * L.t0), mul_add, add_mul]
          _ = a * b := by rw [L.sum_range, mul_one]
      rw [refineRoot_of_col L r hij a hi hj, refineRoot_of_row L r hjk b hj,
        refineRoot_of_plain L r hik (a * b) hi hk, comm_mul_left, comm_mul_right, comm_mul_right,
        (refine_xc (Fin.castSucc_ne_last j).symm
          ((Fin.castSucc_injective n).ne hik.symm)).commutator_eq,
        (refine_xc (Fin.castSucc_ne_last j)
          ((Fin.castSucc_injective n).ne hik.symm)).commutator_eq,
        refine_xcomm ((Fin.castSucc_injective n).ne hik),
        refine_xcomm ((Fin.castSucc_injective n).ne hik),
        one_mul, mul_one, mul_inv_cancel_right,
        refine_conj (refine_xc ((Fin.castSucc_injective n).ne hik.symm)
          ((Fin.castSucc_injective n).ne hjk.symm)),
        refine_conj (refine_xc ((Fin.castSucc_injective n).ne hij.symm)
          ((Fin.castSucc_injective n).ne hik.symm)),
        x_mul, key]
    · by_cases hk : k = r
      · rw [refineRoot_of_plain L r hij a hi hj, refineRoot_of_col L r hjk b hj hk,
          refineRoot_of_col L r hik (a * b) hi hk, comm_mul_right,
          refine_xcomm ((Fin.castSucc_injective n).ne hik),
          refine_xcomm (Fin.castSucc_ne_last i),
          refine_conj_mid (refine_xc ((Fin.castSucc_injective n).ne hik.symm)
            (Fin.castSucc_ne_last j).symm),
          mul_assoc a b L.s0, mul_assoc a b L.s1]
      · rw [refineRoot_of_plain L r hij a hi hj, refineRoot_of_plain L r hjk b hj hk,
          refineRoot_of_plain L r hik (a * b) hi hk]
        exact refine_xcomm _ a b

/-- The refinement on a Steinberg generator. -/
def refineGen (g : SteinbergGenerator (Fin n) R) : SteinbergGroup (Fin (n + 1)) R :=
  refineRoot L r g.row g.column g.row_ne_column g.coefficient

theorem refineGen_kills_relations (w : FreeGroup (SteinbergGenerator (Fin n) R))
    (hw : w ∈ SteinbergGroup.relations (I := Fin n) (R := R)) :
    FreeGroup.lift (refineGen L r) w = 1 := by
  change SteinbergGroup.IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      change refineRoot L r i j hij a * refineRoot L r i j hij b *
        (refineRoot L r i j hij (a + b))⁻¹ = 1
      rw [refineRoot_add, mul_inv_cancel]
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of]
      change ⁅refineRoot L r i j hij a, refineRoot L r k l hkl b⁆ = 1
      exact (refineRoot_commute L r hij hkl hjk hli a b).commutator_eq
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      change ⁅refineRoot L r i j hij a, refineRoot L r j k hjk b⁆ *
        (refineRoot L r i k hik (a * b))⁻¹ = 1
      rw [refineRoot_adjacent, mul_inv_cancel]

/-- The Leavitt refinement homomorphism `St_n(R) → St_{n+1}(R)` splitting the index `r`. -/
def refineHom : SteinbergGroup (Fin n) R →* SteinbergGroup (Fin (n + 1)) R :=
  PresentedGroup.toGroup (f := refineGen L r) (refineGen_kills_relations L r)

theorem refineHom_x (i j : Fin n) (hij : i ≠ j) (a : R) :
    refineHom L r (x i j hij a) = refineRoot L r i j hij a := by
  exact PresentedGroup.toGroup.of _

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refineHom_x
