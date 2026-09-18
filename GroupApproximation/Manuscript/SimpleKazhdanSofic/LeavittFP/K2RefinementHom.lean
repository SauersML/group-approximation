import GroupApproximation.Steinberg.Basic
import GroupApproximation.Leavitt.Leavitt
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.CommutatorCalculus
import GroupApproximation.Meta.AxiomGuard

/-!
# The Leavitt refinement homomorphism `St_n(R) → St_{n+1}(R)`

Let `R` be a ring with a Leavitt family `s₀, s₁, t₀, t₁`, so `tᵢ sⱼ = δᵢⱼ` and
`s₀ t₀ + s₁ t₁ = 1`.  Fix an index `r : Fin n`.  Split `r` into two indices of
`Fin (n + 1)`: `castSucc r` and `last n`.  All other indices `i` go to `castSucc i`.
On generators the refinement map is

* `xᵢⱼ(a) ↦ x_{i j}(a)` if `i ≠ r` and `j ≠ r`;
* `x_{r j}(a) ↦ x_{r j}(t₀ a) · x_{last, j}(t₁ a)`;
* `x_{i r}(a) ↦ x_{i r}(a s₀) · x_{i, last}(a s₁)`.

This is the formula `eq:steinberg-refinement` of the Leavitt manuscript.  All three
Steinberg relations are checked here directly.  The additive and commuting relations
only need commuting roots.  The adjacent relation through the split index uses
`s₀ t₀ + s₁ t₁ = 1`.  So the map descends to `refineHom L r`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

variable {R : Type*} [Ring R] (L : LeavittFamily R) {n : ℕ} (r : Fin n)

/-- The image of the generator `xᵢⱼ(a)` under the refinement splitting `r`. -/
def refineRoot (i j : Fin n) (hij : i ≠ j) (a : R) : SteinbergGroup (Fin (n + 1)) R :=
  if i = r then
    x (Fin.castSucc i) (Fin.castSucc j) ((Fin.castSucc_injective n).ne hij) (L.t0 * a) *
      x (Fin.last n) (Fin.castSucc j) (Fin.castSucc_ne_last j).symm (L.t1 * a)
  else if j = r then
    x (Fin.castSucc i) (Fin.castSucc j) ((Fin.castSucc_injective n).ne hij) (a * L.s0) *
      x (Fin.castSucc i) (Fin.last n) (Fin.castSucc_ne_last i) (a * L.s1)
  else x (Fin.castSucc i) (Fin.castSucc j) ((Fin.castSucc_injective n).ne hij) a

theorem refineRoot_of_row {i j : Fin n} (hij : i ≠ j) (a : R) (hi : i = r) :
    refineRoot L r i j hij a =
      x (Fin.castSucc i) (Fin.castSucc j) ((Fin.castSucc_injective n).ne hij) (L.t0 * a) *
        x (Fin.last n) (Fin.castSucc j) (Fin.castSucc_ne_last j).symm (L.t1 * a) := by
  rw [refineRoot, if_pos hi]

theorem refineRoot_of_col {i j : Fin n} (hij : i ≠ j) (a : R) (hi : ¬ i = r) (hj : j = r) :
    refineRoot L r i j hij a =
      x (Fin.castSucc i) (Fin.castSucc j) ((Fin.castSucc_injective n).ne hij) (a * L.s0) *
        x (Fin.castSucc i) (Fin.last n) (Fin.castSucc_ne_last i) (a * L.s1) := by
  rw [refineRoot, if_neg hi, if_pos hj]

theorem refineRoot_of_plain {i j : Fin n} (hij : i ≠ j) (a : R) (hi : ¬ i = r) (hj : ¬ j = r) :
    refineRoot L r i j hij a =
      x (Fin.castSucc i) (Fin.castSucc j) ((Fin.castSucc_injective n).ne hij) a := by
  rw [refineRoot, if_neg hi, if_neg hj]

/-- Two roots of `St_{n+1}(R)` commute under the usual non-adjacency conditions. -/
theorem refine_xc {p q p' q' : Fin (n + 1)} {h : p ≠ q} {h' : p' ≠ q'} {a b : R}
    (e1 : q ≠ p') (e2 : q' ≠ p) : Commute (x p q h a) (x p' q' h' b) :=
  x_commute_of_ne p q p' q' h h' e1 e2 a b

/-- The adjacent commutator relation in `St_{n+1}(R)`, keeping the implicit data implicit. -/
theorem refine_xcomm {p q s : Fin (n + 1)} {h1 : p ≠ q} {h2 : q ≠ s} (h3 : p ≠ s) (a b : R) :
    ⁅x p q h1 a, x q s h2 b⁆ = x p s h3 (a * b) :=
  x_commutator p q s h1 h2 h3 a b

theorem refine_conj {G : Type*} [Group G] {a b : G} (h : Commute a b) : a * b * a⁻¹ = b := by
  rw [h.eq, mul_inv_cancel_right]

theorem refine_conj_mid {G : Type*} [Group G] {a b c : G} (h : Commute b c) :
    a * b * c * b⁻¹ = a * c := by
  rw [mul_assoc a b c, h.eq, ← mul_assoc, mul_inv_cancel_right]

/-- Discharges the index inequalities `castSucc a ≠ castSucc b`, `castSucc a ≠ last`, and
`last ≠ castSucc a` from hypotheses in context. -/
local macro "fin_ne" : tactic =>
  `(tactic| first
    | exact Fin.castSucc_ne_last _
    | exact (Fin.castSucc_ne_last _).symm
    | exact (Fin.castSucc_injective _).ne ‹_›
    | exact (Fin.castSucc_injective _).ne (Ne.symm ‹_›))

theorem refineRoot_add {i j : Fin n} (hij : i ≠ j) (a b : R) :
    refineRoot L r i j hij a * refineRoot L r i j hij b = refineRoot L r i j hij (a + b) := by
  by_cases hi : i = r
  · rw [refineRoot_of_row L r hij a hi, refineRoot_of_row L r hij b hi,
      refineRoot_of_row L r hij (a + b) hi,
      Commute.mul_mul_mul_comm
        (refine_xc ((Fin.castSucc_injective n).ne hij.symm) (Fin.castSucc_ne_last j)),
      x_mul, x_mul, mul_add, mul_add]
  · by_cases hj : j = r
    · rw [refineRoot_of_col L r hij a hi hj, refineRoot_of_col L r hij b hi hj,
        refineRoot_of_col L r hij (a + b) hi hj,
        Commute.mul_mul_mul_comm
          (refine_xc (Fin.castSucc_ne_last i).symm ((Fin.castSucc_injective n).ne hij.symm)),
        x_mul, x_mul, add_mul, add_mul]
    · rw [refineRoot_of_plain L r hij a hi hj, refineRoot_of_plain L r hij b hi hj,
        refineRoot_of_plain L r hij (a + b) hi hj, x_mul]

theorem refineRoot_commute {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (a b : R) :
    Commute (refineRoot L r i j hij a) (refineRoot L r k l hkl b) := by
  by_cases hi : i = r
  · rw [refineRoot_of_row L r hij a hi]
    by_cases hk : k = r
    · rw [refineRoot_of_row L r hkl b hk]
      exact Commute.mul_left
        (Commute.mul_right (refine_xc (by fin_ne) (by fin_ne))
          (refine_xc (by fin_ne) (by fin_ne)))
        (Commute.mul_right (refine_xc (by fin_ne) (by fin_ne))
          (refine_xc (by fin_ne) (by fin_ne)))
    · by_cases hl : l = r
      · exact absurd (hl.trans hi.symm) hli
      · rw [refineRoot_of_plain L r hkl b hk hl]
        exact Commute.mul_left (refine_xc (by fin_ne) (by fin_ne))
          (refine_xc (by fin_ne) (by fin_ne))
  · by_cases hj : j = r
    · rw [refineRoot_of_col L r hij a hi hj]
      by_cases hk : k = r
      · exact absurd (hj.trans hk.symm) hjk
      · by_cases hl : l = r
        · rw [refineRoot_of_col L r hkl b hk hl]
          exact Commute.mul_left
            (Commute.mul_right (refine_xc (by fin_ne) (by fin_ne))
              (refine_xc (by fin_ne) (by fin_ne)))
            (Commute.mul_right (refine_xc (by fin_ne) (by fin_ne))
              (refine_xc (by fin_ne) (by fin_ne)))
        · rw [refineRoot_of_plain L r hkl b hk hl]
          exact Commute.mul_left (refine_xc (by fin_ne) (by fin_ne))
            (refine_xc (by fin_ne) (by fin_ne))
    · rw [refineRoot_of_plain L r hij a hi hj]
      by_cases hk : k = r
      · rw [refineRoot_of_row L r hkl b hk]
        exact Commute.mul_right (refine_xc (by fin_ne) (by fin_ne))
          (refine_xc (by fin_ne) (by fin_ne))
      · by_cases hl : l = r
        · rw [refineRoot_of_col L r hkl b hk hl]
          exact Commute.mul_right (refine_xc (by fin_ne) (by fin_ne))
            (refine_xc (by fin_ne) (by fin_ne))
        · rw [refineRoot_of_plain L r hkl b hk hl]
          exact refine_xc (by fin_ne) (by fin_ne)

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refineRoot
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refineRoot_of_row
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refineRoot_of_col
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refineRoot_of_plain
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refine_xc
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refine_xcomm
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refine_conj
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refine_conj_mid
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refineRoot_add
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refineRoot_commute
