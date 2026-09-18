import Mathlib.Tactic.Group
import GroupApproximation.Steinberg.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Weyl and diagonal elements in the Steinberg group `St_I(R)`

Lane `sk-rows-11` (ring-generic Steinberg infrastructure on Khanh's route to the rank-four
`K₂` gap behind tex 733; Khanh sec. 5 uses the Weyl relations
`w₁₂ X_{ij} w₁₂⁻¹ = X_{τ(i) τ(j)}`).  No single tex sentence is formalized here.

For an associative unital ring `R`, a finite index type `I`, indices `i ≠ j` and a unit
`u : Rˣ` we define, inside the presented Steinberg group `SteinbergGroup I R`,

* `w i j hij u = x_ij(u) · x_ji(-u⁻¹) · x_ij(u)`,
* `h i j hij u = w i j hij u · w i j hij (-1)`.

## Mathematical content (truth check)

With `A = x_ij(u)`, `B = x_ji(-u⁻¹)` we have `w = A B A` and
`w g w⁻¹ = A (B (A g A⁻¹) B⁻¹) A⁻¹`.  Only the Steinberg relations are used:

* (C1) `x_pq(b) x_qr(c) x_pq(b)⁻¹ = x_pr(bc) x_qr(c)` for `p, q, r` distinct
  (this is `⁅x_pq(b), x_qr(c)⁆ = x_pr(bc)`);
* (C2) `x_qr(c) x_pq(b) x_qr(c)⁻¹ = x_pq(b) x_pr(-(bc))` (C1-type relation applied to
  `⁅x_pq(-b), x_qr(c)⁆ = x_pr(-bc)`);
* `x_ij(a)` and `x_kl(b)` commute when `j ≠ k` and `l ≠ i`.

The case computations are in `SteinbergWeyl/Conjugation.lean` and the matrix images in
`SteinbergWeyl/Projection.lean`.  In matrix terms `W = u E_ij - u⁻¹ E_ji + Σ_{m ∉ {i,j}} E_mm`
and `h(u) = diag(u at i, u⁻¹ at j, 1 elsewhere)`; this was checked on paper for
noncommutative `R` (the products `u · u⁻¹` and `u⁻¹ · u` appear in the right order).

This module holds the definitions and the elementary conjugation lemmas.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

section GroupLemmas

variable {G : Type*} [Group G]

/-- Conjugation by an element commuting with `p` fixes `p`. -/
theorem conj_of_commute {g p : G} (hc : Commute g p) : g * p * g⁻¹ = p := by
  rw [hc.eq, mul_inv_cancel_right]

/-- Conjugation is multiplicative. -/
theorem conj_mul (g p q : G) : g * (p * q) * g⁻¹ = (g * p * g⁻¹) * (g * q * g⁻¹) := by
  group

end GroupLemmas

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

/-- The Weyl element `w_ij(u) = x_ij(u) x_ji(-u⁻¹) x_ij(u)` of `St_I(R)`. -/
def w (i j : I) (hij : i ≠ j) (u : Rˣ) : SteinbergGroup I R :=
  x i j hij (u : R) * x j i hij.symm (-((u⁻¹ : Rˣ) : R)) * x i j hij (u : R)

/-- The diagonal element `h_ij(u) = w_ij(u) w_ij(-1)` of `St_I(R)`. -/
def h (i j : I) (hij : i ≠ j) (u : Rˣ) : SteinbergGroup I R :=
  w i j hij u * w i j hij (-1)

/-- Transport of a Steinberg generator along equalities of its indices and coefficient. -/
theorem x_congr {i j i' j' : I} (hij : i ≠ j) (hij' : i' ≠ j') {a a' : R}
    (hi : i = i') (hj : j = j') (ha : a = a') :
    x i j hij a = x i' j' hij' a' := by
  subst hi hj ha
  rfl

/-- (C1) Left adjacent conjugation: `x_pq(b) x_qr(c) x_pq(b)⁻¹ = x_pr(bc) x_qr(c)`. -/
theorem conj_x_left (p q r : I) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) (b c : R) :
    x p q hpq b * x q r hqr c * (x p q hpq b)⁻¹ = x p r hpr (b * c) * x q r hqr c := by
  rw [← x_commutator p q r hpq hqr hpr b c, commutatorElement_def]
  group

/-- (C2) Right adjacent conjugation: `x_qr(c) x_pq(b) x_qr(c)⁻¹ = x_pq(b) x_pr(-(bc))`. -/
theorem conj_x_right (p q r : I) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) (b c : R) :
    x q r hqr c * x p q hpq b * (x q r hqr c)⁻¹ = x p q hpq b * x p r hpr (-(b * c)) := by
  calc x q r hqr c * x p q hpq b * (x q r hqr c)⁻¹
      = x p q hpq b * ⁅(x p q hpq b)⁻¹, x q r hqr c⁆ := by
        rw [commutatorElement_def]
        group
    _ = x p q hpq b * x p r hpr (-(b * c)) := by
        rw [← x_neg, x_commutator p q r hpq hqr hpr (-b) c, neg_mul]

/-- Expansion of conjugation by a Weyl element into its three root factors. -/
theorem w_conj_expand (i j : I) (hij : i ≠ j) (u : Rˣ) (g : SteinbergGroup I R) :
    w i j hij u * g * (w i j hij u)⁻¹ =
      x i j hij (u : R) *
          (x j i hij.symm (-((u⁻¹ : Rˣ) : R)) *
              (x i j hij (u : R) * g * (x i j hij (u : R))⁻¹) *
            (x j i hij.symm (-((u⁻¹ : Rˣ) : R)))⁻¹) *
        (x i j hij (u : R))⁻¹ := by
  simp only [w, mul_inv_rev, mul_assoc]

/-- The inverse of a Weyl element: `w_ij(u)⁻¹ = w_ij(-u)`. -/
theorem w_inv (i j : I) (hij : i ≠ j) (u : Rˣ) :
    (w i j hij u)⁻¹ = w i j hij (-u) := by
  simp only [w, mul_inv_rev, Units.val_neg, inv_neg, neg_neg, x_neg, inv_inv, mul_assoc]

end GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl.conj_of_commute
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl.conj_mul
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl.x_congr
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl.conj_x_left
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl.conj_x_right
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl.w_conj_expand
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl.w_inv
