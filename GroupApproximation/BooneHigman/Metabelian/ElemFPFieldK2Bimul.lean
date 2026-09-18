import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2Commute
import Mathlib.GroupTheory.Commutator.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Steinberg symbols over a field are bimultiplicative

Lane `bh-met-15`.  Over a field `R`, with indices `i ≠ j` and a third index `k ∉ {i, j}`:

* `h_ik(u) w_ij(v) h_ik(u)⁻¹ = w_ij(uv)` (`h_conj_w`),
* `⁅h_ik(u), h_ij(v)⁆ = symbol i j hij u v` (`commutator_h_h`),
* `symbol(u, v₁v₂) = symbol(u, v₁) symbol(u, v₂)` (`symbol_mul_right`),
* `symbol(u₁u₂, v) = symbol(u₁, v) symbol(u₂, v)` (`symbol_mul_left`),
* `symbol_ik(v, u) = (symbol_ij(u, v))⁻¹` (`symbol_swap_index`).

Truth check (paper).  `h_ik(u)` scales `x_ij` by `u` and `x_ji` by `u⁻¹`, so it sends
`w_ij(v) = x_ij(v) x_ji(-v⁻¹) x_ij(v)` to `w_ij(uv)`.  Hence
`h_ik(u) h_ij(v) h_ik(u)⁻¹ = w_ij(uv) w_ij(-u) = w_ij(uv) w_ij(u)⁻¹`, and so
`⁅h_ik(u), h_ij(v)⁆ = w_ij(uv) w_ij(u)⁻¹ h_ij(v)⁻¹ = h_ij(uv) h_ij(u)⁻¹ h_ij(v)⁻¹`.
Bimultiplicativity then follows from the commutator identities and centrality.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

open scoped commutatorElement
open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h w_inv)

section GroupLemmas

variable {G : Type*} [Group G]

/-- Conjugation distributes over a product of two elements. -/
theorem conj_mul_two (g a b : G) : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by
  group

/-- Conjugation commutes with inversion. -/
theorem conj_inv' (g a : G) : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by
  group

/-- Commutator with a product on the right. -/
theorem commutator_mul_right' (a x y : G) : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
  simp only [commutatorElement_def]
  group

/-- Commutator with a product on the left. -/
theorem commutator_mul_left' (x y b : G) : ⁅x * y, b⁆ = x * ⁅y, b⁆ * x⁻¹ * ⁅x, b⁆ := by
  simp only [commutatorElement_def]
  group

/-- A central left factor on the right of a commutator can be dropped. -/
theorem commutator_central_mul_right {a s y : G} (hs : ∀ g, Commute s g) :
    ⁅a, s * y⁆ = ⁅a, y⁆ := by
  rw [commutator_mul_right', commutatorElement_eq_one_iff_mul_comm.mpr (hs a).eq.symm, one_mul,
    (hs ⁅a, y⁆).eq, mul_inv_cancel_right]

/-- A central left factor on the left of a commutator can be dropped. -/
theorem commutator_central_mul_left {s x b : G} (hs : ∀ g, Commute s g) :
    ⁅s * x, b⁆ = ⁅x, b⁆ := by
  rw [commutator_mul_left', commutatorElement_eq_one_iff_mul_comm.mpr (hs b).eq, mul_one,
    (hs ⁅x, b⁆).eq, mul_inv_cancel_right]

end GroupLemmas

variable {I R : Type*} [Fintype I] [DecidableEq I] [Field R]

/-- `h_ik(u) w_ij(v) h_ik(u)⁻¹ = w_ij(uv)`. -/
theorem h_conj_w (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u v : Rˣ) :
    h i k hik u * w i j hij v * (h i k hik u)⁻¹ = w i j hij (u * v) := by
  show h i k hik u * (x i j hij (v : R) * x j i hij.symm (-((v⁻¹ : Rˣ) : R)) *
      x i j hij (v : R)) * (h i k hik u)⁻¹ =
    x i j hij ((u * v : Rˣ) : R) * x j i hij.symm (-(((u * v)⁻¹ : Rˣ) : R)) *
      x i j hij ((u * v : Rˣ) : R)
  rw [conj_mul_three, h_conj_iq i k j hik hij hjk.symm u, h_conj_pi i k j hik hij.symm hjk u]
  have e1 : (u : R) * (v : R) = ((u * v : Rˣ) : R) := (Units.val_mul u v).symm
  have e2 : (u : R)⁻¹ * -((v⁻¹ : Rˣ) : R) = -(((u * v)⁻¹ : Rˣ) : R) := by
    rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, Units.val_mul, mul_inv]
    ring
  rw [e1, e2]

/-- The commutator form of the symbol: `⁅h_ik(u), h_ij(v)⁆ = symbol i j hij u v`. -/
theorem commutator_h_h (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u v : Rˣ) :
    ⁅h i k hik u, h i j hij v⁆ = symbol i j hij u v := by
  have e : u * -1 = -u := mul_neg_one u
  have e1 : h i k hik u * h i j hij v * (h i k hik u)⁻¹ =
      w i j hij (u * v) * (w i j hij u)⁻¹ := by
    show h i k hik u * (w i j hij v * w i j hij (-1)) * (h i k hik u)⁻¹ =
      w i j hij (u * v) * (w i j hij u)⁻¹
    rw [conj_mul_two, h_conj_w i j k hij hik hjk u v, h_conj_w i j k hij hik hjk u (-1), w_inv, e]
  rw [commutatorElement_def, e1]
  simp only [symbol, h, mul_inv_rev, mul_assoc, mul_inv_cancel_left]

/-- Multiplicativity in the second variable. -/
theorem symbol_mul_right (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u v₁ v₂ : Rˣ) :
    symbol i j hij u (v₁ * v₂) = symbol i j hij u v₁ * symbol i j hij u v₂ := by
  have hv : h i j hij (v₁ * v₂) = symbol i j hij v₁ v₂ * (h i j hij v₂ * h i j hij v₁) := by
    simp only [symbol, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  rw [← commutator_h_h i j k hij hik hjk u (v₁ * v₂), hv,
    commutator_central_mul_right (symbol_commute i j k hij hik hjk v₁ v₂),
    commutator_mul_right' (h i k hik u) (h i j hij v₂) (h i j hij v₁),
    commutator_h_h i j k hij hik hjk u v₂, commutator_h_h i j k hij hik hjk u v₁,
    ← (symbol_commute i j k hij hik hjk u v₁ (h i j hij v₂)).eq, mul_inv_cancel_right]
  exact (symbol_commute i j k hij hik hjk u v₂ (symbol i j hij u v₁)).eq

/-- Multiplicativity in the first variable. -/
theorem symbol_mul_left (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u₁ u₂ v : Rˣ) :
    symbol i j hij (u₁ * u₂) v = symbol i j hij u₁ v * symbol i j hij u₂ v := by
  have hu : h i k hik (u₁ * u₂) = symbol i k hik u₁ u₂ * (h i k hik u₂ * h i k hik u₁) := by
    simp only [symbol, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  rw [← commutator_h_h i j k hij hik hjk (u₁ * u₂) v, hu,
    commutator_central_mul_left (symbol_commute i k j hik hij hjk.symm u₁ u₂),
    commutator_mul_left' (h i k hik u₂) (h i k hik u₁) (h i j hij v),
    commutator_h_h i j k hij hik hjk u₁ v, commutator_h_h i j k hij hik hjk u₂ v,
    ← (symbol_commute i j k hij hik hjk u₁ v (h i k hik u₂)).eq, mul_inv_cancel_right]

/-- Swapping the arguments and the second index inverts the symbol. -/
theorem symbol_swap_index (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u v : Rˣ) :
    symbol i k hik v u = (symbol i j hij u v)⁻¹ := by
  rw [← commutator_h_h i k j hik hij hjk.symm v u, ← commutator_h_h i j k hij hik hjk u v,
    commutatorElement_inv]

end GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.conj_mul_two
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.conj_inv'
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.commutator_mul_right'
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.commutator_mul_left'
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.commutator_central_mul_right
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.commutator_central_mul_left
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.h_conj_w
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.commutator_h_h
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.symbol_mul_right
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.symbol_mul_left
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.symbol_swap_index
