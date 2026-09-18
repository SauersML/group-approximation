import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergWeyl.Defs

/-!
# Matrix images of the Weyl and diagonal Steinberg elements

Lane `sk-rows-11`.  Under the canonical projection `St_I(R) → EL_I(R)`
(`SteinbergGroup.projection`, `Steinberg/Basic.lean`), with `E_pq(c) = Matrix.single p q c`:

* `w_ij(u) ↦ 1 + E_ij(u) + E_ji(-u⁻¹) - E_ii(1) - E_jj(1)`
  (`(1 + E)(1 + F)(1 + E) = 1 + 2E + F + EF + E² + FE + EFE` with `E² = 0`, `EF = -E_ii(1)`,
  `FE = -E_jj(1)`, `EFE = -E`);
* `h_ij(u) ↦ diag(u at i, u⁻¹ at j, 1 elsewhere)`, from the sixteen products of the
  root matrices supported on `{i, j} × {i, j}`, using `(-1 : Rˣ)⁻¹ = -1`.

Only `u · u⁻¹ = 1`, `u⁻¹ · u = 1` are used, in the order in which they occur, so the
statements hold over every associative unital ring.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl

open GroupApproximation.SteinbergGroup

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

/-- The matrix of the projection of a Steinberg generator. -/
theorem projection_x_val (p q : I) (hpq : p ≠ q) (c : R) :
    ((projection (x p q hpq c) : (Matrix I I R)ˣ) : Matrix I I R) =
      1 + Matrix.single p q c := by
  have e : (projection (x p q hpq c) : (Matrix I I R)ˣ) = elementaryUnit p q hpq c := by
    rw [projection_x, elementaryRoot_val]
  exact (congrArg Units.val e).trans rfl

/-- The matrix of the projection of the Weyl element `w_ij(u)`. -/
theorem w_projection_val (i j : I) (hij : i ≠ j) (u : Rˣ) :
    ((projection (w i j hij u) : (Matrix I I R)ˣ) : Matrix I I R) =
      1 + Matrix.single i j (u : R) + Matrix.single j i (-((u⁻¹ : Rˣ) : R)) -
        Matrix.single i i 1 - Matrix.single j j 1 := by
  have e1 : ∀ A B : Matrix I I R,
      (1 + A) * (1 + B) * (1 + A) = 1 + A + A + B + A * B + A * A + B * A + A * B * A := by
    intro A B
    noncomm_ring
  have hEF : Matrix.single i j (u : R) * Matrix.single j i (-((u⁻¹ : Rˣ) : R)) =
      -Matrix.single i i (1 : R) := by
    rw [Matrix.single_mul_single_same, mul_neg, Units.mul_inv, Matrix.single_neg]
  have hEE : Matrix.single i j (u : R) * Matrix.single i j (u : R) = 0 :=
    Matrix.single_mul_single_of_ne (c := (u : R)) i j i hij.symm (u : R)
  have hFE : Matrix.single j i (-((u⁻¹ : Rˣ) : R)) * Matrix.single i j (u : R) =
      -Matrix.single j j (1 : R) := by
    rw [Matrix.single_mul_single_same, neg_mul, Units.inv_mul, Matrix.single_neg]
  have hPE : -Matrix.single i i (1 : R) * Matrix.single i j (u : R) =
      -Matrix.single i j (u : R) := by
    rw [neg_mul, Matrix.single_mul_single_same, one_mul]
  simp only [w, map_mul, Subgroup.coe_mul, Units.val_mul, projection_x_val]
  rw [e1, hEF, hEE, hFE, hPE]
  abel

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl.projection_x_val
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl.w_projection_val

end GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl
