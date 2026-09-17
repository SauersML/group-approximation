import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergWeyl.Defs

/-!
# Weyl conjugation of Steinberg generators, case by case

Lane `sk-rows-11`.  For `i ≠ j`, a unit `u`, and a root `(k, l)` with `k ≠ l` and
`{k, l} ≠ {i, j}`, conjugation by `w = w_ij(u)` in `St_I(R)` sends `x_kl(a)` to a root element
of the root `(τ k, τ l)`, `τ = swap i j`:

| case | `w x_kl(a) w⁻¹` |
|---|---|
| `k = i`, `l ∉ {i,j}` | `x_jl(-u⁻¹ a)` |
| `k = j`, `l ∉ {i,j}` | `x_il(u a)` |
| `l = i`, `k ∉ {i,j}` | `x_kj(-(a u))` |
| `l = j`, `k ∉ {i,j}` | `x_ki(a u⁻¹)` |
| `k, l ∉ {i,j}` | `x_kl(a)` |

Each proof expands `w g w⁻¹ = A (B (A g A⁻¹) B⁻¹) A⁻¹` (`w_conj_expand`, `A = x_ij(u)`,
`B = x_ji(-u⁻¹)`) and rewrites the three conjugations with (C1), (C2) and root commutation.
Paper check of the case `k = j`:
`A x_jl(a) A⁻¹ = x_il(ua) x_jl(a)`; `B (x_il(ua) x_jl(a)) B⁻¹ = x_jl(-u⁻¹ua) x_il(ua) x_jl(a)
= x_il(ua)`; `A x_il(ua) A⁻¹ = x_il(ua)`.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl

open GroupApproximation.SteinbergGroup

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

/-- Case `k = i`, `l ∉ {i, j}`: `w_ij(u) x_il(a) w_ij(u)⁻¹ = x_jl(-u⁻¹ a)`. -/
theorem w_conj_x_row_i (i j l : I) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (u : Rˣ) (a : R) :
    w i j hij u * x i l hil a * (w i j hij u)⁻¹ =
      x j l hjl (-((u⁻¹ : Rˣ) : R) * a) := by
  have h1 : x i j hij (u : R) * x i l hil a * (x i j hij (u : R))⁻¹ = x i l hil a :=
    conj_of_commute (x_commute_of_ne i j i l hij hil hij.symm hil.symm _ _)
  have h2 : x j i hij.symm (-((u⁻¹ : Rˣ) : R)) * x i l hil a *
      (x j i hij.symm (-((u⁻¹ : Rˣ) : R)))⁻¹ =
        x j l hjl (-((u⁻¹ : Rˣ) : R) * a) * x i l hil a :=
    conj_x_left j i l hij.symm hil hjl _ _
  have h3 : x i j hij (u : R) * (x j l hjl (-((u⁻¹ : Rˣ) : R) * a) * x i l hil a) *
      (x i j hij (u : R))⁻¹ = x j l hjl (-((u⁻¹ : Rˣ) : R) * a) := by
    rw [conj_mul, conj_x_left i j l hij hjl hil, conj_of_commute
      (x_commute_of_ne i j i l hij hil hij.symm hil.symm _ _), neg_mul, mul_neg,
      Units.mul_inv_cancel_left,
      (x_commute_of_ne i l j l hil hjl hjl.symm hil.symm _ _).eq, mul_assoc, x_mul,
      neg_add_cancel, x_zero, mul_one]
  rw [w_conj_expand, h1, h2, h3]

/-- Case `k = j`, `l ∉ {i, j}`: `w_ij(u) x_jl(a) w_ij(u)⁻¹ = x_il(u a)`. -/
theorem w_conj_x_row_j (i j l : I) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (u : Rˣ) (a : R) :
    w i j hij u * x j l hjl a * (w i j hij u)⁻¹ = x i l hil ((u : R) * a) := by
  have h1 : x i j hij (u : R) * x j l hjl a * (x i j hij (u : R))⁻¹ =
      x i l hil ((u : R) * a) * x j l hjl a :=
    conj_x_left i j l hij hjl hil _ _
  have h2 : x j i hij.symm (-((u⁻¹ : Rˣ) : R)) * (x i l hil ((u : R) * a) * x j l hjl a) *
      (x j i hij.symm (-((u⁻¹ : Rˣ) : R)))⁻¹ = x i l hil ((u : R) * a) := by
    rw [conj_mul, conj_x_left j i l hij.symm hil hjl, conj_of_commute
      (x_commute_of_ne j i j l hij.symm hjl hij hjl.symm _ _), neg_mul,
      Units.inv_mul_cancel_left,
      (x_commute_of_ne j l i l hjl hil hil.symm hjl.symm _ _).eq, mul_assoc, x_mul,
      neg_add_cancel, x_zero, mul_one]
  have h3 : x i j hij (u : R) * x i l hil ((u : R) * a) * (x i j hij (u : R))⁻¹ =
      x i l hil ((u : R) * a) :=
    conj_of_commute (x_commute_of_ne i j i l hij hil hij.symm hil.symm _ _)
  rw [w_conj_expand, h1, h2, h3]

/-- Case `l = i`, `k ∉ {i, j}`: `w_ij(u) x_ki(a) w_ij(u)⁻¹ = x_kj(-(a u))`. -/
theorem w_conj_x_col_i (i j k : I) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (u : Rˣ) (a : R) :
    w i j hij u * x k i hki a * (w i j hij u)⁻¹ = x k j hkj (-(a * (u : R))) := by
  have h1 : x i j hij (u : R) * x k i hki a * (x i j hij (u : R))⁻¹ =
      x k i hki a * x k j hkj (-(a * (u : R))) :=
    conj_x_right k i j hki hij hkj _ _
  have h2 : x j i hij.symm (-((u⁻¹ : Rˣ) : R)) *
      (x k i hki a * x k j hkj (-(a * (u : R)))) *
      (x j i hij.symm (-((u⁻¹ : Rˣ) : R)))⁻¹ = x k j hkj (-(a * (u : R))) := by
    rw [conj_mul, conj_of_commute
      (x_commute_of_ne j i k i hij.symm hki hki.symm hij _ _),
      conj_x_right k j i hkj hij.symm hki, neg_mul_neg, Units.mul_inv_cancel_right,
      (x_commute_of_ne k j k i hkj hki hkj.symm hki.symm _ _).eq, ← mul_assoc, x_mul,
      add_neg_cancel, x_zero, one_mul]
  have h3 : x i j hij (u : R) * x k j hkj (-(a * (u : R))) * (x i j hij (u : R))⁻¹ =
      x k j hkj (-(a * (u : R))) :=
    conj_of_commute (x_commute_of_ne i j k j hij hkj hkj.symm hij.symm _ _)
  rw [w_conj_expand, h1, h2, h3]

/-- Case `l = j`, `k ∉ {i, j}`: `w_ij(u) x_kj(a) w_ij(u)⁻¹ = x_ki(a u⁻¹)`. -/
theorem w_conj_x_col_j (i j k : I) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (u : Rˣ) (a : R) :
    w i j hij u * x k j hkj a * (w i j hij u)⁻¹ = x k i hki (a * ((u⁻¹ : Rˣ) : R)) := by
  have h1 : x i j hij (u : R) * x k j hkj a * (x i j hij (u : R))⁻¹ = x k j hkj a :=
    conj_of_commute (x_commute_of_ne i j k j hij hkj hkj.symm hij.symm _ _)
  have h2 : x j i hij.symm (-((u⁻¹ : Rˣ) : R)) * x k j hkj a *
      (x j i hij.symm (-((u⁻¹ : Rˣ) : R)))⁻¹ =
        x k j hkj a * x k i hki (-(a * -((u⁻¹ : Rˣ) : R))) :=
    conj_x_right k j i hkj hij.symm hki _ _
  have h3 : x i j hij (u : R) * (x k j hkj a * x k i hki (-(a * -((u⁻¹ : Rˣ) : R)))) *
      (x i j hij (u : R))⁻¹ = x k i hki (a * ((u⁻¹ : Rˣ) : R)) := by
    rw [conj_mul, conj_of_commute
      (x_commute_of_ne i j k j hij hkj hkj.symm hij.symm _ _),
      conj_x_right k i j hki hij hkj, mul_neg, neg_neg, Units.inv_mul_cancel_right,
      (x_commute_of_ne k i k j hki hkj hki.symm hkj.symm _ _).eq, ← mul_assoc, x_mul,
      add_neg_cancel, x_zero, one_mul]
  rw [w_conj_expand, h1, h2, h3]

/-- Case `k, l ∉ {i, j}`: `w_ij(u)` commutes with `x_kl(a)`. -/
theorem w_conj_x_disjoint (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hjk : j ≠ k) (hil : i ≠ l) (hjl : j ≠ l) (u : Rˣ) (a : R) :
    w i j hij u * x k l hkl a * (w i j hij u)⁻¹ = x k l hkl a := by
  have hA : Commute (x i j hij (u : R)) (x k l hkl a) :=
    x_commute_of_ne i j k l hij hkl hjk hil.symm _ _
  have hB : Commute (x j i hij.symm (-((u⁻¹ : Rˣ) : R))) (x k l hkl a) :=
    x_commute_of_ne j i k l hij.symm hkl hik hjl.symm _ _
  exact conj_of_commute ((hA.mul_left hB).mul_left hA)

end GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl.w_conj_x_row_i
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl.w_conj_x_row_j
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl.w_conj_x_col_i
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl.w_conj_x_col_j
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl.w_conj_x_disjoint
