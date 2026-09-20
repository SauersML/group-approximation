import GroupApproximation.BooneHigmanLinear.RelGen.SteinNormal
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergWeyl.Conjugation
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergWeyl.Diagonal
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoAction
import GroupApproximation.BooneHigman.SteinbergBasic.Kernel
import GroupApproximation.Meta.AxiomGuard

/-!
# Torus calculus in `St_I(R)` over a commutative ring

Lane bh-pal-wire, k2-poly H.L1 (ii) (Dennis–Vaserstein for local rings). Here
`h_ij(u) = w_ij(u) w_ij(-1)` and `{u, v}_ij = h_ij(uv) h_ij(u)⁻¹ h_ij(v)⁻¹` (`csym`).

* `act_h_apply`, `csym_mem_K2`: `h_ij(u)` acts on `R^I` as `diag(u at i, u⁻¹ at j)`, so symbols
  lie in `K₂`.
* `h_mul_h`, `h_inv_eq`: `h(u) h(c) = {c, u}⁻¹ h(cu)` and `h(u)⁻¹ = h(u⁻¹) {u⁻¹, u}`.
* `conj_w_of_map`, `conj_h_of_map`: if `g` sends `x_ab(t) ↦ x_cd(l t)` and `x_ba(t) ↦ x_dc(l⁻¹ t)`,
  then `g w_ab(v) g⁻¹ = w_cd(l v)` and `g h_ab(u) g⁻¹ = {l, u}_cd h_cd(u)`.
* `h_conj_x_row_i` … `h_conj_x_col_j`: `h_ij(u)` scales `x_in`, `x_jn`, `x_ni`, `x_nj` by
  `u`, `u⁻¹`, `u⁻¹`, `u`.
* **`h_mul_h_third`**: `h_ij(u) h_jn(u) = {-1, u}_in h_in(u)`. Conjugate `h_ij(u)` by `w_jn(1)`
  in two ways.
* **`h_swap`**: `h_ji(u) = {-1, u⁻¹}_ij h_ij(u⁻¹)`, from `w_ji(v) = w_ij(-v⁻¹)`.
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h w_inv w_conj_x_row_i
  w_conj_x_row_j w_conj_x_col_i w_conj_x_col_j w_conj_x_disjoint
  manuscriptSentence_projectionDiagonalElement)
open GroupApproximation.BooneHigmanLinear.K2Poly (csym cr_h_conj_split)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act)
open GroupApproximation.BooneHigman.SteinbergBasic (K2 mem_K2_iff)

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

theorem act_h_apply (i j : I) (hij : i ≠ j) (u : Rˣ) (v : I → R) (k : I) :
    act (h i j hij u) v k =
      (if k = i then (u : R) else if k = j then ((u⁻¹ : Rˣ) : R) else 1) * v k := by
  rw [act, manuscriptSentence_projectionDiagonalElement, Matrix.mulVec_diagonal]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.act_h_apply

theorem act_smul' (g : SteinbergGroup I R) (c : R) (v : I → R) : act g (c • v) = c • act g v :=
  Matrix.mulVec_smul _ c v

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.act_smul'

theorem projection_h_mul' (i j : I) (hij : i ≠ j) (u v : Rˣ) :
    projection (h i j hij (u * v)) = projection (h i j hij u) * projection (h i j hij v) := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, manuscriptSentence_projectionDiagonalElement,
    manuscriptSentence_projectionDiagonalElement, manuscriptSentence_projectionDiagonalElement,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases hi : k = i
  · rw [if_pos hi, if_pos hi, if_pos hi, Units.val_mul]
  · by_cases hj : k = j
    · rw [if_neg hi, if_neg hi, if_neg hi, if_pos hj, if_pos hj, if_pos hj, mul_inv,
        Units.val_mul]
    · rw [if_neg hi, if_neg hi, if_neg hi, if_neg hj, if_neg hj, if_neg hj, mul_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.projection_h_mul'

/-- Symbols lie in `K₂`, over any commutative ring. -/
theorem csym_mem_K2 (i j : I) (hij : i ≠ j) (u v : Rˣ) : csym i j hij u v ∈ K2 I R := by
  have hc : projection (h i j hij u) * projection (h i j hij v) =
      projection (h i j hij v) * projection (h i j hij u) := by
    rw [← projection_h_mul', ← projection_h_mul', mul_comm u v]
  rw [mem_K2_iff, csym, map_mul, map_mul, map_inv, map_inv, projection_h_mul', hc]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.csym_mem_K2

theorem h_mul_h (i j : I) (hij : i ≠ j) (u c : Rˣ) :
    h i j hij u * h i j hij c = (csym i j hij c u)⁻¹ * h i j hij (c * u) := by
  rw [csym]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.h_mul_h

theorem h_inv_eq (i j : I) (hij : i ≠ j) (u : Rˣ) :
    (h i j hij u)⁻¹ = h i j hij u⁻¹ * csym i j hij u⁻¹ u := by
  rw [csym, inv_mul_cancel u, h_one]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.h_inv_eq

/-- If `g` sends `x_ab(t) ↦ x_cd(l t)` and `x_ba(t) ↦ x_dc(l⁻¹ t)`, then
`g w_ab(v) g⁻¹ = w_cd(l v)`. -/
theorem conj_w_of_map {g : SteinbergGroup I R} {a b c d : I} (hab : a ≠ b) (hcd : c ≠ d)
    (l : Rˣ) (h1 : ∀ t : R, g * x a b hab t * g⁻¹ = x c d hcd ((l : R) * t))
    (h2 : ∀ t : R, g * x b a hab.symm t * g⁻¹ = x d c hcd.symm (((l⁻¹ : Rˣ) : R) * t))
    (v : Rˣ) : g * w a b hab v * g⁻¹ = w c d hcd (l * v) := by
  have e : g * w a b hab v * g⁻¹ = (g * x a b hab (v : R) * g⁻¹) *
      (g * x b a hab.symm (-((v⁻¹ : Rˣ) : R)) * g⁻¹) * (g * x a b hab (v : R) * g⁻¹) := by
    rw [w]
    group
  have hc : ((l⁻¹ : Rˣ) : R) * -((v⁻¹ : Rˣ) : R) = -((((l * v)⁻¹ : Rˣ)) : R) := by
    rw [mul_inv, Units.val_mul]
    ring
  rw [e, h1, h2, hc, ← Units.val_mul, w]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_w_of_map

/-- Under the hypotheses of `conj_w_of_map`, `g h_ab(u) g⁻¹ = {l, u}_cd h_cd(u)`. -/
theorem conj_h_of_map {g : SteinbergGroup I R} {a b c d : I} (hab : a ≠ b) (hcd : c ≠ d)
    (l : Rˣ) (h1 : ∀ t : R, g * x a b hab t * g⁻¹ = x c d hcd ((l : R) * t))
    (h2 : ∀ t : R, g * x b a hab.symm t * g⁻¹ = x d c hcd.symm (((l⁻¹ : Rˣ) : R) * t))
    (u : Rˣ) : g * h a b hab u * g⁻¹ = csym c d hcd l u * h c d hcd u := by
  have e : g * h a b hab u * g⁻¹ = (g * w a b hab u * g⁻¹) * (g * w a b hab (-1) * g⁻¹) := by
    rw [h]
    group
  rw [e, conj_w_of_map hab hcd l h1 h2, conj_w_of_map hab hcd l h1 h2, mul_neg_one, ← w_inv]
  simp only [csym, h]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_h_of_map

section Scale

variable {i j n : I} (hij : i ≠ j) (u : Rˣ)

/-- `h_ij(u) x_in(a) h_ij(u)⁻¹ = x_in(u a)`. -/
theorem h_conj_x_row_i (hin : i ≠ n) (hjn : j ≠ n) (a : R) :
    h i j hij u * x i n hin a * (h i j hij u)⁻¹ = x i n hin ((u : R) * a) := by
  rw [cr_h_conj_split, w_conj_x_row_i i j n hij hin hjn, w_conj_x_row_j i j n hij hin hjn]
  congr 1
  rw [inv_neg_one, Units.val_neg, Units.val_one]
  ring

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.h_conj_x_row_i

/-- `h_ij(u) x_jn(a) h_ij(u)⁻¹ = x_jn(u⁻¹ a)`. -/
theorem h_conj_x_row_j (hin : i ≠ n) (hjn : j ≠ n) (a : R) :
    h i j hij u * x j n hjn a * (h i j hij u)⁻¹ = x j n hjn (((u⁻¹ : Rˣ) : R) * a) := by
  rw [cr_h_conj_split, w_conj_x_row_j i j n hij hin hjn, w_conj_x_row_i i j n hij hin hjn]
  congr 1
  rw [Units.val_neg, Units.val_one]
  ring

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.h_conj_x_row_j

/-- `h_ij(u) x_ni(a) h_ij(u)⁻¹ = x_ni(u⁻¹ a)`. -/
theorem h_conj_x_col_i (hni : n ≠ i) (hnj : n ≠ j) (a : R) :
    h i j hij u * x n i hni a * (h i j hij u)⁻¹ = x n i hni (((u⁻¹ : Rˣ) : R) * a) := by
  rw [cr_h_conj_split, w_conj_x_col_i i j n hij hni hnj, w_conj_x_col_j i j n hij hni hnj]
  congr 1
  rw [Units.val_neg, Units.val_one]
  ring

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.h_conj_x_col_i

/-- `h_ij(u) x_nj(a) h_ij(u)⁻¹ = x_nj(u a)`. -/
theorem h_conj_x_col_j (hni : n ≠ i) (hnj : n ≠ j) (a : R) :
    h i j hij u * x n j hnj a * (h i j hij u)⁻¹ = x n j hnj ((u : R) * a) := by
  rw [cr_h_conj_split, w_conj_x_col_j i j n hij hni hnj, w_conj_x_col_i i j n hij hni hnj]
  congr 1
  rw [inv_neg_one, Units.val_neg, Units.val_one]
  ring

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.h_conj_x_col_j

/-- `h_ij(u)` commutes with `x_kl` for `k, l ∉ {i, j}`. -/
theorem h_conj_x_disjoint {k l : I} (hkl : k ≠ l) (hik : i ≠ k) (hjk : j ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (a : R) :
    h i j hij u * x k l hkl a * (h i j hij u)⁻¹ = x k l hkl a := by
  rw [cr_h_conj_split, w_conj_x_disjoint i j k l hij hkl hik hjk hil hjl,
    w_conj_x_disjoint i j k l hij hkl hik hjk hil hjl]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.h_conj_x_disjoint

end Scale

/-- `g p g⁻¹ = q` gives `g⁻¹ q g⁻¹⁻¹ = p`. -/
theorem inv_conj_of_conj {G : Type*} [Group G] {g p q : G} (hpq : g * p * g⁻¹ = q) :
    g⁻¹ * q * g⁻¹⁻¹ = p := by
  rw [← hpq]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.inv_conj_of_conj

/-- **`h_ij(u) h_jn(u) = {-1, u}_in h_in(u)`** for distinct `i, j, n`. -/
theorem h_mul_h_third {i j n : I} (hij : i ≠ j) (hjn : j ≠ n) (hin : i ≠ n) (u : Rˣ) :
    h i j hij u * h j n hjn u = csym i n hin (-1) u * h i n hin u := by
  -- First way: `h_ij(u)⁻¹ w_jn(1) h_ij(u) = w_jn(u)`.
  have g1 : ∀ t : R, (h i j hij u)⁻¹ * x j n hjn t * (h i j hij u)⁻¹⁻¹ =
      x j n hjn ((u : R) * t) := fun t => inv_conj_of_conj (by
    rw [h_conj_x_row_j hij u hin hjn, ← mul_assoc, Units.inv_mul, one_mul])
  have g2 : ∀ t : R, (h i j hij u)⁻¹ * x n j hjn.symm t * (h i j hij u)⁻¹⁻¹ =
      x n j hjn.symm (((u⁻¹ : Rˣ) : R) * t) := fun t => inv_conj_of_conj (by
    rw [h_conj_x_col_j hij u hin.symm hjn.symm, ← mul_assoc, Units.mul_inv, one_mul])
  have A : w j n hjn 1 * h i j hij u * (w j n hjn 1)⁻¹ = h i j hij u * h j n hjn u := by
    have e := conj_w_of_map hjn hjn u g1 g2 1
    rw [inv_inv, mul_one] at e
    calc w j n hjn 1 * h i j hij u * (w j n hjn 1)⁻¹
        = h i j hij u * ((h i j hij u)⁻¹ * w j n hjn 1 * h i j hij u) * (w j n hjn 1)⁻¹ := by
          group
      _ = h i j hij u * h j n hjn u := by
          rw [e, w_inv]
          simp only [h]
          group
  -- Second way: conjugation by `w_jn(1)` sends the root `(i, j)` to `(i, n)` with `l = -1`.
  have k1 : ∀ t : R, w j n hjn 1 * x i j hij t * (w j n hjn 1)⁻¹ =
      x i n hin ((((-1 : Rˣ)) : R) * t) := fun t => by
    rw [w_conj_x_col_i j n i hjn hij hin, Units.val_neg, Units.val_one]
    congr 1
    ring
  have k2 : ∀ t : R, w j n hjn 1 * x j i hij.symm t * (w j n hjn 1)⁻¹ =
      x n i hin.symm ((((-1 : Rˣ)⁻¹ : Rˣ) : R) * t) := fun t => by
    rw [w_conj_x_row_i j n i hjn hij.symm hin.symm, inv_neg_one, inv_one, Units.val_neg,
      Units.val_one]
  rw [← A, conj_h_of_map hij hin (-1) k1 k2 u]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.h_mul_h_third

/-- `w_ji(v) = w_ij(-v⁻¹)`. -/
theorem w_swap {i j : I} (hij : i ≠ j) (k : I) (hik : i ≠ k) (hjk : j ≠ k) (v : Rˣ) :
    w j i hij.symm v = w i j hij (-v⁻¹) := by
  rw [cr_w_eq_alt j i k hij.symm hjk hik v, w]
  simp only [Units.val_neg, inv_neg, inv_inv, neg_neg]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.w_swap

/-- **`h_ji(u) = {-1, u⁻¹}_ij h_ij(u⁻¹)`**. -/
theorem h_swap {i j : I} (hij : i ≠ j) (k : I) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ) :
    h j i hij.symm u = csym i j hij (-1) u⁻¹ * h i j hij u⁻¹ := by
  rw [h, w_swap hij k hik hjk u, w_swap hij k hik hjk (-1), csym, neg_one_mul]
  simp only [h]
  rw [inv_neg_one, neg_neg, show w i j hij 1 = (w i j hij (-1))⁻¹ by rw [w_inv, neg_neg]]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.h_swap

end GroupApproximation.BooneHigmanLinear.RelGen
