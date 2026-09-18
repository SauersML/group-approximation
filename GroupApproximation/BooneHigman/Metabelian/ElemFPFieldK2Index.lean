import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2Bimul
import GroupApproximation.Meta.AxiomGuard

/-!
# Steinberg symbols over a field: index independence and antisymmetry

Lane `bh-met-15`.  Over a field `R`, with pairwise distinct indices `i, j, k`:

* `w_kj(1) w_ij(v) w_kj(1)⁻¹ = w_ik(v)` (`weyl_conj_w`), so `w_kj(1)` sends `h_ij(u)` to
  `h_ik(u)` (`weyl_conj_h`),
* `symbol i j hij u v = symbol i k hik u v` (`symbol_index`),
* `symbol i j hij v u = (symbol i j hij u v)⁻¹` (`symbol_antisymm`).

Truth check (paper).  `w_kj(1)` sends `x_ij(a)` to `x_ik(a)` and `x_ji(a)` to `x_ki(a)`
(`w_conj_x_col_j`, `w_conj_x_row_j` with unit `1`).  So it sends `w_ij(v)` to `w_ik(v)`.  The
symbol is central, so conjugating it by `w_kj(1)` changes nothing, but conjugation carries
`h_ij` to `h_ik`.  Antisymmetry is `symbol_index` followed by `symbol_swap_index`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h w_conj_x_col_j
  w_conj_x_row_j)

variable {I R : Type*} [Fintype I] [DecidableEq I] [Field R]

/-- `w_kj(1) w_ij(v) w_kj(1)⁻¹ = w_ik(v)`. -/
theorem weyl_conj_w (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (v : Rˣ) :
    w k j hjk.symm (1 : Rˣ) * w i j hij v * (w k j hjk.symm (1 : Rˣ))⁻¹ = w i k hik v := by
  show w k j hjk.symm (1 : Rˣ) * (x i j hij (v : R) * x j i hij.symm (-((v⁻¹ : Rˣ) : R)) *
      x i j hij (v : R)) * (w k j hjk.symm (1 : Rˣ))⁻¹ =
    x i k hik (v : R) * x k i hik.symm (-((v⁻¹ : Rˣ) : R)) * x i k hik (v : R)
  rw [conj_mul_three, w_conj_x_col_j k j i hjk.symm hik hij (1 : Rˣ),
    w_conj_x_row_j k j i hjk.symm hik.symm hij.symm (1 : Rˣ), inv_one, Units.val_one, mul_one,
    one_mul]

/-- `w_kj(1) h_ij(u) w_kj(1)⁻¹ = h_ik(u)`. -/
theorem weyl_conj_h (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Rˣ) :
    w k j hjk.symm (1 : Rˣ) * h i j hij u * (w k j hjk.symm (1 : Rˣ))⁻¹ = h i k hik u := by
  show w k j hjk.symm (1 : Rˣ) * (w i j hij u * w i j hij (-1)) *
      (w k j hjk.symm (1 : Rˣ))⁻¹ = w i k hik u * w i k hik (-1)
  rw [conj_mul_two, weyl_conj_w i j k hij hik hjk u, weyl_conj_w i j k hij hik hjk (-1)]

/-- **Index independence.**  `symbol i j hij u v = symbol i k hik u v`. -/
theorem symbol_index (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u v : Rˣ) :
    symbol i j hij u v = symbol i k hik u v := by
  have hc : symbol i j hij u v * w k j hjk.symm (1 : Rˣ) =
      w k j hjk.symm (1 : Rˣ) * symbol i j hij u v :=
    (symbol_commute i j k hij hik hjk u v (w k j hjk.symm (1 : Rˣ))).eq
  calc symbol i j hij u v =
        w k j hjk.symm (1 : Rˣ) * symbol i j hij u v * (w k j hjk.symm (1 : Rˣ))⁻¹ := by
          rw [← hc, mul_inv_cancel_right]
    _ = symbol i k hik u v := by
          unfold symbol
          rw [conj_mul_three, conj_inv', conj_inv', weyl_conj_h i j k hij hik hjk (u * v),
            weyl_conj_h i j k hij hik hjk u, weyl_conj_h i j k hij hik hjk v]

/-- **Antisymmetry.**  `symbol i j hij v u = (symbol i j hij u v)⁻¹`. -/
theorem symbol_antisymm (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u v : Rˣ) :
    symbol i j hij v u = (symbol i j hij u v)⁻¹ := by
  rw [symbol_index i j k hij hik hjk v u]
  exact symbol_swap_index i j k hij hik hjk u v

end GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.weyl_conj_w
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.weyl_conj_h
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.symbol_index
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.symbol_antisymm
