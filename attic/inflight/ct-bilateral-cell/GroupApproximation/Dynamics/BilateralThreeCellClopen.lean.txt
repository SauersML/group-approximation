import GroupApproximation.Algebra.BilateralThreeCellMatrices
import GroupApproximation.Dynamics.ClopenDefectPair
import GroupApproximation.Dynamics.ClopenCrossedProductComap

/-!
# The bilateral cell of a compressed clopen set in `R_X`

`non_mf_groups_exist.tex`, proof of Proposition `prop:bilateral-three`
(`\label{prop:bilateral-three}`, tex 1550–1555 at origin/main 68481e4d7):

> Take a clopen $P$ with $T(P)\subseteq P$ and nonempty $D=P\setminus T(P)$.  Put $p=1_P$,
> $d=1_D$, and $f_{ab}=u^a d u^{-b}$ for $a,b\in\mathbb Z$.

The abstract cell of `GroupApproximation.Algebra.BilateralThreeCellLevels` is realized in
`R_X = ClopenCrossedProduct T k` by the implementing unit and `p = 1_P`:

* `ClopenCrossedProduct.bilateralCell`: the `Cell` of a compressed clopen `P`;
* `bilateralCell_d`: its defect is `d = 1_{P∖T(P)}` (`defectD`);
* `defectD_ne_zero`: `d ≠ 0` when `D = P∖T(P)` is nonempty, through the injectivity of the
  coefficient embedding (`ClopenCrossedProduct.coeff_injective`,
  `Dynamics/ClopenCrossedProductComap.lean`).

So every identity of `BilateralThreeCellMatrices` (the display tex 1579–1581, `z` central in `B`,
tex 1591–1592) holds verbatim in `GL₃(R_X)` for this cell.
-/

namespace GroupApproximation
namespace ClopenCrossedProduct

open BilateralThreeCell

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) (k : Type*) [Ring k] {P : Set X}

/-- The bilateral cell of a compressed clopen `P` in `R_X`: `u` the implementing unit and
`p = 1_P` (tex 1550–1551). -/
noncomputable def bilateralCell (hP : IsClopen P) (hTP : T '' P ⊆ P) :
    Cell (ClopenCrossedProduct T k) where
  u := unit T k
  p := defectP T k hP
  p_mul_p := defectP_mul_defectP T k hP
  conj_mul_p := by
    rw [unit_mul_defectP_mul_inv T k hP, defectP, ← map_mul,
      charFn_mul_charFn_of_subset k (isClopen_image T hP) hP hTP]
  p_mul_conj := by
    rw [unit_mul_defectP_mul_inv T k hP, defectP, ← map_mul,
      charFn_mul_charFn_of_superset k hP (isClopen_image T hP) hTP]

@[simp] theorem bilateralCell_u (hP : IsClopen P) (hTP : T '' P ⊆ P) :
    (bilateralCell T k hP hTP).u = unit T k := rfl

@[simp] theorem bilateralCell_p (hP : IsClopen P) (hTP : T '' P ⊆ P) :
    (bilateralCell T k hP hTP).p = defectP T k hP := rfl

/-- "$d=1_D$" (tex 1551): the defect of the cell is `1_{P∖T(P)}`. -/
theorem bilateralCell_d (hP : IsClopen P) (hTP : T '' P ⊆ P) :
    (bilateralCell T k hP hTP).d = defectD T k hP := by
  rw [Cell.d, Cell.lvl_one, defectD_eq_sub T k hP hTP]
  exact congrArg (fun x => defectP T k hP - x) (unit_mul_defectP_mul_inv T k hP)

/-- "nonempty $D=P\setminus T(P)$" (tex 1550–1551) makes the defect nonzero. -/
theorem defectD_ne_zero [Nontrivial k] (hP : IsClopen P) {x : X} (hx : x ∈ P \ T '' P) :
    defectD T k hP ≠ 0 := by
  intro h
  rw [defectD, ← map_zero (coeff T k)] at h
  have h2 := congrArg (fun f : LocallyConstant X k => f x) (coeff_injective T k h)
  simp [LocallyConstant.coe_charFn, Set.indicator_of_mem hx] at h2

end ClopenCrossedProduct
end GroupApproximation

open GroupApproximation

#audit_axioms GroupApproximation.ClopenCrossedProduct.bilateralCell_d
#audit_axioms GroupApproximation.ClopenCrossedProduct.defectD_ne_zero
