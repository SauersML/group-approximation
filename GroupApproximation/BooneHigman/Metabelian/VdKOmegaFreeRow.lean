import GroupApproximation.BooneHigman.Metabelian.VdKOmegaRowPar
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabRow
import GroupApproximation.Meta.AxiomGuard

/-!
# `vdkOmegaFree`, part 3: `Π⁻` is injective once `stab` is

Lane `bh-met-93j`.  Unconditional apart from the displayed hypothesis.

* `vdkOmegaFree_padRow_eq_rowVec`: the two last-row vectors `padRow` (`PaddedCentral`) and
  `rowVec` (`RowColumn`) agree.
* `vdkOmegaFree_PiMinus_injective`: if `stab : St_n(R) → St_{n+1}(R)` is injective then so
  is `Π⁻ : R^n ⋊ St_n(R) → St_{n+1}(R)`, `(w, g) ↦ rowVec w · stab g`.  The proof reads
  the last row: `stab g` fixes `e = (0, …, 0, 1)` and `rowVec w` sends it to `(w, 1)`.
* `vdkOmegaFree_mixed_root`: `⁅x_{i,last}(1), x_{last,j}(1)⁆ = stab (x_{ij}(1))`.

Truth check.  `Π⁻(w, g) = 1` means `M = [[g, 0], [w, 1]] = 1` in `E_{n+1}`.  Its last row forces
`w = 0`, and then `stab g = 1` forces `g = 1`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
  (colRoot rowRoot rowVec rowVec_add rowVec_zero rowVec_update_zero)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
  (padRow padRow_add padRow_zero padRow_single)
open GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
  (surjStabVec_inj surjStab_vecMul_stab surjStab_vecMul_padRow)
open scoped commutatorElement

variable {n : ℕ} {R : Type*} [CommRing R]

theorem vdkOmegaFree_padRow_eq_rowVec (v : Fin n → R) : padRow v = rowVec v := by
  induction v using Pi.single_induction with
  | zero => rw [padRow_zero, rowVec_zero]
  | add f g hf hg => rw [padRow_add, rowVec_add, hf, hg]
  | single p a => exact (padRow_single p a).trans (rowVec_update_zero p a).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_padRow_eq_rowVec

theorem vdkOmegaFree_PiMinus_apply (q : vdkOmega_TildeMinus n R) :
    vdkOmega_PiMinus q = rowVec (Multiplicative.toAdd q.left) * stab n R q.right :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_PiMinus_apply

/-- **`Π⁻` is injective once `stab` is.** -/
theorem vdkOmegaFree_PiMinus_injective (hinj : Function.Injective (stab n R)) :
    Function.Injective (vdkOmega_PiMinus (n := n) (R := R)) := by
  refine (injective_iff_map_eq_one _).mpr fun q hq ↦ ?_
  have h1 : rowVec (Multiplicative.toAdd q.left) * stab n R q.right = 1 :=
    (vdkOmegaFree_PiMinus_apply q).symm.trans hq
  have h3 : rowVec (-Multiplicative.toAdd q.left) * rowVec (Multiplicative.toAdd q.left) = 1 := by
    rw [← rowVec_add, neg_add_cancel, rowVec_zero]
  have h2 : stab n R q.right = padRow (-Multiplicative.toAdd q.left) := by
    rw [vdkOmegaFree_padRow_eq_rowVec, eq_inv_of_mul_eq_one_left h3]
    exact eq_inv_of_mul_eq_one_right h1
  have e := surjStab_vecMul_stab (R := R) q.right
  rw [h2, surjStab_vecMul_padRow, zero_add] at e
  have hv : -Multiplicative.toAdd q.left = 0 := surjStabVec_inj e
  have hv0 : Multiplicative.toAdd q.left = 0 := neg_eq_zero.mp hv
  have hs : padRow (-Multiplicative.toAdd q.left) = stab n R 1 := by
    rw [hv, padRow_zero, map_one]
  have hg : q.right = 1 := hinj (h2.trans hs)
  refine SemidirectProduct.ext ?_ hg
  exact (ofAdd_toAdd q.left).symm.trans ((congrArg Multiplicative.ofAdd hv0).trans ofAdd_zero)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_PiMinus_injective

/-- `⁅x_{i,last}(1), x_{last,j}(1)⁆ = stab (x_{ij}(1))`. -/
theorem vdkOmegaFree_mixed_root (i j : Fin n) (hij : i ≠ j) :
    ⁅colRoot i (1 : R), rowRoot j (1 : R)⁆ = stab n R (x i j hij 1) := by
  rw [stab_x]
  have e := x_commutator (R := R) i.castSucc (Fin.last n) j.castSucc (Fin.castSucc_ne_last i)
    (Fin.castSucc_ne_last j).symm (fun h ↦ hij (Fin.castSucc_inj.mp h)) 1 1
  rw [mul_one] at e
  exact e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_mixed_root

end GroupApproximation.BooneHigman.Metabelian.ElemFP
