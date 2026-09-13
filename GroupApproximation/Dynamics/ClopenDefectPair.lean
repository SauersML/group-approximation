import GroupApproximation.Dynamics.ClopenCrossedProduct
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Tactic.NoncommRing

/-!
# The clopen defect pair

`non_mf_groups_exist.tex`, proof of `lem:chain-core-models`, tex 1456–1462:

> Pull back the symbolic defects to cover $X\setminus Y$ by their translates.  They avoid $Y$: for
> any compressed clopen $P$, set $p=1_P$, $d=1_{P\setminus T(P)}$ and calculate
> \begin{equation}\label{eq:clopen-defect-pair}
>  s=up+1-p,\qquad t=pu^{-1}+1-p,\qquad ts=1,\qquad st=1-d.
> \end{equation}
> Restriction to the directly finite ring $R_Y$ forces $d|_Y=0$.

The compressed clopen sets are those of the lemma statement: `P` clopen with `T(P) ⊆ P`.

* `mul_eq_one_of_conj`, `mul_eq_one_sub_of_conj`: the calculation in any ring, for an idempotent
  `p`, elements with `v * w = 1`, and `q = w p v` with `q p = q = p q`;
* `defectP`, `defectS`, `defectT`, `defectD`: `p = 1_P`, `s`, `t` and `d = 1_{P∖T(P)}` in
  `R_X = ClopenCrossedProduct T k`;
* `defectT_mul_defectS : t * s = 1` and `defectS_mul_defectT : s * t = 1 - d`, with the closed
  endpoint `printedClopenDefectPair`;
* `map_defectD_eq_zero`: a unital ring homomorphism into a directly finite ring kills `d`;
* `two_nsmul_defectD`: `2 • d = 0` when `2 = 0` in `k` (thm:core-mf-radical, tex 1646–1647).
-/

namespace GroupApproximation

namespace ClopenCrossedProduct

section Calculation

variable {S : Type*} [Ring S]

/-- `ts = 1` in any ring: `(p v + 1 - p) (w p + 1 - p) = 1` for an idempotent `p`, `v w = 1`, and
`q = w p v` with `q p = q = p q`. -/
theorem mul_eq_one_of_conj {p q v w : S} (hvw : v * w = 1) (hp : p * p = p) (hqp : q * p = q)
    (hpq : p * q = q) (hconj : w * p * v = q) :
    (p * v + 1 - p) * (w * p + 1 - p) = 1 := by
  have hpv : p * v = v * q := by
    rw [← hconj, ← mul_assoc, ← mul_assoc, hvw, one_mul]
  have hwp : w * p = q * w := by
    rw [← hconj, mul_assoc (w * p) v w, hvw, mul_one]
  have e : (p * v + 1 - p) * (w * p + 1 - p) - 1 =
      p * (v * w - 1) * p + (p * p - p) + (p * p - p) +
        ((p * v - v * q) - (p * v - v * q) * p + v * (q - q * p)) +
        ((w * p - q * w) - p * (w * p - q * w) + (q - p * q) * w) := by
    noncomm_ring
  rw [← sub_eq_zero, e, sub_eq_zero.2 hvw, sub_eq_zero.2 hp, sub_eq_zero.2 hpv,
    sub_eq_zero.2 hqp.symm, sub_eq_zero.2 hwp, sub_eq_zero.2 hpq.symm]
  simp

/-- `st = 1 - d` in any ring: `(w p + 1 - p) (p v + 1 - p) = 1 - (p - q)` for an idempotent `p`
and `q = w p v`. -/
theorem mul_eq_one_sub_of_conj {p q v w : S} (hp : p * p = p) (hconj : w * p * v = q) :
    (w * p + 1 - p) * (p * v + 1 - p) = 1 - (p - q) := by
  have e : (w * p + 1 - p) * (p * v + 1 - p) - (1 - (p - q)) =
      w * (p * p - p) * v + (w * p * v - q) - w * (p * p - p) - (p * p - p) * v +
        (p * p - p) := by
    noncomm_ring
  rw [← sub_eq_zero, e, sub_eq_zero.2 hp, sub_eq_zero.2 hconj]
  simp

end Calculation

section Defect

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) (k : Type*) [Ring k] {P : Set X}

/-- `p = 1_P` in `R_X`, for a clopen set `P`. -/
noncomputable def defectP (hP : IsClopen P) : ClopenCrossedProduct T k :=
  coeff T k (LocallyConstant.charFn k hP)

/-- `s = u p + 1 - p`. -/
noncomputable def defectS (hP : IsClopen P) : ClopenCrossedProduct T k :=
  (unit T k : ClopenCrossedProduct T k) * defectP T k hP + 1 - defectP T k hP

/-- `t = p u⁻¹ + 1 - p`. -/
noncomputable def defectT (hP : IsClopen P) : ClopenCrossedProduct T k :=
  defectP T k hP * ↑(unit T k)⁻¹ + 1 - defectP T k hP

/-- `d = 1_{P∖T(P)}`. -/
noncomputable def defectD (hP : IsClopen P) : ClopenCrossedProduct T k :=
  coeff T k (LocallyConstant.charFn k (hP.diff (isClopen_image T hP)))

/-- `u p u⁻¹ = 1_{T(P)}`. -/
theorem unit_mul_defectP_mul_inv (hP : IsClopen P) :
    (unit T k : ClopenCrossedProduct T k) * defectP T k hP * ↑(unit T k)⁻¹ =
      coeff T k (LocallyConstant.charFn k (isClopen_image T hP)) := by
  rw [defectP, unit_mul_coeff_mul_inv, comap_symm_charFn]

theorem defectP_mul_defectP (hP : IsClopen P) :
    defectP T k hP * defectP T k hP = defectP T k hP := by
  rw [defectP, ← map_mul, charFn_mul_charFn_of_subset k hP hP subset_rfl]

/-- `d = p - 1_{T(P)}` for a compressed clopen `P`. -/
theorem defectD_eq_sub (hP : IsClopen P) (hTP : T '' P ⊆ P) :
    defectD T k hP =
      defectP T k hP - coeff T k (LocallyConstant.charFn k (isClopen_image T hP)) := by
  rw [defectD, defectP, ← map_sub, charFn_sub_charFn_of_subset k hP (isClopen_image T hP) hTP]

/-- **`ts = 1`** (eq:clopen-defect-pair). -/
theorem defectT_mul_defectS (hP : IsClopen P) (hTP : T '' P ⊆ P) :
    defectT T k hP * defectS T k hP = 1 := by
  refine mul_eq_one_of_conj (Units.inv_mul (unit T k)) (defectP_mul_defectP T k hP) ?_ ?_
    (unit_mul_defectP_mul_inv T k hP)
  · rw [defectP, ← map_mul, charFn_mul_charFn_of_subset k (isClopen_image T hP) hP hTP]
  · rw [defectP, ← map_mul, charFn_mul_charFn_of_superset k hP (isClopen_image T hP) hTP]

/-- **`st = 1 - d`** (eq:clopen-defect-pair). -/
theorem defectS_mul_defectT (hP : IsClopen P) (hTP : T '' P ⊆ P) :
    defectS T k hP * defectT T k hP = 1 - defectD T k hP := by
  rw [defectD_eq_sub T k hP hTP]
  exact mul_eq_one_sub_of_conj (defectP_mul_defectP T k hP) (unit_mul_defectP_mul_inv T k hP)

/-- "Restriction to the directly finite ring $R_Y$ forces $d|_Y=0$" (tex 1462), in the form
consumed downstream: a unital ring homomorphism from `R_X` into a directly finite ring kills `d`. -/
theorem map_defectD_eq_zero {A : Type*} [Ring A] [IsDedekindFiniteMonoid A]
    (φ : ClopenCrossedProduct T k →+* A) (hP : IsClopen P) (hTP : T '' P ⊆ P) :
    φ (defectD T k hP) = 0 := by
  have hts : φ (defectT T k hP) * φ (defectS T k hP) = 1 := by
    rw [← map_mul, defectT_mul_defectS T k hP hTP, map_one]
  have hst := congrArg φ (defectS_mul_defectT T k hP hTP)
  rw [map_mul, mul_eq_one_symm hts, map_sub, map_one] at hst
  calc φ (defectD T k hP) = 1 - (1 - φ (defectD T k hP)) := (sub_sub_cancel _ _).symm
    _ = 0 := by rw [← hst, sub_self]

/-- "the defects in \eqref{eq:clopen-defect-pair}, which have additive order at most two"
(thm:core-mf-radical, tex 1646–1647, where `k = 𝔽₂`): `2 • d = 0` when `2 = 0` in `k`. -/
theorem two_nsmul_defectD (h2 : (2 : k) = 0) (hP : IsClopen P) : 2 • defectD T k hP = 0 := by
  have hc : ∀ c : LocallyConstant X k, c + c = 0 := fun c => LocallyConstant.ext fun x => by
    show c x + c x = 0
    rw [← two_mul, h2, zero_mul]
  rw [two_nsmul, defectD, ← map_add, hc, map_zero]

end Defect

/-- **eq:clopen-defect-pair** (tex 1457–1461): "for any compressed clopen $P$, set $p=1_P$,
$d=1_{P\setminus T(P)}$ and calculate $s=up+1-p$, $t=pu^{-1}+1-p$, $ts=1$, $st=1-d$."

The identities hold for every topological space `X`, homeomorphism `T`, ring `k` and clopen `P`
with `T(P) ⊆ P`; the printed hypotheses on `X` and `k` are not used. -/
def PrintedClopenDefectPair : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (T : X ≃ₜ X) (k : Type) [Ring k] (P : Set X)
    (hP : IsClopen P), T '' P ⊆ P →
      (coeff T k (LocallyConstant.charFn k hP) * ↑(unit T k)⁻¹ + 1 -
          coeff T k (LocallyConstant.charFn k hP)) *
        ((unit T k : ClopenCrossedProduct T k) * coeff T k (LocallyConstant.charFn k hP) + 1 -
          coeff T k (LocallyConstant.charFn k hP)) = 1 ∧
      ((unit T k : ClopenCrossedProduct T k) * coeff T k (LocallyConstant.charFn k hP) + 1 -
          coeff T k (LocallyConstant.charFn k hP)) *
        (coeff T k (LocallyConstant.charFn k hP) * ↑(unit T k)⁻¹ + 1 -
          coeff T k (LocallyConstant.charFn k hP)) =
        1 - coeff T k (LocallyConstant.charFn k (hP.diff (isClopen_image T hP)))

theorem printedClopenDefectPair : PrintedClopenDefectPair := by
  intro _ _ T k _ _ hP hTP
  exact ⟨defectT_mul_defectS T k hP hTP, defectS_mul_defectT T k hP hTP⟩

end ClopenCrossedProduct

end GroupApproximation

open GroupApproximation

#audit_closed_axioms GroupApproximation.ClopenCrossedProduct.printedClopenDefectPair
#audit_axioms GroupApproximation.ClopenCrossedProduct.map_defectD_eq_zero
#audit_axioms GroupApproximation.ClopenCrossedProduct.two_nsmul_defectD
