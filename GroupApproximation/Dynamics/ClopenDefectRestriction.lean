import GroupApproximation.Dynamics.ClopenCrossedProductComap
import GroupApproximation.Dynamics.ClopenDefectPair
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Data.ZMod.Defs

/-!
# Clopen defects avoid a directly finite invariant set

`non_mf_groups_exist.tex`, proof of `lem:chain-core-models`, tex 1454–1461:

> They avoid $Y$: for any compressed clopen $P$, set $p=1_P$, $d=1_{P\setminus T(P)}$ and calculate
> \begin{equation}\label{eq:clopen-defect-pair}
>  s=up+1-p,\qquad t=pu^{-1}+1-p,\qquad ts=1,\qquad st=1-d.
> \end{equation}
> Restriction to the directly finite ring $R_Y$ forces $d|_Y=0$.

and the proof of `thm:core-mf-radical` (tex 1552, where $k=\F_2$):

> Each defect $d$ in \eqref{eq:clopen-defect-pair} has additive order at most two.

`R_Y` is `ClopenCrossedProduct (restrictHomeo T hY) k` and restriction is `restrict T k hY`
(`GroupApproximation.Dynamics.ClopenCrossedProductComap`).

* `restrict_defectD_eq_zero`: `d` restricts to `0` in a directly finite `R_Y`;
* `notMem_diff_image_of_mem`: so `P ∖ T(P)` misses `Y`;
* closed endpoints `printedDefectsAvoidY` (tex 1454), `printedRestrictionKillsDefect` (tex 1460) and
  `printedDefectAdditiveOrderTwo` (tex 1552).
-/

namespace GroupApproximation

namespace ClopenCrossedProduct

section Restriction

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) (k : Type*) [Ring k] {Y : Set X} {P : Set X}

/-- "Restriction to the directly finite ring $R_Y$ forces $d|_Y=0$": `d` restricts to `0`. -/
theorem restrict_defectD_eq_zero (hY : T '' Y = Y)
    [IsDedekindFiniteMonoid (ClopenCrossedProduct (restrictHomeo T hY) k)]
    (hP : IsClopen P) (hTP : T '' P ⊆ P) : restrict T k hY (defectD T k hP) = 0 :=
  map_defectD_eq_zero T k (restrict T k hY) hP hTP

/-- `d|_Y = 0` pointwise: the defect set `P ∖ T(P)` misses `Y`. -/
theorem notMem_diff_image_of_mem [Nontrivial k] (hY : T '' Y = Y)
    [IsDedekindFiniteMonoid (ClopenCrossedProduct (restrictHomeo T hY) k)]
    (hP : IsClopen P) (hTP : T '' P ⊆ P) {y : X} (hy : y ∈ Y) : y ∉ P \ T '' P := by
  have h0 := restrict_defectD_eq_zero T k hY hP hTP
  rw [defectD, restrict_coeff] at h0
  have h1 := DFunLike.congr_fun
    (coeff_injective (restrictHomeo T hY) k
      (h0.trans (map_zero (coeff (restrictHomeo T hY) k)).symm)) ⟨y, hy⟩
  change LocallyConstant.charFn k (hP.diff (isClopen_image T hP)) y = 0 at h1
  exact (LocallyConstant.charFn_eq_zero k y _).1 h1

end Restriction

/-- **tex 1460** (proof of `lem:chain-core-models`): "Restriction to the directly finite ring $R_Y$
forces $d|_Y=0$."  For every invariant `Y` with `R_Y` directly finite and every compressed clopen
`P`, the defect `d = 1_{P∖T(P)}` restricts to `0` in `R_Y`, and `P ∖ T(P)` misses `Y`.

The printed hypotheses on `X` and `k` (compact metrizable zero-dimensional; a finite field) and the
closedness of `Y` are not used; only `1 ≠ 0` in `k` is. -/
def PrintedRestrictionKillsDefect : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (T : X ≃ₜ X) (k : Type) [Ring k] [Nontrivial k] (Y : Set X)
    (hY : T '' Y = Y), IsDedekindFiniteMonoid (ClopenCrossedProduct (restrictHomeo T hY) k) →
    ∀ (P : Set X) (hP : IsClopen P), T '' P ⊆ P →
      restrict T k hY (defectD T k hP) = 0 ∧ ∀ y ∈ Y, y ∉ P \ T '' P

theorem printedRestrictionKillsDefect : PrintedRestrictionKillsDefect := by
  intro _ _ T k _ _ _ hY _ _ hP hTP
  exact ⟨restrict_defectD_eq_zero T k hY hP hTP,
    fun _ hy => notMem_diff_image_of_mem T k hY hP hTP hy⟩

/-- **tex 1454** (proof of `lem:chain-core-models`): "They avoid $Y$: for any compressed clopen $P$,
set $p=1_P$, $d=1_{P\setminus T(P)}$ and calculate" \eqref{eq:clopen-defect-pair}.  With `R_Y`
directly finite: `ts = 1`, `st = 1 - d`, and the defect set `P ∖ T(P)` is disjoint from `Y`. -/
def PrintedDefectsAvoidY : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (T : X ≃ₜ X) (k : Type) [Ring k] [Nontrivial k] (Y : Set X)
    (hY : T '' Y = Y), IsDedekindFiniteMonoid (ClopenCrossedProduct (restrictHomeo T hY) k) →
    ∀ (P : Set X) (hP : IsClopen P), T '' P ⊆ P →
      defectT T k hP * defectS T k hP = 1 ∧
        defectS T k hP * defectT T k hP = 1 - defectD T k hP ∧ (P \ T '' P) ∩ Y = ∅

theorem printedDefectsAvoidY : PrintedDefectsAvoidY := by
  intro _ _ T k _ _ _ hY _ _ hP hTP
  refine ⟨defectT_mul_defectS T k hP hTP, defectS_mul_defectT T k hP hTP, ?_⟩
  exact Set.eq_empty_of_forall_notMem fun _ hy =>
    notMem_diff_image_of_mem T k hY hP hTP hy.2 hy.1

/-- **tex 1552** (proof of `thm:core-mf-radical`, where $k=\F_2$): "Each defect $d$ in
\eqref{eq:clopen-defect-pair} has additive order at most two." -/
def PrintedDefectAdditiveOrderTwo : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (T : X ≃ₜ X) (P : Set X) (hP : IsClopen P),
    2 • defectD T (ZMod 2) hP = 0

theorem printedDefectAdditiveOrderTwo : PrintedDefectAdditiveOrderTwo := by
  intro _ _ T _ hP
  exact two_nsmul_defectD T (ZMod 2) (by decide) hP

end ClopenCrossedProduct

end GroupApproximation

open GroupApproximation

#audit_closed_axioms GroupApproximation.ClopenCrossedProduct.printedRestrictionKillsDefect
#audit_closed_axioms GroupApproximation.ClopenCrossedProduct.printedDefectsAvoidY
#audit_closed_axioms GroupApproximation.ClopenCrossedProduct.printedDefectAdditiveOrderTwo
