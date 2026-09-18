import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Three commutator identities for the relator reduction of van der Kallen row data

Lane `bh-met-90p`.  Pure group theory, used by `VdKDiagCore` to derive the row relators that
do not touch a fixed index from those that do.

* `vdkDiag_commute_commutator`: an element commuting with `y` and `z` commutes with `⁅y, z⁆`.
* `vdkDiag_commutator_nested`: if `c` commutes with `z`, `⁅c, y⁆ = w`, `⁅w, z⁆ = v`, and `w`, `v`
  commute with `e = ⁅y, z⁆`, then `⁅c, e⁆ = v`.
* `vdkDiag_commutator_conj_inv`: if `e = ⁅s, t⁆`, `s` commutes with `d`, `⁅d, t⁆ = p`,
  `⁅s, p⁆ = q` and `p` commutes with `e`, then `⁅e, d⁆ = q⁻¹`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open scoped commutatorElement

/-- An element commuting with `y` and `z` commutes with `⁅y, z⁆`. -/
theorem vdkDiag_commute_commutator {G : Type*} [Group G] {a y z : G} (hy : Commute a y)
    (hz : Commute a z) : Commute a ⁅y, z⁆ := by
  rw [commutatorElement_def]
  exact ((hy.mul_right hz).mul_right hy.inv_right).mul_right hz.inv_right

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkDiag_commute_commutator

/-- The Hall–Witt step behind `⁅x_{i,last}(a), x_{last,k}(b)⁆ = x_{ik}(ab)`:
`c e c⁻¹ = ⁅w y, z⁆ = w e w⁻¹ ⁅w, z⁆ = e v`, so `⁅c, e⁆ = e v e⁻¹ = v`. -/
theorem vdkDiag_commutator_nested {G : Type*} [Group G] {c y z e w v : G}
    (hE : ⁅y, z⁆ = e) (hCZ : Commute c z) (hCY : ⁅c, y⁆ = w) (hWZ : ⁅w, z⁆ = v)
    (hWE : Commute w e) (hVE : Commute v e) : ⁅c, e⁆ = v := by
  subst hE
  have hy : c * y * c⁻¹ = w * y := by
    rw [← hCY]
    group
  have hz : c * z * c⁻¹ = z := by rw [hCZ.eq, mul_inv_cancel_right]
  have hconj : c * ⁅y, z⁆ * c⁻¹ = ⁅c * y * c⁻¹, c * z * c⁻¹⁆ := by group
  have hprod : ⁅w * y, z⁆ = w * ⁅y, z⁆ * w⁻¹ * ⁅w, z⁆ := by group
  have hw : w * ⁅y, z⁆ * w⁻¹ = ⁅y, z⁆ := by rw [hWE.eq, mul_inv_cancel_right]
  rw [hy, hz, hprod, hw, hWZ] at hconj
  calc ⁅c, ⁅y, z⁆⁆ = c * ⁅y, z⁆ * c⁻¹ * ⁅y, z⁆⁻¹ := commutatorElement_def _ _
    _ = v := by rw [hconj, ← hVE.eq, mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkDiag_commutator_nested

/-- The Hall–Witt step behind `⁅x_{last,j}(a), x_{jk}(b)⁆ = x_{last,k}(ab)`:
`d e d⁻¹ = ⁅s, p t⁆ = ⁅s, p⁆ (p e p⁻¹) = q e`, so `⁅e, d⁆ = e (q e)⁻¹ = q⁻¹`. -/
theorem vdkDiag_commutator_conj_inv {G : Type*} [Group G] {s t d e p q : G}
    (hE : ⁅s, t⁆ = e) (hSD : Commute s d) (hDT : ⁅d, t⁆ = p) (hSP : ⁅s, p⁆ = q)
    (hPE : Commute p e) : ⁅e, d⁆ = q⁻¹ := by
  subst hE
  have hs : d * s * d⁻¹ = s := by rw [← hSD.eq, mul_inv_cancel_right]
  have ht : d * t * d⁻¹ = p * t := by
    rw [← hDT]
    group
  have hconj : d * ⁅s, t⁆ * d⁻¹ = ⁅d * s * d⁻¹, d * t * d⁻¹⁆ := by group
  have hprod : ⁅s, p * t⁆ = ⁅s, p⁆ * (p * ⁅s, t⁆ * p⁻¹) := by group
  have hp : p * ⁅s, t⁆ * p⁻¹ = ⁅s, t⁆ := by rw [hPE.eq, mul_inv_cancel_right]
  rw [hs, ht, hprod, hp, hSP] at hconj
  calc ⁅⁅s, t⁆, d⁆ = ⁅s, t⁆ * (d * ⁅s, t⁆ * d⁻¹)⁻¹ := by group
    _ = q⁻¹ := by
      rw [hconj]
      group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkDiag_commutator_conj_inv

end GroupApproximation.BooneHigman.Metabelian.ElemFP
