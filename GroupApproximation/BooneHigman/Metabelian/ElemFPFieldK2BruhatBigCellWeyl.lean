import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2BruhatBigCellPar
import GroupApproximation.Meta.AxiomGuard

/-!
# Big Bruhat cell, part 4: conjugating by the Weyl element `w_jL(c)`

Lane `bh-met-64c`.  Fix `j ∈ K` and write `W = w_jL(c)`.

Proof route:

* `W U W⁻¹ ⊆ P`.  On generators `x_iL(t)` with `i ∈ K`:
  * for `i = j`, `w_conj_x_self` sends the root to `x_Lj(·) ∈ V`;
  * for `i ≠ j`, `w_conj_x_col_j` sends it to `x_ij(·) ∈ S`.
* `W U_{≠j} W⁻¹ ⊆ S` (`w_conj_x_col_j`), and `W V_{≠j} W⁻¹ ⊆ S` (`w_conj_x_row_j`).
* The same holds for `W⁻¹ (·) W`, since `w(c)⁻¹ = w(-c)` (`w_inv`).
* `w(u₁) w(u₂) = h(u₁) h(-u₂)⁻¹ ∈ P` (`bruhatBigCell_hb_mem_par`).
* Two root identities, each closed by `group` after unfolding `w`:
  * row: `x_Lj(e) = x_jL(e⁻¹) w_jL(-e⁻¹) x_jL(e⁻¹)`;
  * column: `x_bL(d) = x_Lb(d⁻¹) w_bL(d) x_Lb(d⁻¹)` (`w_eq_alt`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h w_inv w_conj_x_row_j
  w_conj_x_col_j)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan
  rootSpan_conj_mem)

variable {I R : Type*} [Fintype I] [DecidableEq I] [Field R]

/-- Conjugation by `w(u)⁻¹` is conjugation by `w(-u)`. -/
theorem bruhatBigCell_w_inv_conj (i j : I) (hij : i ≠ j) (u : Rˣ) (g : SteinbergGroup I R) :
    (w i j hij u)⁻¹ * g * w i j hij u = w i j hij (-u) * g * (w i j hij (-u))⁻¹ := by
  rw [w_inv i j hij u, w_inv i j hij (-u), neg_neg]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_w_inv_conj

/-- `w_jL(c) U w_jL(c)⁻¹ ⊆ P`. -/
theorem bruhatBigCell_w_conj_U (σ : BruhatBigCellData I R) {j : I} (hj : j ∈ σ.K) (c : Rˣ)
    {u : SteinbergGroup I R} (hu : u ∈ bruhatBigCellU R σ.K σ.L) :
    w j σ.L (bruhatBigCell_ne σ.hLK hj) c * u * (w j σ.L (bruhatBigCell_ne σ.hLK hj) c)⁻¹ ∈
      bruhatBigCellPar σ := by
  refine rootSpan_conj_mem (p := fun i l => l = σ.L ∧ i ∈ σ.K) ?_ hu
  intro i l hil t hp
  obtain ⟨hl, hi⟩ := hp
  subst l
  by_cases hij : i = j
  · subst i
    obtain ⟨k, hjk, hLk⟩ := σ.third j σ.L
    rw [w_conj_x_self j σ.L k (bruhatBigCell_ne σ.hLK hj) hjk hLk c t]
    exact bruhatBigCell_V_le_par σ (bruhatBigCell_x_mem_V _ _ hj)
  · rw [w_conj_x_col_j j σ.L i (bruhatBigCell_ne σ.hLK hj) hij hil c t]
    exact bruhatBigCell_S_le_par σ (bruhatBigCell_x_mem_S hij _ hi hj)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_w_conj_U

/-- `w_jL(c)⁻¹ U w_jL(c) ⊆ P`. -/
theorem bruhatBigCell_w_inv_conj_U (σ : BruhatBigCellData I R) {j : I} (hj : j ∈ σ.K)
    (c : Rˣ) {u : SteinbergGroup I R} (hu : u ∈ bruhatBigCellU R σ.K σ.L) :
    (w j σ.L (bruhatBigCell_ne σ.hLK hj) c)⁻¹ * u * w j σ.L (bruhatBigCell_ne σ.hLK hj) c ∈
      bruhatBigCellPar σ := by
  rw [bruhatBigCell_w_inv_conj]
  exact bruhatBigCell_w_conj_U σ hj (-c) hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_w_inv_conj_U

/-- `w_bL(c) U_{≠b} w_bL(c)⁻¹ ⊆ S`. -/
theorem bruhatBigCell_w_conj_Uex (σ : BruhatBigCellData I R) {b : I} (hb : b ∈ σ.K) (c : Rˣ)
    {u : SteinbergGroup I R} (hu : u ∈ bruhatBigCellUex R σ.K σ.L b) :
    w b σ.L (bruhatBigCell_ne σ.hLK hb) c * u * (w b σ.L (bruhatBigCell_ne σ.hLK hb) c)⁻¹ ∈
      bruhatBigCellS R σ.K := by
  refine rootSpan_conj_mem (p := fun i l => l = σ.L ∧ i ∈ σ.K ∧ i ≠ b) ?_ hu
  intro i l hil t hp
  obtain ⟨hl, hi, hib⟩ := hp
  subst l
  rw [w_conj_x_col_j b σ.L i (bruhatBigCell_ne σ.hLK hb) hib hil c t]
  exact bruhatBigCell_x_mem_S hib _ hi hb

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_w_conj_Uex

/-- `w_jL(c) V_{≠j} w_jL(c)⁻¹ ⊆ S`. -/
theorem bruhatBigCell_w_conj_Vex (σ : BruhatBigCellData I R) {j : I} (hj : j ∈ σ.K) (c : Rˣ)
    {v : SteinbergGroup I R} (hv : v ∈ bruhatBigCellVex R σ.K σ.L j) :
    w j σ.L (bruhatBigCell_ne σ.hLK hj) c * v * (w j σ.L (bruhatBigCell_ne σ.hLK hj) c)⁻¹ ∈
      bruhatBigCellS R σ.K := by
  refine rootSpan_conj_mem (p := fun i l => i = σ.L ∧ l ∈ σ.K ∧ l ≠ j) ?_ hv
  intro i l hil t hp
  obtain ⟨hi, hl, hlj⟩ := hp
  subst i
  rw [w_conj_x_row_j j σ.L l (bruhatBigCell_ne σ.hLK hj) (Ne.symm hlj) hil c t]
  exact bruhatBigCell_x_mem_S (Ne.symm hlj) _ hj hl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_w_conj_Vex

/-- `w_jL(c)⁻¹ V_{≠j} w_jL(c) ⊆ S`. -/
theorem bruhatBigCell_w_inv_conj_Vex (σ : BruhatBigCellData I R) {j : I} (hj : j ∈ σ.K)
    (c : Rˣ) {v : SteinbergGroup I R} (hv : v ∈ bruhatBigCellVex R σ.K σ.L j) :
    (w j σ.L (bruhatBigCell_ne σ.hLK hj) c)⁻¹ * v * w j σ.L (bruhatBigCell_ne σ.hLK hj) c ∈
      bruhatBigCellS R σ.K := by
  rw [bruhatBigCell_w_inv_conj]
  exact bruhatBigCell_w_conj_Vex σ hj (-c) hv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_w_inv_conj_Vex

/-- `w(u₁) w(u₂) = h(u₁) h(-u₂)⁻¹`. -/
theorem bruhatBigCell_ww_eq (i j : I) (hij : i ≠ j) (u₁ u₂ : Rˣ) :
    w i j hij u₁ * w i j hij u₂ = h i j hij u₁ * (h i j hij (-u₂))⁻¹ := by
  show _ = w i j hij u₁ * w i j hij (-1) * (w i j hij (-u₂) * w i j hij (-1))⁻¹
  rw [mul_inv_rev, w_inv i j hij (-u₂), neg_neg]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_ww_eq

/-- `w_jL(u₁) w_jL(u₂) ∈ P` for `j ∈ K`. -/
theorem bruhatBigCell_ww_mem (σ : BruhatBigCellData I R) {j : I} (hj : j ∈ σ.K)
    (u₁ u₂ : Rˣ) :
    w j σ.L (bruhatBigCell_ne σ.hLK hj) u₁ * w j σ.L (bruhatBigCell_ne σ.hLK hj) u₂ ∈
      bruhatBigCellPar σ := by
  rw [bruhatBigCell_ww_eq]
  exact Subgroup.mul_mem _ (bruhatBigCell_hb_mem_par σ hj u₁)
    (Subgroup.inv_mem _ (bruhatBigCell_hb_mem_par σ hj (-u₂)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_ww_mem

/-- Row identity: `x_Lj(e) = x_jL(e⁻¹) w_jL(-e⁻¹) x_jL(e⁻¹)`. -/
theorem bruhatBigCell_row_id (j L : I) (hjL : j ≠ L) (e : Rˣ) :
    x L j hjL.symm (e : R) =
      x j L hjL ((e⁻¹ : Rˣ) : R) * w j L hjL (-e⁻¹) * x j L hjL ((e⁻¹ : Rˣ) : R) := by
  rw [w]
  have h1 : ((-e⁻¹ : Rˣ) : R) = -((e⁻¹ : Rˣ) : R) := Units.val_neg _
  have h2 : -((((-e⁻¹ : Rˣ))⁻¹ : Rˣ) : R) = (e : R) := by
    rw [inv_neg, inv_inv, Units.val_neg, neg_neg]
  rw [h1, h2, x_neg]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_row_id

/-- Column identity: `x_bL(d) = x_Lb(d⁻¹) w_bL(d) x_Lb(d⁻¹)`. -/
theorem bruhatBigCell_col_id (b L k : I) (hbL : b ≠ L) (hbk : b ≠ k) (hLk : L ≠ k)
    (dd : Rˣ) :
    x b L hbL (dd : R) =
      x L b hbL.symm ((dd⁻¹ : Rˣ) : R) * w b L hbL dd * x L b hbL.symm ((dd⁻¹ : Rˣ) : R) := by
  rw [w_eq_alt b L k hbL hbk hLk dd, x_neg]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_col_id

end GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2
