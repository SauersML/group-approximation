import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2BruhatBigCellWeyl
import GroupApproximation.Meta.AxiomGuard

/-!
# Big Bruhat cell, part 5: the union `U P ∪ S W P` is stable under left multiplication

Lane `bh-met-64c`.  With `P = bruhatBigCellPar σ`, the two cells are

* `bruhatBigCellBig σ g`: `g = u q` with `u ∈ U` and `q ∈ P`;
* `bruhatBigCellSmall σ g`: `g = s w_jL(c) q` with `j ∈ K`, `s ∈ S` and `q ∈ P`.

`bruhatBigCellBru σ g` is their union.

Proof route: left multiplication by each generator of `G_{K ∪ {L}}` preserves `Bru`.

* `x_ij` with `i, j ∈ K` (`bruhatBigCell_bru_S`): `S` normalizes `U`.
* `x_iL` (`bruhatBigCell_bru_U`): conjugate by `s` and then by `W = w_jL(c)`
  (`bruhatBigCell_w_inv_conj_U`).
* `x_Lb` (`bruhatBigCell_bru_V`).  Write `u = x_bL(d) u'` with `u' ∈ U_{≠b}` (`exists_split`).
  * If `d = 0`, then `u'⁻¹ x_Lb(a) u' ∈ C_b ⊆ P`.
  * If `d ≠ 0`, use the column identity: `x_bL(d) = x_Lb(d⁻¹) w_bL(d) x_Lb(d⁻¹)`.
    Then `w_bL(d) u' w_bL(d)⁻¹ ∈ S`, and we reach the row case.
* Row case (`bruhatBigCell_row_small`): `v₀ W q` with `v₀ ∈ V`.
  Write `v₀ = x_Lj(d) v'` with `v' ∈ V_{≠j}`, so `W⁻¹ v' W ∈ S`.
  * If `d = 0`, the product is small.
  * If `d ≠ 0`, the row identity `x_Lj(e) = x_jL(e⁻¹) w_jL(-e⁻¹) x_jL(e⁻¹)` together with
    `w(-e⁻¹) w(c) ∈ P` makes it big.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan exists_split)

variable {I R : Type*} [Fintype I] [DecidableEq I] [Field R]

/-- The big cell `U P`. -/
def bruhatBigCellBig (σ : BruhatBigCellData I R) (g : SteinbergGroup I R) : Prop :=
  ∃ u ∈ bruhatBigCellU R σ.K σ.L, ∃ q ∈ bruhatBigCellPar σ, g = u * q

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCellBig

/-- The small cells `S w_jL(c) P` with `j ∈ K`. -/
def bruhatBigCellSmall (σ : BruhatBigCellData I R) (g : SteinbergGroup I R) : Prop :=
  ∃ j : I, ∃ hj : j ∈ σ.K, ∃ c : Rˣ, ∃ s ∈ bruhatBigCellS R σ.K, ∃ q ∈ bruhatBigCellPar σ,
    g = s * w j σ.L (bruhatBigCell_ne σ.hLK hj) c * q

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCellSmall

/-- The union of the cells. -/
def bruhatBigCellBru (σ : BruhatBigCellData I R) (g : SteinbergGroup I R) : Prop :=
  bruhatBigCellBig σ g ∨ bruhatBigCellSmall σ g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCellBru

theorem bruhatBigCell_bru_congr (σ : BruhatBigCellData I R) {g g' : SteinbergGroup I R}
    (hg : bruhatBigCellBru σ g) (e : g = g') : bruhatBigCellBru σ g' := by
  subst e
  exact hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_bru_congr

/-- Left multiplication by `S` preserves the cells. -/
theorem bruhatBigCell_bru_S (σ : BruhatBigCellData I R) {y z : SteinbergGroup I R}
    (hy : y ∈ bruhatBigCellS R σ.K) (hz : bruhatBigCellBru σ z) :
    bruhatBigCellBru σ (y * z) := by
  rcases hz with ⟨u, hu, q, hq, rfl⟩ | ⟨j, hj, c, s, hs, q, hq, rfl⟩
  · exact Or.inl ⟨y * u * y⁻¹, bruhatBigCell_S_conj_U σ.hLK hy hu, y * q,
      Subgroup.mul_mem _ (bruhatBigCell_S_le_par σ hy) hq, by group⟩
  · exact Or.inr ⟨j, hj, c, y * s, Subgroup.mul_mem _ hy hs, q, hq, by group⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_bru_S

/-- Left multiplication by `U` preserves the cells. -/
theorem bruhatBigCell_bru_U (σ : BruhatBigCellData I R) {y z : SteinbergGroup I R}
    (hy : y ∈ bruhatBigCellU R σ.K σ.L) (hz : bruhatBigCellBru σ z) :
    bruhatBigCellBru σ (y * z) := by
  rcases hz with ⟨u, hu, q, hq, rfl⟩ | ⟨j, hj, c, s, hs, q, hq, rfl⟩
  · exact Or.inl ⟨y * u, Subgroup.mul_mem _ hy hu, q, hq, by group⟩
  · have hu := bruhatBigCell_S_conj_U σ.hLK (Subgroup.inv_mem _ hs) hy
    rw [inv_inv] at hu
    exact Or.inr ⟨j, hj, c, s, hs, _,
      Subgroup.mul_mem _ (bruhatBigCell_w_inv_conj_U σ hj c hu) hq, by group⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_bru_U

/-- Row case: `v₀ w_jL(c) q` lies in a cell when `v₀ ∈ V` and `q ∈ P`. -/
theorem bruhatBigCell_row_small (σ : BruhatBigCellData I R) {v₀ q : SteinbergGroup I R}
    (hv : v₀ ∈ bruhatBigCellV R σ.K σ.L) {j : I} (hj : j ∈ σ.K) (c : Rˣ)
    (hq : q ∈ bruhatBigCellPar σ) :
    bruhatBigCellBru σ (v₀ * w j σ.L (bruhatBigCell_ne σ.hLK hj) c * q) := by
  have hsplit : ∀ i l : I, i ≠ l → (i = σ.L ∧ l ∈ σ.K) →
      (i = σ.L ∧ l = j) ∨ (i = σ.L ∧ l ∈ σ.K ∧ l ≠ j) := by
    intro i l _ hp
    by_cases hlj : l = j
    · exact Or.inl ⟨hp.1, hlj⟩
    · exact Or.inr ⟨hp.1, hp.2, hlj⟩
  have hcomm : ∀ (i l : I) (hil : i ≠ l) (a b : R), (i = σ.L ∧ l ∈ σ.K ∧ l ≠ j) →
      Commute (x σ.L j (bruhatBigCell_ne σ.hLK hj).symm b) (x i l hil a) := by
    intro i l hil a b hp
    obtain ⟨hi, _⟩ := hp
    subst i
    exact x_commute_of_ne σ.L j σ.L l (bruhatBigCell_ne σ.hLK hj).symm hil
      (bruhatBigCell_ne σ.hLK hj) hil.symm b a
  obtain ⟨d, v', hv', rfl⟩ := exists_split (p := fun i l => i = σ.L ∧ l ∈ σ.K)
    (q := fun i l => i = σ.L ∧ l ∈ σ.K ∧ l ≠ j) (bruhatBigCell_ne σ.hLK hj).symm hsplit hcomm
    hv
  have hq₁ := Subgroup.mul_mem _
    (bruhatBigCell_S_le_par σ (bruhatBigCell_w_inv_conj_Vex σ hj c hv')) hq
  by_cases hd : d = 0
  · subst hd
    rw [x_zero, one_mul]
    exact Or.inr ⟨j, hj, c, 1, Subgroup.one_mem _, _, hq₁, by group⟩
  · obtain ⟨e, rfl⟩ : ∃ e : Rˣ, (e : R) = d := ⟨Units.mk0 d hd, Units.val_mk0 hd⟩
    rw [bruhatBigCell_row_id j σ.L (bruhatBigCell_ne σ.hLK hj) e]
    exact Or.inl ⟨x j σ.L (bruhatBigCell_ne σ.hLK hj) ((e⁻¹ : Rˣ) : R),
      bruhatBigCell_x_mem_U _ _ hj, _,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (bruhatBigCell_ww_mem σ hj (-e⁻¹) c)
        (bruhatBigCell_w_inv_conj_U σ hj c
          (bruhatBigCell_x_mem_U (bruhatBigCell_ne σ.hLK hj) ((e⁻¹ : Rˣ) : R) hj))) hq₁,
      by group⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_row_small

/-- Left multiplication by a row root `x_Lb(a)` with `b ∈ K` preserves the cells. -/
theorem bruhatBigCell_bru_V (σ : BruhatBigCellData I R) {b : I} (hb : b ∈ σ.K) (a : R)
    {z : SteinbergGroup I R} (hz : bruhatBigCellBru σ z) :
    bruhatBigCellBru σ (x σ.L b (bruhatBigCell_ne σ.hLK hb).symm a * z) := by
  rcases hz with ⟨u, hu, q, hq, rfl⟩ | ⟨j, hj, c, s, hs, q, hq, rfl⟩
  · have hsplit : ∀ i l : I, i ≠ l → (l = σ.L ∧ i ∈ σ.K) →
        (i = b ∧ l = σ.L) ∨ (l = σ.L ∧ i ∈ σ.K ∧ i ≠ b) := by
      intro i l _ hp
      by_cases hib : i = b
      · exact Or.inl ⟨hib, hp.1⟩
      · exact Or.inr ⟨hp.1, hp.2, hib⟩
    have hcomm : ∀ (i l : I) (hil : i ≠ l) (a' b' : R), (l = σ.L ∧ i ∈ σ.K ∧ i ≠ b) →
        Commute (x b σ.L (bruhatBigCell_ne σ.hLK hb) b') (x i l hil a') := by
      intro i l hil a' b' hp
      obtain ⟨hl, _⟩ := hp
      subst l
      exact x_commute_of_ne b σ.L i σ.L (bruhatBigCell_ne σ.hLK hb) hil hil.symm
        (bruhatBigCell_ne σ.hLK hb).symm b' a'
    obtain ⟨d, u', hu', rfl⟩ := exists_split (p := fun i l => l = σ.L ∧ i ∈ σ.K)
      (q := fun i l => l = σ.L ∧ i ∈ σ.K ∧ i ≠ b) (bruhatBigCell_ne σ.hLK hb) hsplit hcomm hu
    by_cases hd : d = 0
    · subst hd
      rw [x_zero, one_mul]
      have hC := bruhatBigCell_Uex_conj_C (Subgroup.inv_mem _ hu')
        (bruhatBigCell_x_mem_C (bruhatBigCell_ne σ.hLK hb).symm a
          (Finset.mem_insert_self σ.L σ.K))
      rw [inv_inv] at hC
      exact Or.inl ⟨u', bruhatBigCell_Uex_le_U hu', _,
        Subgroup.mul_mem _ (bruhatBigCell_C_le_par σ hb hC) hq, by group⟩
    · obtain ⟨dd, rfl⟩ : ∃ dd : Rˣ, (dd : R) = d := ⟨Units.mk0 d hd, Units.val_mk0 hd⟩
      obtain ⟨k, hbk, hLk⟩ := σ.third b σ.L
      rw [bruhatBigCell_col_id b σ.L k (bruhatBigCell_ne σ.hLK hb) hbk hLk dd]
      have hs₁ := bruhatBigCell_w_conj_Uex σ hb dd hu'
      have hC := bruhatBigCell_Uex_conj_C (Subgroup.inv_mem _ hu')
        (bruhatBigCell_x_mem_C (bruhatBigCell_ne σ.hLK hb).symm ((dd⁻¹ : Rˣ) : R)
          (Finset.mem_insert_self σ.L σ.K))
      rw [inv_inv] at hC
      have hq₁ := Subgroup.mul_mem _ (bruhatBigCell_C_le_par σ hb hC) hq
      have hv₀ := bruhatBigCell_S_conj_V σ.hLK (Subgroup.inv_mem _ hs₁)
        (bruhatBigCell_x_mem_V (bruhatBigCell_ne σ.hLK hb).symm (a + ((dd⁻¹ : Rˣ) : R)) hb)
      rw [inv_inv] at hv₀
      refine bruhatBigCell_bru_congr σ
        (bruhatBigCell_bru_S σ hs₁ (bruhatBigCell_row_small σ hv₀ hb dd hq₁)) ?_
      rw [← x_mul]
      group
  · have hv := bruhatBigCell_S_conj_V σ.hLK (Subgroup.inv_mem _ hs)
      (bruhatBigCell_x_mem_V (bruhatBigCell_ne σ.hLK hb).symm a hb)
    rw [inv_inv] at hv
    refine bruhatBigCell_bru_congr σ
      (bruhatBigCell_bru_S σ hs (bruhatBigCell_row_small σ hv hj c hq)) ?_
    group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_bru_V

end GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2
