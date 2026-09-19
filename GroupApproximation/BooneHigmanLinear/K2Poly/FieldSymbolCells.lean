import GroupApproximation.BooneHigmanLinear.K2Poly.FieldSymbolPar
import GroupApproximation.Meta.AxiomGuard

/-!
# Symbols generate `K₂` of a field, part 2: the cells `U P ∪ S W P`

k2-poly piece A5.1 (lane bh-pal-wire). This is `ElemFPFieldK2BruhatBigCellWeyl` and
`ElemFPFieldK2BruhatBigCellCells` (lane bh-met-64c) with the parabolic `P` replaced by the
symbol-twisted `fsgPar F σ` of `FieldSymbolPar`. The proofs are unchanged: they use `P` only
as a subgroup containing `S`, `V`, the tori `h_bL` (`b ∈ K`) and the column spans `C_b`.

* Weyl conjugations `w_jL(c) U w_jL(c)⁻¹ ⊆ P`, `w_jL(c) V_{≠j} w_jL(c)⁻¹ ⊆ S`, and
  `w(u₁) w(u₂) ∈ P`.
* The cells: `fsgBig` is `U P`, `fsgSmall` is `S w_jL(c) P` with `j ∈ K`, and `fsgBru` is their
  union. Left multiplication by `S` (`fsg_bru_S`), by `U` (`fsg_bru_U`) and by each row root
  `x_Lb` (`fsg_bru_V`) preserves `fsgBru`.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h w_conj_x_row_j
  w_conj_x_col_j)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan
  rootSpan_conj_mem exists_split)

variable {I : Type} [Fintype I] [DecidableEq I] {F : Type} [Field F]

/-- `w_jL(c) U w_jL(c)⁻¹ ⊆ P`. -/
theorem fsg_w_conj_U (σ : FsgData I) {j : I} (hj : j ∈ σ.K) (c : Fˣ)
    {u : SteinbergGroup I F} (hu : u ∈ bruhatBigCellU F σ.K σ.L) :
    w j σ.L (bruhatBigCell_ne σ.hLK hj) c * u * (w j σ.L (bruhatBigCell_ne σ.hLK hj) c)⁻¹ ∈
      fsgPar F σ := by
  refine rootSpan_conj_mem (p := fun i l => l = σ.L ∧ i ∈ σ.K) ?_ hu
  intro i l hil t hp
  obtain ⟨hl, hi⟩ := hp
  subst l
  by_cases hij : i = j
  · subst i
    obtain ⟨k, hjk, hLk⟩ := σ.third j σ.L
    rw [w_conj_x_self j σ.L k (bruhatBigCell_ne σ.hLK hj) hjk hLk c t]
    exact fsg_V_le_par σ (bruhatBigCell_x_mem_V _ _ hj)
  · rw [w_conj_x_col_j j σ.L i (bruhatBigCell_ne σ.hLK hj) hij hil c t]
    exact fsg_S_le_par σ (bruhatBigCell_x_mem_S hij _ hi hj)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fsg_w_conj_U

/-- `w_jL(c)⁻¹ U w_jL(c) ⊆ P`. -/
theorem fsg_w_inv_conj_U (σ : FsgData I) {j : I} (hj : j ∈ σ.K) (c : Fˣ)
    {u : SteinbergGroup I F} (hu : u ∈ bruhatBigCellU F σ.K σ.L) :
    (w j σ.L (bruhatBigCell_ne σ.hLK hj) c)⁻¹ * u * w j σ.L (bruhatBigCell_ne σ.hLK hj) c ∈
      fsgPar F σ := by
  rw [bruhatBigCell_w_inv_conj]
  exact fsg_w_conj_U σ hj (-c) hu

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fsg_w_inv_conj_U

/-- `w_bL(c) U_{≠b} w_bL(c)⁻¹ ⊆ S`. -/
theorem fsg_w_conj_Uex (σ : FsgData I) {b : I} (hb : b ∈ σ.K) (c : Fˣ)
    {u : SteinbergGroup I F} (hu : u ∈ bruhatBigCellUex F σ.K σ.L b) :
    w b σ.L (bruhatBigCell_ne σ.hLK hb) c * u * (w b σ.L (bruhatBigCell_ne σ.hLK hb) c)⁻¹ ∈
      bruhatBigCellS F σ.K := by
  refine rootSpan_conj_mem (p := fun i l => l = σ.L ∧ i ∈ σ.K ∧ i ≠ b) ?_ hu
  intro i l hil t hp
  obtain ⟨hl, hi, hib⟩ := hp
  subst l
  rw [w_conj_x_col_j b σ.L i (bruhatBigCell_ne σ.hLK hb) hib hil c t]
  exact bruhatBigCell_x_mem_S hib _ hi hb

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fsg_w_conj_Uex

/-- `w_jL(c)⁻¹ V_{≠j} w_jL(c) ⊆ S`. -/
theorem fsg_w_inv_conj_Vex (σ : FsgData I) {j : I} (hj : j ∈ σ.K) (c : Fˣ)
    {v : SteinbergGroup I F} (hv : v ∈ bruhatBigCellVex F σ.K σ.L j) :
    (w j σ.L (bruhatBigCell_ne σ.hLK hj) c)⁻¹ * v * w j σ.L (bruhatBigCell_ne σ.hLK hj) c ∈
      bruhatBigCellS F σ.K := by
  rw [bruhatBigCell_w_inv_conj]
  refine rootSpan_conj_mem (p := fun i l => i = σ.L ∧ l ∈ σ.K ∧ l ≠ j) ?_ hv
  intro i l hil t hp
  obtain ⟨hi, hl, hlj⟩ := hp
  subst i
  rw [w_conj_x_row_j j σ.L l (bruhatBigCell_ne σ.hLK hj) (Ne.symm hlj) hil (-c) t]
  exact bruhatBigCell_x_mem_S (Ne.symm hlj) _ hj hl

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fsg_w_inv_conj_Vex

/-- `w_jL(u₁) w_jL(u₂) ∈ P` for `j ∈ K`. -/
theorem fsg_ww_mem (σ : FsgData I) {j : I} (hj : j ∈ σ.K) (u₁ u₂ : Fˣ) :
    w j σ.L (bruhatBigCell_ne σ.hLK hj) u₁ * w j σ.L (bruhatBigCell_ne σ.hLK hj) u₂ ∈
      fsgPar F σ := by
  rw [bruhatBigCell_ww_eq]
  exact Subgroup.mul_mem _ (fsg_hb_mem_par σ hj u₁)
    (Subgroup.inv_mem _ (fsg_hb_mem_par σ hj (-u₂)))

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fsg_ww_mem

/-- The big cell `U P`. -/
def fsgBig (σ : FsgData I) (g : SteinbergGroup I F) : Prop :=
  ∃ u ∈ bruhatBigCellU F σ.K σ.L, ∃ q ∈ fsgPar F σ, g = u * q

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fsgBig

/-- The small cells `S w_jL(c) P` with `j ∈ K`. -/
def fsgSmall (σ : FsgData I) (g : SteinbergGroup I F) : Prop :=
  ∃ j : I, ∃ hj : j ∈ σ.K, ∃ c : Fˣ, ∃ s ∈ bruhatBigCellS F σ.K, ∃ q ∈ fsgPar F σ,
    g = s * w j σ.L (bruhatBigCell_ne σ.hLK hj) c * q

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fsgSmall

/-- The union of the cells. -/
def fsgBru (σ : FsgData I) (g : SteinbergGroup I F) : Prop :=
  fsgBig σ g ∨ fsgSmall σ g

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fsgBru

theorem fsg_bru_congr (σ : FsgData I) {g g' : SteinbergGroup I F} (hg : fsgBru σ g)
    (e : g = g') : fsgBru σ g' := by
  subst e
  exact hg

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fsg_bru_congr

/-- Left multiplication by `S` preserves the cells. -/
theorem fsg_bru_S (σ : FsgData I) {y z : SteinbergGroup I F}
    (hy : y ∈ bruhatBigCellS F σ.K) (hz : fsgBru σ z) : fsgBru σ (y * z) := by
  rcases hz with ⟨u, hu, q, hq, rfl⟩ | ⟨j, hj, c, s, hs, q, hq, rfl⟩
  · exact Or.inl ⟨y * u * y⁻¹, bruhatBigCell_S_conj_U σ.hLK hy hu, y * q,
      Subgroup.mul_mem _ (fsg_S_le_par σ hy) hq, by group⟩
  · exact Or.inr ⟨j, hj, c, y * s, Subgroup.mul_mem _ hy hs, q, hq, by group⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fsg_bru_S

/-- Left multiplication by `U` preserves the cells. -/
theorem fsg_bru_U (σ : FsgData I) {y z : SteinbergGroup I F}
    (hy : y ∈ bruhatBigCellU F σ.K σ.L) (hz : fsgBru σ z) : fsgBru σ (y * z) := by
  rcases hz with ⟨u, hu, q, hq, rfl⟩ | ⟨j, hj, c, s, hs, q, hq, rfl⟩
  · exact Or.inl ⟨y * u, Subgroup.mul_mem _ hy hu, q, hq, by group⟩
  · have hu := bruhatBigCell_S_conj_U σ.hLK (Subgroup.inv_mem _ hs) hy
    rw [inv_inv] at hu
    exact Or.inr ⟨j, hj, c, s, hs, _,
      Subgroup.mul_mem _ (fsg_w_inv_conj_U σ hj c hu) hq, by group⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fsg_bru_U

/-- Row case: `v₀ w_jL(c) q` lies in a cell when `v₀ ∈ V` and `q ∈ P`. -/
theorem fsg_row_small (σ : FsgData I) {v₀ q : SteinbergGroup I F}
    (hv : v₀ ∈ bruhatBigCellV F σ.K σ.L) {j : I} (hj : j ∈ σ.K) (c : Fˣ)
    (hq : q ∈ fsgPar F σ) :
    fsgBru σ (v₀ * w j σ.L (bruhatBigCell_ne σ.hLK hj) c * q) := by
  have hsplit : ∀ i l : I, i ≠ l → (i = σ.L ∧ l ∈ σ.K) →
      (i = σ.L ∧ l = j) ∨ (i = σ.L ∧ l ∈ σ.K ∧ l ≠ j) := by
    intro i l _ hp
    by_cases hlj : l = j
    · exact Or.inl ⟨hp.1, hlj⟩
    · exact Or.inr ⟨hp.1, hp.2, hlj⟩
  have hcomm : ∀ (i l : I) (hil : i ≠ l) (a b : F), (i = σ.L ∧ l ∈ σ.K ∧ l ≠ j) →
      Commute (x σ.L j (bruhatBigCell_ne σ.hLK hj).symm b) (x i l hil a) := by
    intro i l hil a b hp
    obtain ⟨hi, _⟩ := hp
    subst i
    exact x_commute_of_ne σ.L j σ.L l (bruhatBigCell_ne σ.hLK hj).symm hil
      (bruhatBigCell_ne σ.hLK hj) hil.symm b a
  obtain ⟨d, v', hv', rfl⟩ := exists_split (p := fun i l => i = σ.L ∧ l ∈ σ.K)
    (q := fun i l => i = σ.L ∧ l ∈ σ.K ∧ l ≠ j) (bruhatBigCell_ne σ.hLK hj).symm hsplit hcomm
    hv
  have hq₁ := Subgroup.mul_mem _ (fsg_S_le_par σ (fsg_w_inv_conj_Vex σ hj c hv')) hq
  by_cases hd : d = 0
  · subst hd
    rw [x_zero, one_mul]
    exact Or.inr ⟨j, hj, c, 1, Subgroup.one_mem _, _, hq₁, by group⟩
  · obtain ⟨e, rfl⟩ : ∃ e : Fˣ, (e : F) = d := ⟨Units.mk0 d hd, Units.val_mk0 hd⟩
    rw [bruhatBigCell_row_id j σ.L (bruhatBigCell_ne σ.hLK hj) e]
    exact Or.inl ⟨x j σ.L (bruhatBigCell_ne σ.hLK hj) ((e⁻¹ : Fˣ) : F),
      bruhatBigCell_x_mem_U _ _ hj, _,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (fsg_ww_mem σ hj (-e⁻¹) c)
        (fsg_w_inv_conj_U σ hj c
          (bruhatBigCell_x_mem_U (bruhatBigCell_ne σ.hLK hj) ((e⁻¹ : Fˣ) : F) hj))) hq₁,
      by group⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fsg_row_small

/-- Left multiplication by a row root `x_Lb(a)` with `b ∈ K` preserves the cells. -/
theorem fsg_bru_V (σ : FsgData I) {b : I} (hb : b ∈ σ.K) (a : F) {z : SteinbergGroup I F}
    (hz : fsgBru σ z) : fsgBru σ (x σ.L b (bruhatBigCell_ne σ.hLK hb).symm a * z) := by
  rcases hz with ⟨u, hu, q, hq, rfl⟩ | ⟨j, hj, c, s, hs, q, hq, rfl⟩
  · have hsplit : ∀ i l : I, i ≠ l → (l = σ.L ∧ i ∈ σ.K) →
        (i = b ∧ l = σ.L) ∨ (l = σ.L ∧ i ∈ σ.K ∧ i ≠ b) := by
      intro i l _ hp
      by_cases hib : i = b
      · exact Or.inl ⟨hib, hp.1⟩
      · exact Or.inr ⟨hp.1, hp.2, hib⟩
    have hcomm : ∀ (i l : I) (hil : i ≠ l) (a' b' : F), (l = σ.L ∧ i ∈ σ.K ∧ i ≠ b) →
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
        Subgroup.mul_mem _ (fsg_C_le_par σ hb hC) hq, by group⟩
    · obtain ⟨dd, rfl⟩ : ∃ dd : Fˣ, (dd : F) = d := ⟨Units.mk0 d hd, Units.val_mk0 hd⟩
      obtain ⟨k, hbk, hLk⟩ := σ.third b σ.L
      rw [bruhatBigCell_col_id b σ.L k (bruhatBigCell_ne σ.hLK hb) hbk hLk dd]
      have hs₁ := fsg_w_conj_Uex σ hb dd hu'
      have hC := bruhatBigCell_Uex_conj_C (Subgroup.inv_mem _ hu')
        (bruhatBigCell_x_mem_C (bruhatBigCell_ne σ.hLK hb).symm ((dd⁻¹ : Fˣ) : F)
          (Finset.mem_insert_self σ.L σ.K))
      rw [inv_inv] at hC
      have hq₁ := Subgroup.mul_mem _ (fsg_C_le_par σ hb hC) hq
      have hv₀ := bruhatBigCell_S_conj_V σ.hLK (Subgroup.inv_mem _ hs₁)
        (bruhatBigCell_x_mem_V (bruhatBigCell_ne σ.hLK hb).symm (a + ((dd⁻¹ : Fˣ) : F)) hb)
      rw [inv_inv] at hv₀
      refine fsg_bru_congr σ (fsg_bru_S σ hs₁ (fsg_row_small σ hv₀ hb dd hq₁)) ?_
      rw [← x_mul]
      group
  · have hv := bruhatBigCell_S_conj_V σ.hLK (Subgroup.inv_mem _ hs)
      (bruhatBigCell_x_mem_V (bruhatBigCell_ne σ.hLK hb).symm a hb)
    rw [inv_inv] at hv
    refine fsg_bru_congr σ (fsg_bru_S σ hs (fsg_row_small σ hv hj c hq)) ?_
    group

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fsg_bru_V

end GroupApproximation.BooneHigmanLinear.K2Poly
