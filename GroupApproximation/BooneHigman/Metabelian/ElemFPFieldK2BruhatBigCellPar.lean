import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2BruhatBigCellTorus
import GroupApproximation.Meta.AxiomGuard

/-!
# Big Bruhat cell, part 3: the parabolic subgroup `P = S · V · T`

Lane `bh-met-64c`.  Here `bruhatBigCellPar σ` is the set of products `s v h_mL(c)` with
`s ∈ S = G_K`, `v ∈ V = ⟨x_Lj : j ∈ K⟩` and `c` a unit.

Proof route:

* It is a subgroup: `S` normalizes `V` (`bruhatBigCell_S_conj_V`), `h_mL(c)` normalizes both
  (`bruhatBigCell_h_conj_S`, `bruhatBigCell_h_conj_V`), and the torus law holds
  (`σ.torus`, `bruhatBigCell_h_inv`).  The group identities are closed by `group`.
* It contains `S`, `V`, every `h_mL(c)`, and every `h_bL(c)` with `b ∈ K`
  (`bruhatBigCell_h_first` conjugates `h_mL` to `h_bL` by `w_bm(1) ∈ S`).
* It contains the column span `C_b` for `b ∈ K`: the roots `x_Lb` lie in `V`, and the roots
  `x_kb` with `k ∈ K` lie in `S`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan
  rootSpan_induction rootSpan_mono)

variable {I R : Type*} [Fintype I] [DecidableEq I] [Field R]

/-- Products of two elements of the form `s v h(c)` have the same form. -/
theorem bruhatBigCell_par_mul (σ : BruhatBigCellData I R) {s v s' v' : SteinbergGroup I R}
    (hs : s ∈ bruhatBigCellS R σ.K) (hv : v ∈ bruhatBigCellV R σ.K σ.L)
    (hs' : s' ∈ bruhatBigCellS R σ.K) (hv' : v' ∈ bruhatBigCellV R σ.K σ.L) (c c' : Rˣ) :
    ∃ s₂ ∈ bruhatBigCellS R σ.K, ∃ v₂ ∈ bruhatBigCellV R σ.K σ.L, ∃ c₂ : Rˣ,
      s * v * h σ.m σ.L σ.hmL c * (s' * v' * h σ.m σ.L σ.hmL c') =
        s₂ * v₂ * h σ.m σ.L σ.hmL c₂ := by
  have ht := bruhatBigCell_h_conj_S σ c hs'
  have hv₁ := bruhatBigCell_S_conj_V σ.hLK (Subgroup.inv_mem _ ht) hv
  rw [inv_inv] at hv₁
  have hv₃ := bruhatBigCell_h_conj_V σ c hv'
  refine ⟨s * (h σ.m σ.L σ.hmL c * s' * (h σ.m σ.L σ.hmL c)⁻¹), Subgroup.mul_mem _ hs ht,
    (h σ.m σ.L σ.hmL c * s' * (h σ.m σ.L σ.hmL c)⁻¹)⁻¹ * v *
      (h σ.m σ.L σ.hmL c * s' * (h σ.m σ.L σ.hmL c)⁻¹) *
      (h σ.m σ.L σ.hmL c * v' * (h σ.m σ.L σ.hmL c)⁻¹), Subgroup.mul_mem _ hv₁ hv₃,
    c' * c, ?_⟩
  rw [← σ.torus c c']
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_par_mul

/-- The inverse of an element of the form `s v h(c)` has the same form. -/
theorem bruhatBigCell_par_inv (σ : BruhatBigCellData I R) {s v : SteinbergGroup I R}
    (hs : s ∈ bruhatBigCellS R σ.K) (hv : v ∈ bruhatBigCellV R σ.K σ.L) (c : Rˣ) :
    ∃ s₂ ∈ bruhatBigCellS R σ.K, ∃ v₂ ∈ bruhatBigCellV R σ.K σ.L, ∃ c₂ : Rˣ,
      (s * v * h σ.m σ.L σ.hmL c)⁻¹ = s₂ * v₂ * h σ.m σ.L σ.hmL c₂ := by
  have hs₂ := bruhatBigCell_h_conj_S σ c⁻¹ (Subgroup.inv_mem _ hs)
  have hv₂ := bruhatBigCell_S_conj_V σ.hLK (Subgroup.inv_mem _ hs₂)
    (bruhatBigCell_h_conj_V σ c⁻¹ (Subgroup.inv_mem _ hv))
  rw [inv_inv] at hv₂
  refine ⟨_, hs₂, _, hv₂, c⁻¹, ?_⟩
  rw [← bruhatBigCell_h_inv σ c]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_par_inv

/-- The parabolic subgroup `P = S · V · T`. -/
def bruhatBigCellPar (σ : BruhatBigCellData I R) : Subgroup (SteinbergGroup I R) where
  carrier := {g | ∃ s ∈ bruhatBigCellS R σ.K, ∃ v ∈ bruhatBigCellV R σ.K σ.L, ∃ c : Rˣ,
    g = s * v * h σ.m σ.L σ.hmL c}
  mul_mem' := by
    rintro _ _ ⟨s, hs, v, hv, c, rfl⟩ ⟨s', hs', v', hv', c', rfl⟩
    exact bruhatBigCell_par_mul σ hs hv hs' hv' c c'
  one_mem' := ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, 1, by
    simp only [bruhat_h_one, mul_one]⟩
  inv_mem' := by
    rintro _ ⟨s, hs, v, hv, c, rfl⟩
    exact bruhatBigCell_par_inv σ hs hv c

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCellPar

theorem bruhatBigCell_mem_par (σ : BruhatBigCellData I R) {g : SteinbergGroup I R} :
    g ∈ bruhatBigCellPar σ ↔ ∃ s ∈ bruhatBigCellS R σ.K, ∃ v ∈ bruhatBigCellV R σ.K σ.L,
      ∃ c : Rˣ, g = s * v * h σ.m σ.L σ.hmL c :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_mem_par

theorem bruhatBigCell_S_le_par (σ : BruhatBigCellData I R) {s : SteinbergGroup I R}
    (hs : s ∈ bruhatBigCellS R σ.K) : s ∈ bruhatBigCellPar σ :=
  ⟨s, hs, 1, Subgroup.one_mem _, 1, by simp only [bruhat_h_one, mul_one]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_S_le_par

theorem bruhatBigCell_V_le_par (σ : BruhatBigCellData I R) {v : SteinbergGroup I R}
    (hv : v ∈ bruhatBigCellV R σ.K σ.L) : v ∈ bruhatBigCellPar σ :=
  ⟨1, Subgroup.one_mem _, v, hv, 1, by simp only [bruhat_h_one, one_mul, mul_one]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_V_le_par

theorem bruhatBigCell_h_mem_par (σ : BruhatBigCellData I R) (c : Rˣ) :
    h σ.m σ.L σ.hmL c ∈ bruhatBigCellPar σ :=
  ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, c, by simp only [one_mul]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_h_mem_par

/-- `h_bL(c) ∈ P` for every `b ∈ K`. -/
theorem bruhatBigCell_hb_mem_par (σ : BruhatBigCellData I R) {b : I} (hb : b ∈ σ.K)
    (c : Rˣ) : h b σ.L (bruhatBigCell_ne σ.hLK hb) c ∈ bruhatBigCellPar σ := by
  by_cases hbm : b = σ.m
  · subst b
    exact bruhatBigCell_h_mem_par σ c
  · have hbL := bruhatBigCell_ne σ.hLK hb
    rw [← bruhatBigCell_h_first b σ.m σ.L hbm hbL σ.hmL c]
    have hW := bruhatBigCell_S_le_par σ (bruhatBigCell_w_mem_S hbm (1 : Rˣ) hb σ.hmK)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hW (bruhatBigCell_h_mem_par σ c))
      (Subgroup.inv_mem _ hW)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_hb_mem_par

/-- The column span `C_b` lies in `P` for `b ∈ K`. -/
theorem bruhatBigCell_C_le_par (σ : BruhatBigCellData I R) {b : I} (hb : b ∈ σ.K)
    {g : SteinbergGroup I R} (hg : g ∈ bruhatBigCellC R σ.K σ.L b) :
    g ∈ bruhatBigCellPar σ := by
  refine rootSpan_induction (p := fun i j => j = b ∧ i ∈ insert σ.L σ.K)
    (Q := fun g => g ∈ bruhatBigCellPar σ) ?_ (Subgroup.one_mem _) ?_ hg
  · intro i j hij a hp
    obtain ⟨hjb, hi⟩ := hp
    subst j
    rcases Finset.mem_insert.mp hi with hiL | hiK
    · subst i
      exact bruhatBigCell_V_le_par σ (bruhatBigCell_x_mem_V hij a hb)
    · exact bruhatBigCell_S_le_par σ (bruhatBigCell_x_mem_S hij a hiK hb)
  · intro g k _ _ hg hk
    exact Subgroup.mul_mem _ hg hk

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_C_le_par

theorem bruhatBigCell_Uex_le_U {K : Finset I} {L b : I} {u : SteinbergGroup I R}
    (hu : u ∈ bruhatBigCellUex R K L b) : u ∈ bruhatBigCellU R K L :=
  rootSpan_mono (p := fun i j => j = L ∧ i ∈ K ∧ i ≠ b) (q := fun i j => j = L ∧ i ∈ K)
    (fun _ _ _ hp => ⟨hp.1, hp.2.1⟩) hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_Uex_le_U

theorem bruhatBigCell_Vex_le_V {K : Finset I} {L j₀ : I} {v : SteinbergGroup I R}
    (hv : v ∈ bruhatBigCellVex R K L j₀) : v ∈ bruhatBigCellV R K L :=
  rootSpan_mono (p := fun i j => i = L ∧ j ∈ K ∧ j ≠ j₀) (q := fun i j => i = L ∧ j ∈ K)
    (fun _ _ _ hp => ⟨hp.1, hp.2.1⟩) hv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhatBigCell_Vex_le_V

end GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2
