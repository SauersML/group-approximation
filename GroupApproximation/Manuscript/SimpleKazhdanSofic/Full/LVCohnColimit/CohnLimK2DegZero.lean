import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnDegZero.StageHom
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Ultramatricial
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFieldK2.FieldK2
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStableK2.Reduction
import GroupApproximation.Meta.AxiomGuard

/-!
# The degree-zero part `C₀` of `C_2(𝔽₂)` has stable `K₂ = 0` (lane sk-lv-01)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii: "stable `K₂` of the
Cohn algebra vanishes" (Ara–Brustenga–Cortiñas, Münster J. Math. 2 (2009), Thm 3.6; Sec. 5 for
the degree-zero part).  The degree-zero part `C₀ = LVCohnDegZero.cohnDegreeZero` is the increasing
union of the stages `stage n ≅ ∏_{j ≤ n} M_{2^j}(𝔽₂)` (`LVCohnDegZero.stageEquiv`).  So `C₀` is
ultramatricial over `𝔽₂`, and it has stable `K₂ = 0` by the ultramatricial toolkit.

Route:
* `skCohnLimK2_exists_stage_of_mem`: every element of `C₀` lies in one stage.  The generators
  `x_μ y_ν` (`|μ| = |ν|`) lie in `stage |μ|`, and the stages increase (`stage_mono`).
* `skCohnLimK2_isUltramatricialF2_degreeZero`: `C₀` is ultramatricial over `𝔽₂`.
* `skCohnLimK2_stableK2Trivial_degreeZero`: stable `K₂(C₀) = 0`.
* `skCohnLimK2_degreeZeroSurjStatement`: stable surjectivity of `K₂(C₀) → K₂(C)`, the
  Mayer–Vietoris / Yao core of ABC Thm 3.6 (it uses `K₁(C₀) = 0`).  This is the residual.
  It has strictly smaller proof content than `StableK2Trivial CohnTwoF2`, because the part
  `K₂(C₀) = 0` is discharged here.  LOUD: it is still logically equivalent to it (both are
  true; see `skCohnLimK2_degreeZeroSurj_of_cohn_stableK2Trivial` for the converse).
* `skCohnLimK2_cohn_stableK2Trivial_of_degreeZeroSurj`: the reduction.
-/

namespace GroupApproximation.Full.LVCohnColimit

noncomputable section

/-- The stages `stage n ⊆ C₀` form an increasing chain.  (ABC 2009 Sec. 5;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnLimK2_stage_monotone : Monotone LVCohnDegZero.stage :=
  monotone_nat_of_le_succ LVCohnDegZero.stage_mono

#audit_axioms GroupApproximation.Full.LVCohnColimit.skCohnLimK2_stage_monotone

/-- The union of the stages is the supremum `⨆ n, stage n`, since they are directed.  (ABC 2009
Sec. 5; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnLimK2_mem_iSup_stage {x : LVCohnRelK1.CohnTwoF2} :
    x ∈ ⨆ n, LVCohnDegZero.stage n ↔ ∃ n, x ∈ LVCohnDegZero.stage n :=
  Subring.mem_iSup_of_directed skCohnLimK2_stage_monotone.directed_le

#audit_axioms GroupApproximation.Full.LVCohnColimit.skCohnLimK2_mem_iSup_stage

/-- `C₀` lies in the union of the stages: the generators `x_μ y_ν` with `|μ| = |ν|` lie in
`stage |μ|`.  (ABC 2009 Sec. 5; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnLimK2_cohnDegreeZero_le_iSup :
    LVCohnDegZero.cohnDegreeZero ≤ ⨆ n, LVCohnDegZero.stage n := by
  rw [LVCohnDegZero.cohnDegreeZero, Subring.closure_le]
  rintro a ⟨mu, nu, h, rfl⟩
  rw [SetLike.mem_coe, skCohnLimK2_mem_iSup_stage]
  refine ⟨mu.length, ?_⟩
  rw [LVCohnDegZero.cxWord_eq_xw, LVCohnDegZero.cyWord_eq_yw]
  exact LVCohnDegZero.xw_mul_yw_mem_stage _ mu nu rfl h.symm

#audit_axioms GroupApproximation.Full.LVCohnColimit.skCohnLimK2_cohnDegreeZero_le_iSup

/-- Every element of `C₀` lies in some stage.  (ABC 2009 Sec. 5;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnLimK2_exists_stage_of_mem {x : LVCohnRelK1.CohnTwoF2}
    (hx : x ∈ LVCohnDegZero.cohnDegreeZero) : ∃ n, x ∈ LVCohnDegZero.stage n :=
  skCohnLimK2_mem_iSup_stage.mp (skCohnLimK2_cohnDegreeZero_le_iSup hx)

#audit_axioms GroupApproximation.Full.LVCohnColimit.skCohnLimK2_exists_stage_of_mem

/-- Every finite subset of `C₀` lies in one stage.  (ABC 2009 Sec. 5;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnLimK2_exists_stage (s : Finset LVCohnDegZero.cohnDegreeZero) :
    ∃ n, ∀ x ∈ s, (x : LVCohnRelK1.CohnTwoF2) ∈ LVCohnDegZero.stage n := by
  choose ix hx using fun x : LVCohnDegZero.cohnDegreeZero => skCohnLimK2_exists_stage_of_mem x.2
  exact ⟨s.sup ix, fun x hxs => skCohnLimK2_stage_monotone (Finset.le_sup hxs) (hx x)⟩

#audit_axioms GroupApproximation.Full.LVCohnColimit.skCohnLimK2_exists_stage

/-- The stage `stage n`, viewed as a subring of `C₀`, is isomorphic to `stage n`.  (ABC 2009
Sec. 5; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skCohnLimK2_comapStageEquiv (n : ℕ) :
    (LVCohnDegZero.stage n).comap LVCohnDegZero.cohnDegreeZero.subtype ≃+*
      LVCohnDegZero.stage n where
  toFun x := ⟨x.1.1, x.2⟩
  invFun y := ⟨⟨y.1, LVCohnDegZero.stage_le_cohnDegreeZero n y.2⟩, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

#audit_axioms GroupApproximation.Full.LVCohnColimit.skCohnLimK2_comapStageEquiv

/-- **`C₀` is ultramatricial over `𝔽₂`**: every finite subset lies in a stage
`stage n ≅ ∏_{j ≤ n} M_{2^j}(𝔽₂)`.  (ABC 2009 Sec. 5; `simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
theorem skCohnLimK2_isUltramatricialF2_degreeZero :
    LVSkewLaurentK2.IsUltramatricialF2 LVCohnDegZero.cohnDegreeZero := by
  intro s
  obtain ⟨n, hn⟩ := skCohnLimK2_exists_stage s
  refine ⟨n, fun j => 2 ^ j.val,
    (LVCohnDegZero.stage n).comap LVCohnDegZero.cohnDegreeZero.subtype, ?_, ?_⟩
  · intro x hx
    exact hn x (Finset.mem_coe.mp hx)
  · exact ⟨(skCohnLimK2_comapStageEquiv n).trans (LVCohnDegZero.stageEquiv n)⟩

#audit_axioms GroupApproximation.Full.LVCohnColimit.skCohnLimK2_isUltramatricialF2_degreeZero

/-- **Stable `K₂(C₀) = 0`.**  (ABC 2009 Sec. 5 and Thm 3.6; `simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
theorem skCohnLimK2_stableK2Trivial_degreeZero :
    LVH2GL3.StableK2Trivial LVCohnDegZero.cohnDegreeZero :=
  LVCohnK2.stableK2Trivial_of_isUltramatricialF2 LVFieldK2.stableK2Trivial_zmodTwo
    skCohnLimK2_isUltramatricialF2_degreeZero

#audit_axioms GroupApproximation.Full.LVCohnColimit.skCohnLimK2_stableK2Trivial_degreeZero
