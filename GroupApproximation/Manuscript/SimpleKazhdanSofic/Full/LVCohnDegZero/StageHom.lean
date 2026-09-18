import Mathlib.Algebra.Field.ZMod
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnDegZero.Stage

/-!
# The `n`-th stage of the degree-zero part of `C₂(𝔽₂)` as a subring

The matrix units `stageUnit n` give an injective unital ring hom
`∏_{j ≤ n} M_{2^j}(𝔽₂) → C₂(𝔽₂)`.  Its range `stage n` lies in the degree-zero part `C₀`.
It contains `e_{μν}` for `|μ| = |ν| < n` and `x_μ y_ν` for `|μ| = |ν| = n`, and
`stage n ≤ stage (n + 1)` (Ara-Brustenga-Cortiñas 2009, Sec. 5 and the proof of Thm 3.6;
`simple_kazhdan_sofic_group.tex` l.733-735, `sec:questions`, leaf T1b.iii).
-/

namespace GroupApproximation.Full.LVCohnDegZero

open GroupApproximation.Full.LVCohnRelK1

noncomputable section

/-- The non-unital algebra hom `∏_{j ≤ n} M_{2^j}(𝔽₂) → C₂(𝔽₂)` of the matrix units. -/
def stageNU (n : ℕ) : StageAlg n →ₙₐ[ZMod 2] CohnTwoF2 :=
  ChainCore.matrixUnitsHom (ZMod 2) (stageUnit_isFamily n)

theorem block_one (n : ℕ) (j : Fin (n + 1)) :
    ChainCore.matrixUnitsBlock (stageUnit n) j ((1 : StageAlg n) j) = ∑ a, stageUnit n j a a := by
  rw [ChainCore.matrixUnitsBlock]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h0 : ∀ b : Fin (2 ^ j.val), b ≠ a →
      (1 : StageAlg n) j a b • stageUnit n j a b = 0 := by
    intro b hb
    rw [Pi.one_apply, Matrix.one_apply_ne (Ne.symm hb), zero_smul]
  rw [Fintype.sum_eq_single a h0, Pi.one_apply, Matrix.one_apply_eq, one_smul]

theorem diag_sum_of_lt (n : ℕ) (j : Fin (n + 1)) (h : j.val < n) :
    ∑ a, stageUnit n j a a = wsum j.val diagU := by
  rw [← sum_vw]
  exact Finset.sum_congr rfl fun a _ => stageUnit_of_lt h a a

theorem diag_sum_of_not_lt (n : ℕ) (j : Fin (n + 1)) (h : ¬j.val < n) :
    ∑ a, stageUnit n j a a = wsum j.val diagV := by
  rw [← sum_vw]
  exact Finset.sum_congr rfl fun a _ => stageUnit_of_not_lt h a a

theorem stageNU_one (n : ℕ) : stageNU n 1 = 1 := by
  rw [stageNU, ChainCore.matrixUnitsHom_apply]
  simp only [block_one]
  rw [Fin.sum_univ_castSucc, diag_sum_of_not_lt n (Fin.last n) (Nat.lt_irrefl n), Fin.val_last]
  have hc : ∀ i : Fin n, ∑ a, stageUnit n (Fin.castSucc i) a a = wsum i.val diagU :=
    fun i => diag_sum_of_lt n (Fin.castSucc i) i.isLt
  simp only [hc]
  exact total_eq_one n

/-- The unital ring hom `∏_{j ≤ n} M_{2^j}(𝔽₂) → C₂(𝔽₂)` of the `n`-th stage. -/
def stageHom (n : ℕ) : StageAlg n →+* CohnTwoF2 where
  toFun := stageNU n
  map_one' := stageNU_one n
  map_mul' := map_mul (stageNU n)
  map_zero' := map_zero (stageNU n)
  map_add' := map_add (stageNU n)

theorem stageHom_apply (n : ℕ) (M : StageAlg n) :
    stageHom n M = ∑ j, ChainCore.matrixUnitsBlock (stageUnit n) j (M j) :=
  rfl

theorem stageHom_injective (n : ℕ) : Function.Injective (stageHom n) :=
  ChainCore.matrixUnitsHom_injective (ZMod 2) (stageUnit_isFamily n) (stageUnit_diag_ne_zero n)

/-- The `n`-th stage: the range of `stageHom n`. -/
def stage (n : ℕ) : Subring CohnTwoF2 := (stageHom n).range

/-- The `n`-th stage is isomorphic to `∏_{j ≤ n} M_{2^j}(𝔽₂)`. -/
def stageEquiv (n : ℕ) : stage n ≃+* StageAlg n :=
  (RingEquiv.ofBijective (stageHom n).rangeRestrict
    ⟨fun x y hxy => stageHom_injective n (congrArg Subtype.val hxy),
      (stageHom n).rangeRestrict_surjective⟩).symm

/-! ### Membership in the stages -/

theorem zmod_smul_mem (S : Subring CohnTwoF2) (c : ZMod 2) {x : CohnTwoF2} (hx : x ∈ S) :
    c • x ∈ S := by
  rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hx _

/-- A subring containing all the matrix units of the `n`-th stage contains the stage. -/
theorem stage_le (n : ℕ) (S : Subring CohnTwoF2) (hS : ∀ j a b, stageUnit n j a b ∈ S) :
    stage n ≤ S := by
  intro x hx
  obtain ⟨M, rfl⟩ := RingHom.mem_range.1 hx
  rw [stageHom_apply]
  refine sum_mem fun j _ => ?_
  rw [ChainCore.matrixUnitsBlock]
  exact sum_mem fun a _ => sum_mem fun b _ => zmod_smul_mem S _ (hS j a b)

theorem stageHom_single (n : ℕ) (j : Fin (n + 1)) (a b : Fin (2 ^ j.val)) :
    stageHom n (Pi.single j (Matrix.single a b (1 : ZMod 2)) : StageAlg n) = stageUnit n j a b := by
  have hoff : ∀ j' : Fin (n + 1), j' ≠ j → ChainCore.matrixUnitsBlock (stageUnit n) j'
      ((Pi.single j (Matrix.single a b (1 : ZMod 2)) : StageAlg n) j') = 0 := by
    intro j' hj'
    rw [Pi.single_eq_of_ne hj', ChainCore.matrixUnitsBlock]
    simp only [Matrix.zero_apply, zero_smul, Finset.sum_const_zero]
  have hrow : ∀ i : Fin (2 ^ j.val), i ≠ a →
      ∑ k, Matrix.single a b (1 : ZMod 2) i k • stageUnit n j i k = 0 := by
    intro i hi
    exact Finset.sum_eq_zero fun k _ => by
      rw [Matrix.single_apply_of_row_ne (Ne.symm hi), zero_smul]
  have hcol : ∀ k : Fin (2 ^ j.val), k ≠ b →
      Matrix.single a b (1 : ZMod 2) a k • stageUnit n j a k = 0 := by
    intro k hk
    rw [Matrix.single_apply_of_col_ne a a (Ne.symm hk), zero_smul]
  rw [stageHom_apply, Fintype.sum_eq_single j hoff, Pi.single_eq_same,
    ChainCore.matrixUnitsBlock, Fintype.sum_eq_single a hrow, Fintype.sum_eq_single b hcol,
    Matrix.single_apply_same, one_smul]

theorem stageUnit_mem (n : ℕ) (j : Fin (n + 1)) (a b : Fin (2 ^ j.val)) :
    stageUnit n j a b ∈ stage n :=
  RingHom.mem_range.2 ⟨_, stageHom_single n j a b⟩

/-- Every stage lies in the degree-zero part `C₀`. -/
theorem stage_le_cohnDegreeZero (n : ℕ) : stage n ≤ cohnDegreeZero := by
  refine stage_le n _ fun j a b => ?_
  by_cases hj : j.val < n
  · rw [stageUnit_of_lt hj]
    exact unitE_mem _ _ ((vw_length _ a).trans (vw_length _ b).symm)
  · rw [stageUnit_of_not_lt hj]
    exact xw_mul_yw_mem _ _ ((vw_length _ a).trans (vw_length _ b).symm)

theorem exists_vw_of_length (j : ℕ) (μ : List Bool) (h : μ.length = j) :
    ∃ a : Fin (2 ^ j), vw j a = μ := by
  subst h
  exact exists_vw μ

theorem unitE_mem_stage (N : ℕ) (μ ν : List Bool) (h : μ.length = ν.length)
    (hN : μ.length < N) : unitE μ ν ∈ stage N := by
  have hj : (⟨μ.length, by omega⟩ : Fin (N + 1)).val < N := hN
  obtain ⟨a, ha⟩ := exists_vw_of_length μ.length μ rfl
  obtain ⟨b, hb⟩ := exists_vw_of_length μ.length ν h.symm
  have hmem := stageUnit_mem N ⟨μ.length, by omega⟩ a b
  rw [stageUnit_of_lt hj] at hmem
  rw [← ha, ← hb]
  exact hmem

theorem xw_mul_yw_mem_stage (N : ℕ) (μ ν : List Bool) (hμ : μ.length = N)
    (hν : ν.length = N) : xw μ * yw ν ∈ stage N := by
  have hj : ¬(Fin.last N).val < N := Nat.lt_irrefl N
  obtain ⟨a, ha⟩ := exists_vw_of_length N μ hμ
  obtain ⟨b, hb⟩ := exists_vw_of_length N ν hν
  have hmem := stageUnit_mem N (Fin.last N) a b
  rw [stageUnit_of_not_lt hj] at hmem
  rw [← ha, ← hb]
  exact hmem

theorem xy_eq_unitE_add (μ ν : List Bool) :
    xw μ * yw ν = unitE μ ν + (xw (μ ++ [false]) * yw (ν ++ [false]) +
      xw (μ ++ [true]) * yw (ν ++ [true])) := by
  rw [unitE_expand, sub_sub, sub_add_cancel]

theorem length_vw_append (j : ℕ) (a : Fin (2 ^ j)) (c : Bool) :
    (vw j a ++ [c]).length = j + 1 := by
  rw [List.length_append, vw_length, List.length_singleton]

/-- The stages increase: `stage n ≤ stage (n + 1)`. -/
theorem stage_mono (n : ℕ) : stage n ≤ stage (n + 1) := by
  refine stage_le n _ fun j a b => ?_
  have hab : (vw j.val a).length = (vw j.val b).length :=
    (vw_length _ a).trans (vw_length _ b).symm
  have := j.isLt
  by_cases hj : j.val < n
  · rw [stageUnit_of_lt hj]
    exact unitE_mem_stage (n + 1) _ _ hab (by rw [vw_length]; omega)
  · rw [stageUnit_of_not_lt hj]
    have hjn : j.val = n := by omega
    rw [xy_eq_unitE_add]
    refine add_mem (unitE_mem_stage (n + 1) _ _ hab (by rw [vw_length]; omega))
      (add_mem ?_ ?_)
    · exact xw_mul_yw_mem_stage (n + 1) _ _ (by rw [length_vw_append, hjn])
        (by rw [length_vw_append, hjn])
    · exact xw_mul_yw_mem_stage (n + 1) _ _ (by rw [length_vw_append, hjn])
        (by rw [length_vw_append, hjn])

end

end GroupApproximation.Full.LVCohnDegZero
