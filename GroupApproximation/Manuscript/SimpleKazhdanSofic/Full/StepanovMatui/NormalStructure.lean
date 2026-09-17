import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.NormalStructureCore

/-!
# Stepanov's Theorem 4.4 over a simple ring, part 2: the theorem

`simple_kazhdan_sofic_group.tex`, remark at tex l.307–315, "Stepanov's theorem on the normal
structure of $\GL_n$ [Stepanov, Theorem 4.4]".

Stepanov, J. Math. Sci. 95 (1999), Theorem 4.4 (pp. 2151–2152): if for every proper ideal `I`
(a) `[GL(n,R,I), E(n,R)] = E(n,R,I)` and (b) every `a ∈ GL(n,R)` has `b ∈ E(n,R/I)` and `α ≠ 0`
with `α_i = (a^b α)_j = 0`, then every subgroup `H` normalized by `E(n,R)` satisfies
`E(n,R,I) ≤ H ≤ C(n,R,I)` for a unique ideal `I`.  At a simple ring (the generality of the
remark) the only proper ideal is `0` and (a) is vacuous.

* `commute_colMatrix_of_row_annihilated`, `mem_congruenceSubgroup_bot_of_conditionB`: the p. 2152
  step `d = [c, t_{*i}(αλ)]`, with simplicity of `R` in place of Lemma 4.3 at `I = 0`;
* `StepanovConditionB`, `sandwich_of_conditionB`, `PrintedStepanovTheorem44SimpleRing`;
* `isSimpleGroup_elementaryGroup_of_conditionB`: `EL_ι(R)` is simple when `1` is the only central
  unit.

Adapted (lane-owned copy) from the never-wired orphan `GroupApproximation/Algebra/StepanovNormalStructure.lean`.
-/

namespace GroupApproximation
namespace Full
namespace StepanovMatui

open scoped commutatorElement Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

variable {H : Subgroup (Matrix ι ι R)ˣ}

/-- For a column `y` with `y_i = 0` annihilated by row `j` of `c ∈ H`, `c` commutes with the
column matrix: the commutator `[c, t_{*i}(y)]` has row `j` equal to the unit row off column `i`, so
it is central, and its `(j, j)` entry is `1`. -/
theorem commute_colMatrix_of_row_annihilated
    (hnorm : PreusserNormalizedBy.NormalizedBy H (elementaryGroup ι R)) (hno : NoTransvection H)
    (hcard : 3 ≤ Fintype.card ι) {c : (Matrix ι ι R)ˣ} (hc : c ∈ H) {i j : ι} {y : ι → R}
    (hyi : y i = 0) (hsum : ∑ t, (c : Matrix ι ι R) j t * y t = 0) :
    (c : Matrix ι ι R) * ElementarySimplicity.colMatrix i y =
      ElementarySimplicity.colMatrix i y * (c : Matrix ι ι R) := by
  have hA : RowAnnihilator.colDefect i y = ElementarySimplicity.colMatrix i y :=
    colDefect_eq_colMatrix hyi
  have hd : ⁅c, RowAnnihilator.colUnitMat i y⁆ ∈ H :=
    hnorm.commutator_mem_left hc (RowAnnihilator.colUnitMat_mem i y)
  have hval : ((⁅c, RowAnnihilator.colUnitMat i y⁆ : (Matrix ι ι R)ˣ) : Matrix ι ι R) =
      (1 + (c : Matrix ι ι R) * ElementarySimplicity.colMatrix i y *
        ((c⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)) * (1 - ElementarySimplicity.colMatrix i y) := by
    rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul]
    show (c : Matrix ι ι R) * (1 + RowAnnihilator.colDefect i y) *
        ((c⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) * (1 - RowAnnihilator.colDefect i y) = _
    rw [hA, RowAnnihilator.conj_val_eq _ _ _ (Units.mul_inv c)]
  have hrow1 : ∀ b, (1 + (c : Matrix ι ι R) * ElementarySimplicity.colMatrix i y *
      ((c⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)) j b = (1 : Matrix ι ι R) j b := by
    intro b
    rw [Matrix.add_apply, ElementarySimplicity.mul_colMatrix, colMatrix_mul_apply]
    show (1 : Matrix ι ι R) j b + (∑ t, (c : Matrix ι ι R) j t * y t) *
      ((c⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) i b = _
    rw [hsum, zero_mul, add_zero]
  have hdrow : ∀ b, ((⁅c, RowAnnihilator.colUnitMat i y⁆ : (Matrix ι ι R)ˣ) : Matrix ι ι R) j b =
      (1 : Matrix ι ι R) j b - ElementarySimplicity.colMatrix i y j b := by
    intro b
    rw [hval, mul_apply_of_row_eq_one hrow1 b, Matrix.sub_apply]
  obtain ⟨k, hki, hkj⟩ := exists_third_index hcard i j
  have hdjk : ((⁅c, RowAnnihilator.colUnitMat i y⁆ : (Matrix ι ι R)ˣ) : Matrix ι ι R) j k = 0 := by
    rw [hdrow, Matrix.one_apply_ne (Ne.symm hkj), ElementarySimplicity.colMatrix_apply,
      if_neg hki, sub_zero]
  have hdC := mem_congruenceSubgroup_bot_of_entry_eq_zero hnorm hno hcard hd (Ne.symm hkj) hdjk
  have hd1 : ⁅c, RowAnnihilator.colUnitMat i y⁆ = 1 := by
    obtain ⟨lam, -, hent⟩ := mem_congruenceSubgroup.mp hdC
    have hentry : ∀ a b,
        ((⁅c, RowAnnihilator.colUnitMat i y⁆ : (Matrix ι ι R)ˣ) : Matrix ι ι R) a b =
          (Matrix.diagonal fun _ : ι => lam) a b := by
      intro a b
      have h := hent a b
      rwa [TwoSidedIdeal.mem_bot, Matrix.sub_apply, sub_eq_zero] at h
    have hjj : ((⁅c, RowAnnihilator.colUnitMat i y⁆ : (Matrix ι ι R)ˣ) : Matrix ι ι R) j j = 1 := by
      rw [hdrow, Matrix.one_apply_eq, ElementarySimplicity.colMatrix_apply]
      by_cases hji : j = i
      · rw [if_pos hji, hji, hyi, sub_zero]
      · rw [if_neg hji, sub_zero]
    have hlam : lam = 1 := by
      rw [← hjj, hentry j j, Matrix.diagonal_apply_eq]
    apply Units.ext
    ext a b
    rw [hentry a b, hlam, Units.val_one, Matrix.diagonal_one]
  rw [commutatorElement_eq_one_iff_mul_comm] at hd1
  have h2 := congrArg (fun u : (Matrix ι ι R)ˣ => (u : Matrix ι ι R)) hd1
  simp only [Units.val_mul] at h2
  change (c : Matrix ι ι R) * (1 + RowAnnihilator.colDefect i y) =
    (1 + RowAnnihilator.colDefect i y) * (c : Matrix ι ι R) at h2
  rw [hA, mul_add, add_mul, mul_one, one_mul] at h2
  exact add_left_cancel h2

/-- **The no-transvection case of Theorem 4.4** (p. 2152), over a simple ring: if `c ∈ H` has a
nonzero column `α` with `α_i = 0` and `(cα)_j = 0`, then `c` is central.  Simplicity of `R` takes
the place of Lemma 4.3 at `I = 0`. -/
theorem mem_congruenceSubgroup_bot_of_conditionB [IsSimpleRing R]
    (hnorm : PreusserNormalizedBy.NormalizedBy H (elementaryGroup ι R)) (hno : NoTransvection H)
    (hcard : 3 ≤ Fintype.card ι) {c : (Matrix ι ι R)ˣ} (hc : c ∈ H) {α : ι → R} (hα : α ≠ 0)
    {i j : ι} (hαi : α i = 0) (hβj : ((c : Matrix ι ι R) *ᵥ α) j = 0) :
    c ∈ congruenceSubgroup ι (⊥ : TwoSidedIdeal R) := by
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hα
  have hβ : ∑ t, (c : Matrix ι ι R) j t * α t = 0 := hβj
  have hzero : ∀ q, q ≠ i → (c : Matrix ι ι R) i q = 0 := by
    intro q hqi
    by_contra hne
    obtain ⟨lam, hlam⟩ := Pestov91.SimpleModCentre.exists_mul_mul_ne_zero hp hne
    apply hlam
    have e1 : ∑ t, (c : Matrix ι ι R) j t * (α t * lam) =
        (∑ t, (c : Matrix ι ι R) j t * α t) * lam := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun t _ => (mul_assoc _ _ _).symm
    have hsum : ∑ t, (c : Matrix ι ι R) j t * (α t * lam) = 0 := by
      rw [e1, hβ, zero_mul]
    have hcomm := commute_colMatrix_of_row_annihilated hnorm hno hcard hc (i := i)
      (y := fun t => α t * lam) (by simp only [hαi, zero_mul]) hsum
    have h := congrFun (congrFun hcomm p) q
    rw [ElementarySimplicity.mul_colMatrix, ElementarySimplicity.colMatrix_apply, if_neg hqi,
      colMatrix_mul_apply] at h
    exact h.symm
  obtain ⟨q, hqi, -⟩ := exists_third_index hcard i i
  exact mem_congruenceSubgroup_bot_of_entry_eq_zero hnorm hno hcard hc (Ne.symm hqi) (hzero q hqi)

/-! ### Theorem 4.4 over a simple ring -/

/-- **Stepanov's condition (b) at the ideal `0`**: every `a ∈ GL_ι(R)` has `b ∈ E(ι, R)` and a
nonzero column `α` with `α_i = (a^b α)_j = 0` for some `i, j`, where `a^b = b⁻¹ a b`. -/
def StepanovConditionB (ι R : Type*) [Fintype ι] [DecidableEq ι] [Ring R] : Prop :=
  ∀ a : (Matrix ι ι R)ˣ, ∃ b ∈ elementaryGroup ι R, ∃ α : ι → R, α ≠ 0 ∧
    ∃ i j : ι, α i = 0 ∧ (((b⁻¹ * a * b : (Matrix ι ι R)ˣ) : Matrix ι ι R) *ᵥ α) j = 0

/-- **Stepanov's Theorem 4.4 over a simple ring**: under condition (b), every subgroup `H` of
`GL_ι(R)` normalized by `E(ι, R)` satisfies `E(ι, R, I) ≤ H ≤ C(ι, R, I)` for a unique ideal `I`. -/
theorem sandwich_of_conditionB [IsSimpleRing R] (hcard : 3 ≤ Fintype.card ι)
    (hb : StepanovConditionB ι R) (H : Subgroup (Matrix ι ι R)ˣ)
    (hnorm : PreusserNormalizedBy.NormalizedBy H (elementaryGroup ι R)) :
    ∃! I : TwoSidedIdeal R,
      (relativeElementary ι I).map (elementaryGroup ι R).subtype ≤ H ∧
        H ≤ congruenceSubgroup ι I := by
  have hex : ∃ I : TwoSidedIdeal R,
      (relativeElementary ι I).map (elementaryGroup ι R).subtype ≤ H ∧
        H ≤ congruenceSubgroup ι I := by
    by_cases hno : NoTransvection H
    · refine ⟨⊥, ?_, ?_⟩
      · rintro _ ⟨g, hg, rfl⟩
        have hbot : relativeElementary ι (⊥ : TwoSidedIdeal R) ≤ ⊥ := by
          refine Subgroup.normalClosure_le_normal ?_
          rintro _ ⟨i, j, hij, a, ha, rfl⟩
          rw [TwoSidedIdeal.mem_bot] at ha
          rw [ha, elGen_zero]
          exact Subgroup.one_mem _
        rw [Subgroup.mem_bot.mp (hbot hg), map_one]
        exact H.one_mem
      · intro a ha
        obtain ⟨b, hbE, α, hα, i, j, hαi, hβ⟩ := hb a
        have hc : b⁻¹ * a * b ∈ H := hnorm.conj_mem' hbE ha
        have hcC := mem_congruenceSubgroup_bot_of_conditionB hnorm hno hcard hc hα hαi hβ
        rw [congruenceSubgroup_bot (by omega) i] at hcC ⊢
        have key : a = b⁻¹ * a * b := by
          have h := Subgroup.mem_center_iff.mp hcC b
          calc a = b * (b⁻¹ * a * b) * b⁻¹ := by group
            _ = b⁻¹ * a * b * b * b⁻¹ := by rw [h]
            _ = b⁻¹ * a * b := by group
        rw [key]
        exact hcC
    · simp only [NoTransvection, not_forall] at hno
      obtain ⟨i, j, hij, a, hmem, hne⟩ := hno
      haveI : (PreusserNormalizedBy.elementaryPart H).Normal :=
        PreusserNormalizedBy.elementaryPart_normal hnorm
      have htop := Pestov91.SimpleModCentre.normal_eq_top_of_elGen_mem hcard
        (PreusserNormalizedBy.elementaryPart H) hij hne
        (PreusserNormalizedBy.mem_elementaryPart.mpr hmem)
      have hEH : ∀ e ∈ elementaryGroup ι R, e ∈ H := by
        intro e he
        have h : (⟨e, he⟩ : elementaryGroup ι R) ∈ PreusserNormalizedBy.elementaryPart H := by
          rw [htop]
          exact Subgroup.mem_top _
        exact PreusserNormalizedBy.mem_elementaryPart.mp h
      refine ⟨⊤, ?_, ?_⟩
      · rintro _ ⟨g, -, rfl⟩
        exact hEH _ g.2
      · intro u _
        exact mem_congruenceSubgroup.mpr
          ⟨1, one_mem_relativeCenter _, fun _ _ => TwoSidedIdeal.mem_top _⟩
  obtain ⟨I, hIl, hIu⟩ := hex
  exact ⟨I, ⟨hIl, hIu⟩, fun J hJ => PreusserNormalizedBy.eq_of_sandwich hcard hJ.1 hJ.2 hIl hIu⟩

/-- **Printed:** Stepanov's Theorem 4.4 at the generality the note uses, a simple ring, where
condition (a) is vacuous and condition (b) is `StepanovConditionB`. -/
def PrintedStepanovTheorem44SimpleRing : Prop :=
  ∀ (ι R : Type) [Fintype ι] [DecidableEq ι] [Ring R] [IsSimpleRing R], 3 ≤ Fintype.card ι →
    StepanovConditionB ι R → ∀ H : Subgroup (Matrix ι ι R)ˣ,
      PreusserNormalizedBy.NormalizedBy H (elementaryGroup ι R) →
        ∃! I : TwoSidedIdeal R,
          (relativeElementary ι I).map (elementaryGroup ι R).subtype ≤ H ∧
            H ≤ congruenceSubgroup ι I

theorem printedStepanovTheorem44SimpleRing : PrintedStepanovTheorem44SimpleRing :=
  fun _ _ _ _ _ _ hcard hb H hnorm => sandwich_of_conditionB hcard hb H hnorm

/-- **Simplicity along the Stepanov route**: over a simple ring satisfying condition (b), whose
only central unit is `1`, `EL_ι(R)` is simple for `|ι| ≥ 3`. -/
theorem isSimpleGroup_elementaryGroup_of_conditionB [IsSimpleRing R] (hcard : 3 ≤ Fintype.card ι)
    (hb : StepanovConditionB ι R)
    (hcentral : ∀ u : Rˣ, (∀ x : R, Commute (u : R) x) → (u : R) = 1) :
    IsSimpleGroup (elementaryGroup ι R) := by
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card ι)
  have hne1 : elGen (R := R) i j hij 1 ≠ 1 := by
    intro h
    have h' : elementaryUnit (R := R) i j hij 1 = elementaryUnit i j hij 0 := by
      rw [elementaryUnit_zero]
      exact congrArg Subtype.val h
    exact one_ne_zero (elementaryUnit_injective i j hij h')
  refine isSimpleGroup_of_preusser_sandwich hcard hcentral (fun N hN => ?_)
    (nontrivial_of_ne _ _ hne1)
  have hnorm : PreusserNormalizedBy.NormalizedBy (N.map (elementaryGroup ι R).subtype)
      (elementaryGroup ι R) := by
    intro e he h hh
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨(⟨e, he⟩ : elementaryGroup ι R) * n * (⟨e, he⟩ : elementaryGroup ι R)⁻¹,
      hN.conj_mem n hn ⟨e, he⟩, ?_⟩
    simp
  obtain ⟨I, ⟨hIl, hIu⟩, -⟩ := sandwich_of_conditionB hcard hb _ hnorm
  exact ⟨I, (Subgroup.map_le_map_iff_of_injective (Subgroup.subtype_injective _)).mp hIl, hIu⟩

end StepanovMatui
end Full
end GroupApproximation

#audit_axioms GroupApproximation.Full.StepanovMatui.mem_congruenceSubgroup_bot_of_conditionB
#audit_axioms GroupApproximation.Full.StepanovMatui.sandwich_of_conditionB
#audit_axioms GroupApproximation.Full.StepanovMatui.isSimpleGroup_elementaryGroup_of_conditionB
#audit_closed_axioms GroupApproximation.Full.StepanovMatui.printedStepanovTheorem44SimpleRing
