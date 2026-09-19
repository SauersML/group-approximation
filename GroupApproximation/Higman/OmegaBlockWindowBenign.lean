import GroupApproximation.Higman.HNNStableHullBenign
import GroupApproximation.Higman.OmegaTower
import GroupApproximation.Higman.SwapCarrierWitness

/-!
# Finite block windows are torsion-free benign

The sequence window `blockSet m` has infinitely many elements, but only
finitely many coordinates. This file realizes the passage from the first
`j` coordinates to the first `j+1` coordinates as the stable hull under the
inner automorphism which appends the row `b_j` on the right.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-- The part of a sequence strictly below the nonnegative coordinate `j`. -/
noncomputable def blockPrefix (j : ℕ) (f : E) : E :=
  Finsupp.filter (fun i : ℤ => i < (j : ℤ)) f

theorem blockPrefix_support_lt {j : ℕ} {f : E} {i : ℤ}
    (hi : i ∈ (blockPrefix j f).support) : i < (j : ℤ) := by
  have hn : blockPrefix j f i ≠ 0 := Finsupp.mem_support_iff.mp hi
  unfold blockPrefix at hn
  rw [Finsupp.filter_apply] at hn
  by_contra h
  rw [if_neg h] at hn
  exact hn rfl

theorem blockPrefix_mem_blockSet {j : ℕ} {f : E}
    (hf : f ∈ blockSet (j + 1)) : blockPrefix j f ∈ blockSet j := by
  intro i hi
  unfold blockPrefix
  rw [Finsupp.filter_apply]
  by_cases hij : i < (j : ℤ)
  · rw [if_pos hij]
    apply hf i
    intro hwin
    have hi0 := (Finset.mem_Ico.mp hwin).1
    exact hi (Finset.mem_Ico.mpr ⟨hi0, hij⟩)
  · rw [if_neg hij]

theorem blockPrefix_add_single_mem {j : ℕ} {f : E}
    (hf : f ∈ blockSet (j + 1)) (n : ℤ) :
    blockPrefix j f + Finsupp.single (j : ℤ) n ∈ blockSet (j + 1) := by
  intro i hi
  rw [Finsupp.add_apply, Finsupp.single_apply]
  by_cases hij : i = (j : ℤ)
  · exact (hi (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)).elim
  · rw [if_neg (Ne.symm hij)]
    unfold blockPrefix
    rw [Finsupp.filter_apply]
    by_cases hilow : i < (j : ℤ)
    · rw [if_pos hilow]
      have hi0 : ¬ (0 : ℤ) ≤ i := by
        intro hi0
        exact hi (Finset.mem_Ico.mpr ⟨hi0, by omega⟩)
      rw [hf i (by
        intro hwin
        exact hi0 (Finset.mem_Ico.mp hwin).1), zero_add]
    · rw [if_neg hilow, zero_add]

theorem add_single_mem_blockSet {j : ℕ} {f : E}
    (hf : f ∈ blockSet (j + 1)) (n : ℤ) :
    f + Finsupp.single (j : ℤ) n ∈ blockSet (j + 1) := by
  intro i hi
  rw [Finsupp.add_apply, Finsupp.single_apply]
  have hne : (j : ℤ) ≠ i := by
    intro h
    subst i
    exact hi (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  rw [if_neg hne, add_zero]
  exact hf i hi

/-- A sequence in `[0,j+1)` is its prefix below `j`, followed by its `j`th
coordinate. -/
theorem blockPrefix_add_single_eq {j : ℕ} {f : E}
    (hf : f ∈ blockSet (j + 1)) :
    blockPrefix j f + Finsupp.single (j : ℤ) (f (j : ℤ)) = f := by
  ext i
  rw [Finsupp.add_apply, Finsupp.single_apply]
  by_cases hij : i = (j : ℤ)
  · subst i
    unfold blockPrefix
    rw [Finsupp.filter_apply, if_neg (by omega), if_pos rfl, zero_add]
  · rw [if_neg (Ne.symm hij)]
    unfold blockPrefix
    rw [Finsupp.filter_apply]
    by_cases hilow : i < (j : ℤ)
    · rw [if_pos hilow, add_zero]
    · rw [if_neg hilow, zero_add]
      exact (hf i (by
        intro hwin
        have hi := Finset.mem_Ico.mp hwin
        omega)).symm

theorem bElt_blockPrefix_mul_row {j : ℕ} {f : E}
    (hf : f ∈ blockSet (j + 1)) :
    bElt f = bElt (blockPrefix j f) * rowElt (j : ℤ) ^ (f (j : ℤ)) := by
  calc
    bElt f = bElt
        (blockPrefix j f + Finsupp.single (j : ℤ) (f (j : ℤ))) :=
      congrArg bElt (blockPrefix_add_single_eq hf).symm
    _ = bElt (blockPrefix j f) * rowElt (j : ℤ) ^ (f (j : ℤ)) :=
      bElt_add_single_high (fun i hi => blockPrefix_support_lt hi)

/-- Right multiplication by the last row adds to the last coordinate. -/
theorem bElt_mul_row_eq_add_single {j : ℕ} {f : E}
    (hf : f ∈ blockSet (j + 1)) (n : ℤ) :
    bElt f * rowElt (j : ℤ) ^ n =
      bElt (f + Finsupp.single (j : ℤ) n) := by
  have hadd : f + Finsupp.single (j : ℤ) n =
      blockPrefix j f + Finsupp.single (j : ℤ) (f (j : ℤ) + n) := by
    have hsplit := blockPrefix_add_single_eq hf
    ext i
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    by_cases hij : i = (j : ℤ)
    · subst i
      have hpj : blockPrefix j f (j : ℤ) = 0 := by
        unfold blockPrefix
        rw [Finsupp.filter_apply, if_neg (by omega)]
      simp [hpj]
    · have hi := congrArg (fun q : E => q i) hsplit
      simp only [Finsupp.add_apply, Finsupp.single_apply,
        if_neg (Ne.symm hij), add_zero] at hi
      simp [Ne.symm hij, hi]
  rw [bElt_blockPrefix_mul_row hf, hadd,
    bElt_add_single_high (fun i hi => blockPrefix_support_lt hi), zpow_add]
  group

/-- The inner automorphism which appends the `j`th row to a canonical block
word. -/
def appendRowAut (j : ℕ) : MulAut F₃ :=
  MulAut.conj (rowElt (j : ℤ))⁻¹

theorem appendRowAut_aElt {j : ℕ} {f : E}
    (hf : f ∈ blockSet (j + 1)) :
    appendRowAut j (aElt f) =
      aElt (f + Finsupp.single (j : ℤ) 1) := by
  unfold appendRowAut aElt
  rw [MulAut.conj_apply, inv_inv,
    ← bElt_mul_row_eq_add_single hf (1 : ℤ), zpow_one]
  group

theorem appendRowAut_symm_aElt {j : ℕ} {f : E}
    (hf : f ∈ blockSet (j + 1)) :
    (appendRowAut j).symm (aElt f) =
      aElt (f + Finsupp.single (j : ℤ) (-1)) := by
  unfold appendRowAut aElt
  rw [MulAut.conj_symm_apply, inv_inv,
    ← bElt_mul_row_eq_add_single hf (-1 : ℤ), zpow_neg, zpow_one]
  group

/-- The full `(j+1)`-coordinate subgroup is stable under changing the last
coordinate by one. -/
theorem stable_ASub_blockSet_succ (j : ℕ) :
    HNNDescent.Stable (topAut (appendRowAut j)) (ASub (blockSet (j + 1))) := by
  constructor
  · intro x hx
    change appendRowAut j (x : F₃) ∈ ASub (blockSet (j + 1))
    refine Subgroup.closure_induction (p := fun z _ =>
      appendRowAut j z ∈ ASub (blockSet (j + 1))) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨f, hf, rfl⟩
      rw [appendRowAut_aElt hf]
      exact Subgroup.subset_closure
        ⟨_, add_single_mem_blockSet (j := j) (f := f) hf 1, rfl⟩
    · rw [map_one]
      exact Subgroup.one_mem _
    · intro u v _ _ hu hv
      rw [map_mul]
      exact Subgroup.mul_mem _ hu hv
    · intro u _ hu
      rw [map_inv]
      exact Subgroup.inv_mem _ hu
  · intro x hx
    change (appendRowAut j).symm (x : F₃) ∈ ASub (blockSet (j + 1))
    refine Subgroup.closure_induction (p := fun z _ =>
      (appendRowAut j).symm z ∈ ASub (blockSet (j + 1))) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨f, hf, rfl⟩
      rw [appendRowAut_symm_aElt hf]
      exact Subgroup.subset_closure
        ⟨_, add_single_mem_blockSet (j := j) (f := f) hf (-1), rfl⟩
    · rw [map_one]
      exact Subgroup.one_mem _
    · intro u v _ _ hu hv
      rw [map_mul]
      exact Subgroup.mul_mem _ hu hv
    · intro u _ hu
      rw [map_inv]
      exact Subgroup.inv_mem _ hu

/-- Exact arithmetic computation of the stable hull which adjoins one block
coordinate. -/
theorem stableHull_ASub_blockSet_succ (j : ℕ) :
    HNNDescent.stableHull (topAut (appendRowAut j)) (ASub (blockSet j)) =
      ASub (blockSet (j + 1)) := by
  apply le_antisymm
  · apply HNNDescent.stableHull_le
    · unfold ASub
      exact Subgroup.closure_mono (Set.image_mono (by
        intro f hf i hi
        apply hf i
        intro hwin
        have hw := Finset.mem_Ico.mp hwin
        exact hi (Finset.mem_Ico.mpr ⟨hw.1, lt_trans hw.2 (by omega)⟩)))
    · exact stable_ASub_blockSet_succ j
  · unfold ASub
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨f, hf, rfl⟩
    let p : E := blockPrefix j f
    have hp : p ∈ blockSet j := blockPrefix_mem_blockSet hf
    have hpbase : aElt p ∈
        HNNDescent.stableHull (topAut (appendRowAut j)) (ASub (blockSet j)) :=
      HNNDescent.le_stableHull _ _
        (Subgroup.subset_closure ⟨p, hp, rfl⟩)
    have horbit : ∀ n : ℤ,
        aElt (p + Finsupp.single (j : ℤ) n) ∈
          HNNDescent.stableHull (topAut (appendRowAut j)) (ASub (blockSet j)) := by
      intro n
      induction n using Int.induction_on with
      | zero => simpa using hpbase
      | succ n ih =>
          have hmem : p + Finsupp.single (j : ℤ) (n : ℤ) ∈ blockSet (j + 1) :=
            blockPrefix_add_single_mem hf (n : ℤ)
          have hstep := (HNNDescent.stable_stableHull
            (topAut (appendRowAut j)) (ASub (blockSet j))).fwd
              ⟨aElt (p + Finsupp.single (j : ℤ) (n : ℤ)), Subgroup.mem_top _⟩ ih
          change appendRowAut j
            (aElt (p + Finsupp.single (j : ℤ) (n : ℤ))) ∈ _ at hstep
          rw [appendRowAut_aElt hmem] at hstep
          have hseq :
              (p + Finsupp.single (j : ℤ) (n : ℤ)) +
                  Finsupp.single (j : ℤ) 1 =
                p + Finsupp.single (j : ℤ) ((n : ℤ) + 1) := by
            ext i
            simp only [Finsupp.add_apply, Finsupp.single_apply]
            by_cases hi : (j : ℤ) = i
            · simp [hi]
              ring
            · simp [hi]
          rw [hseq] at hstep
          exact hstep
      | pred n ih =>
          have hmem : p + Finsupp.single (j : ℤ) (-(n : ℤ)) ∈
              blockSet (j + 1) :=
            blockPrefix_add_single_mem hf (-(n : ℤ))
          have hstep := (HNNDescent.stable_stableHull
            (topAut (appendRowAut j)) (ASub (blockSet j))).bwd
              ⟨aElt (p + Finsupp.single (j : ℤ) (-(n : ℤ))), Subgroup.mem_top _⟩ ih
          change (appendRowAut j).symm
            (aElt (p + Finsupp.single (j : ℤ) (-(n : ℤ)))) ∈ _ at hstep
          rw [appendRowAut_symm_aElt hmem] at hstep
          have hseq :
              (p + Finsupp.single (j : ℤ) (-(n : ℤ))) +
                  Finsupp.single (j : ℤ) (-1) =
                p + Finsupp.single (j : ℤ) (-(n : ℤ) - 1) := by
            ext i
            simp only [Finsupp.add_apply, Finsupp.single_apply]
            by_cases hi : (j : ℤ) = i
            · simp [hi]
              ring
            · simp [hi]
          rw [hseq] at hstep
          exact hstep
    rw [← blockPrefix_add_single_eq hf]
    exact horbit (f (j : ℤ))

theorem blockSet_zero_eq_Zset : blockSet 0 = Zset := by
  ext f
  constructor
  · intro hf
    change f = 0
    ext i
    exact hf i (by simp)
  · intro hf
    change f = 0 at hf
    subst f
    intro i _
    rfl

/-- Every fixed finite coordinate window has a torsion-free benign conjugate
subgroup.  This is the finite leaf needed before passing to the fat Omega
base. -/
theorem benignTF_ASub_blockSet (m : ℕ) : BenignTF (ASub (blockSet m)) := by
  induction m with
  | zero =>
      rw [blockSet_zero_eq_Zset]
      exact benignTF_ASub_Zset
  | succ j ih =>
      rw [← stableHull_ASub_blockSet_succ j]
      exact BenignTF.stableHull IsPowerTorsionFree.of_isMulTorsionFree
        (appendRowAut j) ih

end Omega
end Higman
end GroupApproximation
