-- DRAFT (not landed, not compiled). Lane LVCohnColimit, WO-LVCohnK2-4 final assembly.
-- Land as Full/LVCohnColimit/Final.lean once LVCornerShift.stableK2_corner_eq and
-- WO-LVCohnColimit-2 (exists_cohnColimit_embedding) are on origin/main.  Fill the two imports.
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.Descent
-- import <LVCornerShift module containing stableK2_corner_eq>
-- import <module containing exists_cohnColimit_embedding>

/-!
# Stable `K₂` of the Cohn algebra `C_2(𝔽₂)` vanishes (lane LVCohnColimit)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii; ABC 2009 Thm 3.6,
`yaoseq6.tex` thm:skewyao Step 3.
-/

namespace GroupApproximation.Full.LVCohnColimit

open SteinbergGroup LVCohnRelK1

/-- The Cohn shift `a ↦ x a y` on `C_2(𝔽₂)` ... already landed in Shift.lean. -/

/-- **Stable `K₂(C_2(𝔽₂)) = 0`.**  (ABC 2009 Thm 3.6 / `yaoseq6.tex` thm:skewyao Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cohn_stableK2Trivial : LVH2GL3.StableK2Trivial CohnTwoF2 := by
  obtain ⟨D, _, hD, ι, hinj, hunion, hcompat⟩ := exists_cohnColimit_embedding
  intro n k hk
  obtain ⟨M, N, hN, hMN⟩ := cohnShiftPow_descent hD hinj hunion hcompat n k hk
  obtain ⟨N', hN', hcorner⟩ := LVCornerShift.stableK2_corner_eq (cx false ^ M) (cy false ^ M)
    (cy_pow_mul_cx_pow M) (cohnShiftPow M) (cohnShiftPow_apply M) n k hk
  refine ⟨max N N', hN.trans (le_max_left N N'), ?_⟩
  have e1 := congrArg (indexMap (R := CohnTwoF2) (Fin.castLEEmb (le_max_right N N'))) hcorner
  have e2 := congrArg (indexMap (R := CohnTwoF2) (Fin.castLEEmb (le_max_left N N'))) hMN
  rw [LVH2GL3.indexMap_castLEEmb_castLEEmb, LVH2GL3.indexMap_castLEEmb_castLEEmb] at e1
  rw [LVH2GL3.indexMap_castLEEmb_castLEEmb, map_one] at e2
  exact e1.symm.trans e2

end GroupApproximation.Full.LVCohnColimit
