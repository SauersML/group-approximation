import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.Descent
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCornerShift.StableK2

/-!
# Stable `K₂` of `C_2(𝔽₂)` from a corner-shift colimit (lane LVCohnColimit)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  Step 3 of the
proof of the degree-two Ara–Brustenga–Cortiñas theorem (`yaoseq6.tex` thm:skewyao; ABC,
Münster J. Math. 2 (2009), Thm 3.6): the map `η(a) = x a y` induces the identity on stable
`K₂` because `y x = 1` (`LVCornerShift.stableK2_corner_eq`).  So if the direct limit of the
unital corner shifts `θ_M` has stable `K₂ = 0`, then `C_2(𝔽₂)` has stable `K₂ = 0`.

* `stableK2Trivial_of_cohnColimit`: this statement for an arbitrary ring `D` receiving compatible
  injective maps `ι_M : C × 𝔽₂ → D`, `ι_M ∘ θ_M = ι_0`, whose ranges exhaust `D`.
-/

namespace GroupApproximation.Full.LVCohnColimit

open SteinbergGroup LVCohnRelK1

/-- Let `D` be a ring with stable `K₂ = 0` receiving injective ring maps `ι_M : C × 𝔽₂ → D` with
`ι_M ∘ θ_M = ι_0` whose ranges exhaust `D`.  Then `C = C_2(𝔽₂)` has stable `K₂ = 0`: a class
`k` is killed by a corner shift `a ↦ x^M a y^M` (`cohnShiftPow_descent`), and that shift acts
trivially on stable `K₂` (`LVCornerShift.stableK2_corner_eq`).  (ABC 2009, proof of Thm 3.6;
`yaoseq6.tex` thm:skewyao Step 3; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem stableK2Trivial_of_cohnColimit {D : Type*} [Ring D] (hD : LVH2GL3.StableK2Trivial D)
    {ι : ℕ → (CohnTwoF2 × ZMod 2 →+* D)} (hinj : ∀ M, Function.Injective (ι M))
    (hunion : ∀ s : Finset D, ∃ M, (s : Set D) ⊆ ((ι M).range : Set D))
    (hcompat : ∀ M, (ι M).comp (cohnTheta M) = ι 0) :
    LVH2GL3.StableK2Trivial CohnTwoF2 := by
  intro n k hk
  obtain ⟨M, N, hN, hMN⟩ := cohnShiftPow_descent hD hinj hunion hcompat n k hk
  obtain ⟨N', _hN', hcorner⟩ := LVCornerShift.stableK2_corner_eq (cx false ^ M) (cy false ^ M)
    (cy_pow_mul_cx_pow M) (cohnShiftPow M) (cohnShiftPow_apply M) n k hk
  refine ⟨max N N', hN.trans (le_max_left N N'), ?_⟩
  have e1 := congrArg (indexMap (R := CohnTwoF2) (Fin.castLEEmb (le_max_right N N'))) hcorner
  have e2 := congrArg (indexMap (R := CohnTwoF2) (Fin.castLEEmb (le_max_left N N'))) hMN
  rw [LVH2GL3.indexMap_castLEEmb_castLEEmb, LVH2GL3.indexMap_castLEEmb_castLEEmb] at e1
  rw [LVH2GL3.indexMap_castLEEmb_castLEEmb, map_one] at e2
  exact e1.symm.trans e2

end GroupApproximation.Full.LVCohnColimit
