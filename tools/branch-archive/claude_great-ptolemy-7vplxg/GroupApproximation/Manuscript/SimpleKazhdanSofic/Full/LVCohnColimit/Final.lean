import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.Assembly
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.Embedding

/-!
# Stable `K₂` of the Cohn algebra `C_2(𝔽₂)` vanishes (lane LVCohnColimit)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii; Ara–Brustenga–Cortiñas,
Münster J. Math. 2 (2009), Thm 3.6 (`yaoseq6.tex` thm:skewyao, Step 3).
DRAFT: land as Full/LVCohnColimit/Final.lean once `exists_cohnColimit_embedding`
(WO-LVCohnColimit-2, Embedding.lean) is on origin/main; delete this DRAFT line first.
-/

namespace GroupApproximation.Full.LVCohnColimit

/-- **Stable `K₂(C_2(𝔽₂)) = 0`.**  (ABC 2009 Thm 3.6, `yaoseq6.tex` thm:skewyao Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cohn_stableK2Trivial : LVH2GL3.StableK2Trivial LVCohnRelK1.CohnTwoF2 := by
  obtain ⟨D, _, hD, ι, hinj, hunion, hcompat⟩ := exists_cohnColimit_embedding
  exact stableK2Trivial_of_cohnColimit (ι := ι) hD hinj hunion hcompat

end GroupApproximation.Full.LVCohnColimit
