import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.Assembly
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.Embedding
import GroupApproximation.Meta.AxiomGuard

/-!
# Stable `K₂` of the Cohn algebra `C_2(𝔽₂)` vanishes (lane LVCohnColimit)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii; Ara–Brustenga–Cortiñas,
Münster J. Math. 2 (2009), Thm 3.6 (`yaoseq6.tex` thm:skewyao, Step 3).

Conditional on the residual `skCohnLimK2_degreeZeroSurjStatement` (lane `sk-lv-01`): stable
surjectivity of `K₂(C₀) → K₂(C)`.  LOUD: that residual is logically equivalent to the conclusion
(both directions are proved in `CohnLimK2DegZero.lean`); it is smaller only in proof content.
-/

namespace GroupApproximation.Full.LVCohnColimit

/-- **Stable `K₂(C_2(𝔽₂)) = 0`** from the degree-zero surjectivity residual, through the
colimit embedding.  (ABC 2009 Thm 3.6, `yaoseq6.tex` thm:skewyao Step 3.) -/
theorem cohn_stableK2Trivial_of_degreeZeroSurj (h : skCohnLimK2_degreeZeroSurjStatement) :
    LVH2GL3.StableK2Trivial LVCohnRelK1.CohnTwoF2 := by
  obtain ⟨D, _, hD, ι, hinj, hunion, hcompat⟩ := exists_cohnColimit_embedding_of_degreeZeroSurj h
  exact stableK2Trivial_of_cohnColimit (ι := ι) hD hinj hunion hcompat

#audit_axioms GroupApproximation.Full.LVCohnColimit.cohn_stableK2Trivial_of_degreeZeroSurj

end GroupApproximation.Full.LVCohnColimit
