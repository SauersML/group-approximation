import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKFix01.CohnK2
import GroupApproximation.Meta.AxiomGuard

/-!
# Stable surjectivity of `K₂(𝔽₂) → K₂(C_2(𝔽₂))`, conditional (lane LVCohnK2)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.
Ara–Brustenga–Cortiñas 2009 show that `𝔽₂ → C_2(𝔽₂)` is a `K`-equivalence.  In degree
two, stable `K₂(C_2(𝔽₂)) = 0` makes every class trivially a base-change image.

REPAIR (lane ms-sk-uncond-a).  The earlier draft of this file cited
`LVCohnColimit.cohn_stableK2Trivial`, which does not exist, so the module could not build.
It now takes the one open residual of the chain,
`h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement`, and delegates to
`SKFix01.skFix01_cohn_stableK2BaseSurjective` (lane sk-fix-01).  LOUD: `h` is logically
equivalent to stable `K₂(C_2(𝔽₂)) = 0` (`SKFix01.skFix01_degreeZeroSurj_iff_cohn`).
-/

namespace GroupApproximation.Full.LVCohnK2

/-- **Degree two of the ABC `K`-equivalence `𝔽₂ → C_2(𝔽₂)`**, from the degree-zero
surjectivity residual.
(`simple_kazhdan_sofic_group.tex` l.733-735, `sec:questions`, leaf T1b.iii.) -/
theorem cohn_stableK2BaseSurjective_of_degreeZeroSurj
    (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    LVStableK2.StableK2BaseSurjective LVCohnRelK1.cohnUnit :=
  SKFix01.skFix01_cohn_stableK2BaseSurjective h

#audit_axioms GroupApproximation.Full.LVCohnK2.cohn_stableK2BaseSurjective_of_degreeZeroSurj

end GroupApproximation.Full.LVCohnK2
