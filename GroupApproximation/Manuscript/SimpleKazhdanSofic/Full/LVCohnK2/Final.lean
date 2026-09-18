-- DRAFT (not landed, not compiled). Lane LVCohnK2, target of work order S3.
-- Land as Full/LVCohnK2/Final.lean once LVCohnColimit.cohn_stableK2Trivial is on origin/main
-- (expected module Full/LVCohnColimit/Final.lean). Run taint.sh on the imports first.
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStableK2.Reduction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnRelK1.Cohn
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.Final

/-!
# Stable surjectivity of `K₂(𝔽₂) → K₂(C_2(𝔽₂))` (lane LVCohnK2)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  Ara–Brustenga–Cortiñas
2009 show that `𝔽₂ → C_2(𝔽₂)` is a `K`-equivalence; in degree two, stable `K₂(C_2(𝔽₂)) = 0`
(`LVCohnColimit.cohn_stableK2Trivial`) makes every class trivially a base-change image.
-/

namespace GroupApproximation.Full.LVCohnK2

/-- **Degree two of the ABC `K`-equivalence `𝔽₂ → C_2(𝔽₂)`.**
(`simple_kazhdan_sofic_group.tex` l.733-735, `sec:questions`, leaf T1b.iii.) -/
theorem cohn_stableK2BaseSurjective :
    LVStableK2.StableK2BaseSurjective LVCohnRelK1.cohnUnit :=
  LVStableK2.baseSurjective_of_stableK2Trivial LVCohnRelK1.cohnUnit
    LVCohnColimit.cohn_stableK2Trivial

end GroupApproximation.Full.LVCohnK2
