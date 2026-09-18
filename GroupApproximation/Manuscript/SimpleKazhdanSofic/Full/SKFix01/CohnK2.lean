import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStableK2.Reduction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnRelK1.Cohn
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.Final
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.CohnLimK2Limit
import GroupApproximation.Meta.AxiomGuard

/-!
# Conditional form of the stale draft `LVCohnK2/Final.lean` (lane sk-fix-01)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  The draft
`Full/LVCohnK2/Final.lean` cites `LVCohnColimit.cohn_stableK2Trivial`, which was removed: the
landed `Full/LVCohnColimit/Final.lean` only has the conditional
`LVCohnColimit.cohn_stableK2Trivial_of_degreeZeroSurj
  (h : skCohnLimK2_degreeZeroSurjStatement)`.
This module states the draft's theorems with that one hypothesis `h`.

* `skFix01_cohn_stableK2Trivial`: stable `K₂(C_2(𝔽₂)) = 0` from `h` (ABC 2009, Thm 3.6);
* `skFix01_cohn_stableK2BaseSurjective`: the draft theorem `cohn_stableK2BaseSurjective`
  (degree two of the ABC `K`-equivalence `𝔽₂ → C_2(𝔽₂)`) from `h`;
* `skFix01_cohnLimit_stableK2Trivial`: the hypothesis `hD` of the `LVWire` rows from `h`
  (`LVCohnColimit.skCohnLimK2_stableK2Trivial_of_degreeZeroSurj`);
* `skFix01_degreeZeroSurj_iff_cohn`: LOUD honesty record, `h` is logically EQUIVALENT to stable
  `K₂(C_2(𝔽₂)) = 0`.

Truth: `h` (stable surjectivity of `K₂(C₀) → K₂(C)`, `C₀` the degree-zero part) is true, since
stable `K₂(C_2(𝔽₂)) = 0` (ABC 2009, Thm 3.6) and `h` follows from it.  It is smaller than the
conclusion only in proof content (stable `K₂(C₀) = 0` is proved in `CohnLimK2DegZero.lean`).
-/

namespace GroupApproximation.Full.SKFix01

/-- **Stable `K₂(C_2(𝔽₂)) = 0`** from the degree-zero surjectivity residual `h`.
(ABC 2009, Thm 3.6; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skFix01_cohn_stableK2Trivial (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    LVH2GL3.StableK2Trivial LVCohnRelK1.CohnTwoF2 :=
  LVCohnColimit.cohn_stableK2Trivial_of_degreeZeroSurj h

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_cohn_stableK2Trivial

/-- **Degree two of the ABC `K`-equivalence `𝔽₂ → C_2(𝔽₂)`**, from `h`: every stable class of
`K₂(C_2(𝔽₂))` is a base-change image, trivially, because stable `K₂(C_2(𝔽₂)) = 0`.
Conditional replacement of the draft `LVCohnK2.cohn_stableK2BaseSurjective`.
(`simple_kazhdan_sofic_group.tex` l.733-735, `sec:questions`, leaf T1b.iii.) -/
theorem skFix01_cohn_stableK2BaseSurjective
    (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    LVStableK2.StableK2BaseSurjective LVCohnRelK1.cohnUnit :=
  LVStableK2.baseSurjective_of_stableK2Trivial LVCohnRelK1.cohnUnit
    (skFix01_cohn_stableK2Trivial h)

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_cohn_stableK2BaseSurjective

/-- **Stable `K₂` of the Cohn colimit vanishes**, from `h`: this is the hypothesis `hD` of every
`LVWire` row.  (ABC 2009, Thm 3.6, Step 3; `simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem skFix01_cohnLimit_stableK2Trivial
    (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    LVH2GL3.StableK2Trivial LVCohnColimit.CohnLimit :=
  LVCohnColimit.skCohnLimK2_stableK2Trivial_of_degreeZeroSurj h

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_cohnLimit_stableK2Trivial

/-- **LOUD: the residual `h` is equivalent to stable `K₂(C_2(𝔽₂)) = 0`.**  Recorded so that no
consequence below is mistaken for an unconditional result.  (ABC 2009, Thm 3.6;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skFix01_degreeZeroSurj_iff_cohn :
    LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement ↔
      LVH2GL3.StableK2Trivial LVCohnRelK1.CohnTwoF2 :=
  ⟨skFix01_cohn_stableK2Trivial,
    LVCohnColimit.skCohnLimK2_degreeZeroSurj_of_cohn_stableK2Trivial⟩

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_degreeZeroSurj_iff_cohn

end GroupApproximation.Full.SKFix01
