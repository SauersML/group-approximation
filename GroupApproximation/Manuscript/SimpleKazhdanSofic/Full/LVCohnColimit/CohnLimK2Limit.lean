import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.EmbeddingLimit
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.Assembly
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.CohnLimK2DegZero
import GroupApproximation.Meta.AxiomGuard

/-!
# Stable `K₂` of the corner-shift colimit `CohnLimit` (lane sk-lv-01)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii; Ara–Brustenga–Cortiñas,
Münster J. Math. 2 (2009), Thm 3.6, Step 3 (`yaoseq6.tex` `thm:skewyao`).  The target of the lane
is `LVH2GL3.StableK2Trivial CohnLimit`, the hypothesis `hD` of
`exists_cohnColimit_embedding_of_stableK2Trivial` (`EmbeddingLimit.lean`).

Truth check.  The target is TRUE (ABC 2009 Thm 3.6).  LOUD: it is EQUIVALENT to stable
`K₂(C_2(𝔽₂)) = 0` (`skCohnLimK2_iff_cohn`).  One direction is `stableK2Trivial_of_cohnColimit`
(`Assembly.lean`).  For the other, every finite subset of `CohnLimit` lies in one range
`ι_M(C × 𝔽₂) ≅ C × 𝔽₂`, and `C × 𝔽₂` has stable `K₂ = 0` when `C` does.  So the colimit does not
lower the logical content of the leaf: the real content is ABC's Yao step for `C` itself.

Route:
* `skCohnLimK2_rangeEquiv`: `C × 𝔽₂ ≃+* ι_M(C × 𝔽₂)`;
* `skCohnLimK2_stableK2Trivial_of_cohn`, `skCohnLimK2_iff_cohn`: the equivalence above;
* `skCohnLimK2_stableK2Trivial_of_degreeZeroSurj`: the target from the residual
  `skCohnLimK2_degreeZeroSurjStatement` (`CohnLimK2DegZero.lean`, stable surjectivity of
  `K₂(C₀) → K₂(C)`), using stable `K₂(C₀) = 0`, which is proved there.
-/

namespace GroupApproximation.Full.LVCohnColimit

noncomputable section

/-- The stage `ι_M(C × 𝔽₂) ⊆ CohnLimit` is isomorphic to `C × 𝔽₂`, since `ι_M` is injective.
(`yaoseq6.tex` `thm:skewyao`, Step 3; `simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
def skCohnLimK2_rangeEquiv (M : ℕ) :
    (LVCohnRelK1.CohnTwoF2 × ZMod 2) ≃+* (cohnLimitOf M).range :=
  RingEquiv.ofBijective (cohnLimitOf M).rangeRestrict
    ⟨fun x y hxy => cohnLimitOf_injective M (congrArg Subtype.val hxy),
      (cohnLimitOf M).rangeRestrict_surjective⟩

#audit_axioms GroupApproximation.Full.LVCohnColimit.skCohnLimK2_rangeEquiv

/-- If `C = C_2(𝔽₂)` has stable `K₂ = 0`, so does `CohnLimit`: each finite subset lies in a
subring `ι_M(C × 𝔽₂) ≅ C × 𝔽₂`, and stable `K₂(𝔽₂) = 0`.  (`yaoseq6.tex` `thm:skewyao`,
Step 3; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnLimK2_stableK2Trivial_of_cohn
    (hC : LVH2GL3.StableK2Trivial LVCohnRelK1.CohnTwoF2) :
    LVH2GL3.StableK2Trivial CohnLimit := by
  refine LVCohnK2.stableK2Trivial_of_subrings fun s => ?_
  obtain ⟨M, hM⟩ := exists_range_cohnLimitOf s
  exact ⟨(cohnLimitOf M).range, hM,
    LVCohnK2.stableK2Trivial_of_ringEquiv (skCohnLimK2_rangeEquiv M)
      (LVCohnK2.stableK2Trivial_prod hC LVFieldK2.stableK2Trivial_zmodTwo)⟩

#audit_axioms GroupApproximation.Full.LVCohnColimit.skCohnLimK2_stableK2Trivial_of_cohn

/-- **LOUD: the target is equivalent to stable `K₂(C_2(𝔽₂)) = 0`.**  (ABC 2009 Thm 3.6,
Step 3; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnLimK2_iff_cohn :
    LVH2GL3.StableK2Trivial CohnLimit ↔ LVH2GL3.StableK2Trivial LVCohnRelK1.CohnTwoF2 :=
  ⟨fun hD => stableK2Trivial_of_cohnColimit (ι := cohnLimitOf) hD cohnLimitOf_injective
    exists_range_cohnLimitOf cohnLimitOf_comp_cohnTheta, skCohnLimK2_stableK2Trivial_of_cohn⟩

#audit_axioms GroupApproximation.Full.LVCohnColimit.skCohnLimK2_iff_cohn

/-- **Endpoint of lane sk-lv-01 (reduction).**  Stable surjectivity of `K₂(C₀) → K₂(C)` gives
stable `K₂(CohnLimit) = 0`.  Stable `K₂(C₀) = 0` is proved (`C₀` is ultramatricial,
`skCohnLimK2_stableK2Trivial_degreeZero`).  (ABC 2009 Thm 3.6; `simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
theorem skCohnLimK2_stableK2Trivial_of_degreeZeroSurj
    (h : skCohnLimK2_degreeZeroSurjStatement) : LVH2GL3.StableK2Trivial CohnLimit :=
  skCohnLimK2_stableK2Trivial_of_cohn (skCohnLimK2_cohn_stableK2Trivial_of_degreeZeroSurj h)

#audit_axioms
  GroupApproximation.Full.LVCohnColimit.skCohnLimK2_stableK2Trivial_of_degreeZeroSurj

/-- The converse, recorded for honesty: the target gives the residual Statement back.
(ABC 2009 Thm 3.6; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnLimK2_degreeZeroSurj_of_stableK2Trivial
    (hD : LVH2GL3.StableK2Trivial CohnLimit) : skCohnLimK2_degreeZeroSurjStatement :=
  skCohnLimK2_degreeZeroSurj_of_cohn_stableK2Trivial (skCohnLimK2_iff_cohn.mp hD)

#audit_axioms
  GroupApproximation.Full.LVCohnColimit.skCohnLimK2_degreeZeroSurj_of_stableK2Trivial

end

end GroupApproximation.Full.LVCohnColimit
