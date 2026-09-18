import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.CohnLimK2Limit
import GroupApproximation.Meta.AxiomGuard

/-!
# The corner-shift embedding of `C × 𝔽₂` (WO-LVCohnColimit-2, lane sk-lv-01)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii; Ara–Brustenga–Cortiñas,
Münster J. Math. 2 (2009), Thm 3.6, Step 3 (`yaoseq6.tex` `thm:skewyao`).

REDUCTION, not the unconditional `exists_cohnColimit_embedding`.  The draft `Final.lean` must call
`exists_cohnColimit_embedding_of_degreeZeroSurj h` with
`h : skCohnLimK2_degreeZeroSurjStatement`.

Route: `skCohnLimK2_stableK2Trivial_of_degreeZeroSurj` (`CohnLimK2Limit.lean`) turns the residual
(stable surjectivity of `K₂(C₀) → K₂(C)`, where `C₀` is the ultramatricial degree-zero part, with
stable `K₂(C₀) = 0` proved in `CohnLimK2DegZero.lean`) into `StableK2Trivial CohnLimit`.  Then
`exists_cohnColimit_embedding_of_stableK2Trivial` (`EmbeddingLimit.lean`) takes the canonical
maps into the colimit.  LOUD: the residual is logically equivalent to `StableK2Trivial CohnLimit`
(`skCohnLimK2_degreeZeroSurj_of_stableK2Trivial`); it is strictly smaller only in proof content.
-/

namespace GroupApproximation.Full.LVCohnColimit

/-- **`exists_cohnColimit_embedding` from the residual.**  Stable surjectivity of
`K₂(C₀) → K₂(C)` gives a ring `D` with stable `K₂ = 0` and injective, exhausting, compatible maps
`ι_M : C × 𝔽₂ → D` with `ι_M ∘ θ_M = ι_0`.  (ABC 2009 Thm 3.6, `yaoseq6.tex` `thm:skewyao`,
Step 3; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem exists_cohnColimit_embedding_of_degreeZeroSurj
    (h : skCohnLimK2_degreeZeroSurjStatement) :
    ∃ (D : Type) (_ : Ring D), LVH2GL3.StableK2Trivial D ∧
      ∃ ι : ℕ → (LVCohnRelK1.CohnTwoF2 × ZMod 2 →+* D),
        (∀ M, Function.Injective (ι M)) ∧
        (∀ s : Finset D, ∃ M, (s : Set D) ⊆ ((ι M).range : Set D)) ∧
        ∀ M, (ι M).comp (cohnTheta M) = ι 0 :=
  exists_cohnColimit_embedding_of_stableK2Trivial
    (skCohnLimK2_stableK2Trivial_of_degreeZeroSurj h)

#audit_axioms
  GroupApproximation.Full.LVCohnColimit.exists_cohnColimit_embedding_of_degreeZeroSurj

end GroupApproximation.Full.LVCohnColimit
