import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnGraded.Vanishing
import GroupApproximation.Meta.AxiomGuard

/-!
# Graded generation of `K₂(C_2(𝔽₂))` (lane sk-lv-04)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.

The residual `skCohnGr_gradedGenStatement` says: after padding, every `k ∈ K₂(n, C_2(𝔽₂))` is a
product of graded `K₂` elements.  Each factor lies in `K₂` and is a Steinberg word that is graded
for some potential, and different factors may use different potentials.

* `skCohnGr_cohn_stableK2Trivial_of_gradedGen`: the residual gives stable `K₂(C_2(𝔽₂)) = 0`, using
  graded vanishing (`skCohnGr_closure_gradedK2_le`).
* `skCohnGr_degreeZeroSurj_of_gradedGen`: the residual gives
  `LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement`.
* `skCohnGr_gradedGen_of_degreeZeroSurj`: conversely, `degreeZeroSurj` gives the residual
  directly, with the potential `0` and without using `K₂(C₀) = 0`.
* `skCohnGr_gradedGen_of_cohn_stableK2Trivial`: stable `K₂(C) = 0` gives the residual trivially.

**LOUD WARNING: `skCohnGr_gradedGenStatement` is logically EQUIVALENT to stable
`K₂(C_2(𝔽₂)) = 0`**, and so also to `skCohnLimK2_degreeZeroSurjStatement`.  It is weaker than
`degreeZeroSurj` only in what a proof must supply: arbitrary potentials instead of `m = 0`, and no
lift to `St(C₀)`.  It is NOT a strictly weaker true residual in the logical sense.
-/

namespace GroupApproximation.Full.LVCohnGraded

open SteinbergGroup

noncomputable section

/-- **Residual (EQUIVALENT to stable `K₂(C_2(𝔽₂)) = 0`)**: after padding, every element of
`K₂(n, C_2(𝔽₂))` is a product of graded `K₂` elements, possibly for different potentials.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skCohnGr_gradedGenStatement : Prop :=
  ∀ (n : ℕ) (k : SteinbergGroup (Fin n) LVCohnRelK1.CohnTwoF2), projection k = 1 →
    ∃ (N : ℕ) (h : n ≤ N),
      indexMap (Fin.castLEEmb h) k ∈ Subgroup.closure (skCohnGr_gradedK2Set N)

#audit_axioms GroupApproximation.Full.LVCohnGraded.skCohnGr_gradedGenStatement

/-- **Reduction**: graded generation gives stable `K₂(C_2(𝔽₂)) = 0`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnGr_cohn_stableK2Trivial_of_gradedGen (h : skCohnGr_gradedGenStatement) :
    LVH2GL3.StableK2Trivial LVCohnRelK1.CohnTwoF2 := by
  intro n k hk
  obtain ⟨N, hN, hmem⟩ := h n k hk
  obtain ⟨N', hN', e⟩ := skCohnGr_mem_stablyTrivial.mp (skCohnGr_closure_gradedK2_le N hmem)
  refine ⟨N', hN.trans hN', ?_⟩
  rw [← LVH2GL3.indexMap_castLEEmb_castLEEmb hN hN', e]

#audit_axioms GroupApproximation.Full.LVCohnGraded.skCohnGr_cohn_stableK2Trivial_of_gradedGen

/-- **Reduction**: graded generation gives the degree-zero base surjectivity residual.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnGr_degreeZeroSurj_of_gradedGen (h : skCohnGr_gradedGenStatement) :
    LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement :=
  LVStableK2.baseSurjective_of_stableK2Trivial _
    (skCohnGr_cohn_stableK2Trivial_of_gradedGen h)

#audit_axioms GroupApproximation.Full.LVCohnGraded.skCohnGr_degreeZeroSurj_of_gradedGen

/-- **Converse**: degree-zero base surjectivity gives graded generation with the potential `0`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnGr_gradedGen_of_degreeZeroSurj
    (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) : skCohnGr_gradedGenStatement := by
  intro n k hk
  obtain ⟨N, hN, y, _, e⟩ := h n k hk
  have hmem : indexMap (Fin.castLEEmb hN) k ∈ skCohnGr_gradedK2Set N := by
    refine skCohnGr_mem_gradedK2Set.mpr ⟨LVH2GL3.projection_indexMap_eq_one _ hk, fun _ => 0, ?_⟩
    rw [← e]
    exact skCohnGr_ringMap_mem_gradedSt_zero y
  exact ⟨N, hN, Subgroup.subset_closure hmem⟩

#audit_axioms GroupApproximation.Full.LVCohnGraded.skCohnGr_gradedGen_of_degreeZeroSurj

/-- **Converse**: stable `K₂(C_2(𝔽₂)) = 0` gives graded generation.  Together with
`skCohnGr_cohn_stableK2Trivial_of_gradedGen`, this shows the residual is EQUIVALENT.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnGr_gradedGen_of_cohn_stableK2Trivial
    (h : LVH2GL3.StableK2Trivial LVCohnRelK1.CohnTwoF2) : skCohnGr_gradedGenStatement := by
  intro n k hk
  obtain ⟨N, hN, e⟩ := h n k hk
  exact ⟨N, hN, by rw [e]; exact one_mem _⟩

#audit_axioms GroupApproximation.Full.LVCohnGraded.skCohnGr_gradedGen_of_cohn_stableK2Trivial

end

end GroupApproximation.Full.LVCohnGraded
