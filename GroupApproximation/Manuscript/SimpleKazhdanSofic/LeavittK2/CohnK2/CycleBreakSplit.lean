import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnK2.CycleBreak
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnK2.BaseChangeConjRelative
import GroupApproximation.Meta.AxiomGuard

/-!
# Splitting stable `K₂(C_2(𝔽₂))` along `π : C_2 → L_{𝔽₂}(1,2)`

Lane `sk-cohn-01`, second module.  Write `C = C_2(𝔽₂)`, `L = L_{𝔽₂}(1,2)`,
`π = toLeavitt : C → L` and `I = (p) = ker π`.

`CycleBreak.lean` shows that the three cycle statements are one statement, stable
`K₂(C) = 0` (`S`).  This module splits `S` into two pieces:
* the downstream Leavitt endpoint `BinaryLeavittStableK2TrivialStatement`.  Every consumer of
  the cycle uses `S` only to reach this endpoint (`UsedStatement.lean`);
* `CycleBreakRelativeKernelStatement` (**the isolated statement**): every
  `k ∈ K₂(n, C)` that already dies in `St_n(L)` dies in some `St_N(C)`.  This is the image of
  relative `K₂(C, I)` in `K₂(C)`.

Endpoints:
* `cycleBreak_cohnStableK2_of_relativeKernel`: the relative statement and the Leavitt endpoint
  give `S`, hence all three cycle members (`cycleBreak_conj_of_relativeKernel`).  Route: the
  Leavitt endpoint pads `π k` to `1` (`cohnRelativeK2Surjective_of_leavittK2`).  The padded `k` is
  then in `K₂ ∩ ker π`, and the relative statement kills it.
* `cycleBreak_relativeKernel_of_cohnStableK2`: `S` implies the relative statement (drop the
  extra hypothesis).
* `cycleBreak_cohnStableK2_iff`: `S ↔ relative ∧ Leavitt`, with no hypothesis.

**Truth check.**  The relative statement is true: it is implied by `S`, which holds by
Ara–Brustenga–Cortiñas together with the proved stable `K₂(𝔽₂) = 0`.  Its mathematical
content is that `K₂(C, I) → K₂(C)` vanishes stably.  `I ≅ M_∞(𝔽₂)` has local units
(`CohnTwo.span_p_equiv_matrixUnits`).  So `K₂` excision for local-unit ideals, Morita invariance
and `K₂(𝔽₂) = 0` would give it, with no reference to `L`.

**Why it is strictly weaker (LOUD: it does not imply a cycle member on its own).**  `S → relative`
is immediate.  The converse is not available: `relative → S` needs the Leavitt endpoint as a
second input, and `S → Leavitt` is proved (`binaryLeavittStableK2Trivial_of_cohnStableK2`).  So
the relative statement is `S` with the whole Leavitt part removed.  It implies a cycle member
only **together with** the Leavitt endpoint.  That endpoint is the downstream target itself,
which sibling lanes attack directly (`StableReduction/FiveStepCentralLeavitt*`).

**Consequence for the route.**  Each cycle member implies the Leavitt endpoint, and
`cycleBreak_cohnStableK2_iff` shows that its excess over the endpoint is exactly the relative
statement.  So routing the Leavitt endpoint through the cycle adds proof content (the relative
statement) and removes none.  The cycle should not be used as a route to the endpoint.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic

/-- **Isolated statement (lane `sk-cohn-01`): relative stable `K₂(C_2(𝔽₂), (p))` vanishes in
`K₂(C_2)`.**  Every `k ∈ K₂(n, C_2(𝔽₂))` whose image in `St_n(L_{𝔽₂}(1,2))` is already
trivial becomes trivial in some `St_N(C_2(𝔽₂))`, `n ≤ N`.  True, because it is implied by stable
`K₂(C_2(𝔽₂)) = 0` (`cycleBreak_relativeKernel_of_cohnStableK2`). -/
def CycleBreakRelativeKernelStatement : Prop :=
  ∀ (n : ℕ) (k : GroupApproximation.SteinbergGroup (Fin n) (CohnTwo (ZMod 2))),
    k ∈ GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin n) (CohnTwo (ZMod 2)) →
    GroupApproximation.SteinbergGroup.ringMap (CohnTwo.toLeavitt (ZMod 2)).toRingHom k = 1 →
    ∃ (N : ℕ) (h : n ≤ N), GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h) k = 1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CycleBreakRelativeKernelStatement

/-- Stable `K₂(C_2(𝔽₂)) = 0` implies the relative statement. -/
theorem cycleBreak_relativeKernel_of_cohnStableK2 (hS : BinaryCohnStableK2TrivialStatement) :
    CycleBreakRelativeKernelStatement :=
  fun n k hk _ => hS n k hk

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cycleBreak_relativeKernel_of_cohnStableK2

/-- **Reduction.**  The relative statement and the Leavitt endpoint give stable
`K₂(C_2(𝔽₂)) = 0`. -/
theorem cycleBreak_cohnStableK2_of_relativeKernel (hR : CycleBreakRelativeKernelStatement)
    (hL : BinaryLeavittStableK2TrivialStatement) : BinaryCohnStableK2TrivialStatement := by
  intro n k hk
  obtain ⟨N, hN, hNk⟩ := cohnRelativeK2Surjective_of_leavittK2 hL n k hk
  obtain ⟨M, hM, hMk⟩ :=
    hR N (indexMap (Fin.castLEEmb hN) k) (indexMap_mem_K2 (Fin.castLEEmb hN) hk) hNk
  refine ⟨M, hN.trans hM, ?_⟩
  rw [← CohnTwo.indexMap_castLE_castLE hN hM]
  exact hMk

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cycleBreak_cohnStableK2_of_relativeKernel

/-- **Reduction to the conjugation member of the cycle.** -/
theorem cycleBreak_conj_of_relativeKernel (hR : CycleBreakRelativeKernelStatement)
    (hL : BinaryLeavittStableK2TrivialStatement) : CohnBaseChangeConjStatement :=
  cycleBreak_conj_of_cohnStableK2 (cycleBreak_cohnStableK2_of_relativeKernel hR hL)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cycleBreak_conj_of_relativeKernel

/-- **Reduction to the base-change member of the cycle.** -/
theorem cycleBreak_baseChange_of_relativeKernel (hR : CycleBreakRelativeKernelStatement)
    (hL : BinaryLeavittStableK2TrivialStatement) : CohnBaseChangeK2Statement :=
  baseChange_of_cohnStableK2 (cycleBreak_cohnStableK2_of_relativeKernel hR hL)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cycleBreak_baseChange_of_relativeKernel

/-- **Split.**  Stable `K₂(C_2(𝔽₂)) = 0` is exactly the relative statement together with the
Leavitt endpoint. -/
theorem cycleBreak_cohnStableK2_iff :
    BinaryCohnStableK2TrivialStatement ↔
      CycleBreakRelativeKernelStatement ∧ BinaryLeavittStableK2TrivialStatement :=
  ⟨fun hS => ⟨cycleBreak_relativeKernel_of_cohnStableK2 hS,
      binaryLeavittStableK2Trivial_of_cohnStableK2 hS⟩,
    fun h => cycleBreak_cohnStableK2_of_relativeKernel h.1 h.2⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cycleBreak_cohnStableK2_iff

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
