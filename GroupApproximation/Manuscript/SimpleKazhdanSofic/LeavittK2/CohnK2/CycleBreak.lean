import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnK2.BaseChangeProof
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoInduction
import GroupApproximation.Meta.AxiomGuard

/-!
# The Cohn base-change cycle collapses to one statement

Lane `sk-cohn-01`, first module.  Write `C = C_2(𝔽₂)` and `ι = algebraMap 𝔽₂ C`.

**The cycle.**  Three statements reduce to one another:
* `BinaryCohnStableK2TrivialStatement` (`S`, `CohnTwo/StableK2.lean`): stable `K₂(C) = 0`;
* `CohnBaseChangeK2Statement` (`B`, `CohnK2/BaseChange.lean`): padded `k = ι y`, `y ∈ K₂(𝔽₂)`;
* `CohnBaseChangeConjStatement` (`J`, `CohnK2/BaseChangeProof.lean`): padded `k` is conjugate
  to some `ι y`.

The existing links are:
* `S → B` (`baseChange_of_cohnStableK2`, take `y = 1`);
* `B → J` (`conj_of_cohnBaseChange`, take `g = 1`);
* `J → B` (`cohnBaseChange_of_conj`, via padded centrality and `E_N(𝔽₂) ↪ E_N(C)`);
* `B → S`, given `FieldTwoStableK2Statement` (`cohnStableK2_of_baseChange`).

**Loud finding.**  `FieldTwoStableK2Statement` is proved (lane `sk-leavitt-23`,
`FieldTwo.fieldTwoStableK2`), but none of the cycle files imports it.  With it, the cycle is an
equivalence class and nothing more.  No hypothesis is left:
`cycleBreak_baseChange_iff_cohnStableK2` and `cycleBreak_conj_iff_cohnStableK2`.

Worse, the `𝔽₂`-side of `B` and `J` is vacuous.  `K₂(N, 𝔽₂)` is trivial for every `N ≥ 3`
(`cycleBreak_fieldTwo_K2_eq_one`, from `FieldTwo.inj_of_three_le`).  So a witness `y` of `B` at
a stage `N ≥ 3` is `1`, and the witness equation says that the padded `k` is `1`
(`cycleBreak_baseChange_witness_trivial`).  `B` and `J` are therefore stable `K₂(C) = 0` in
disguise.  In particular the conjugation statement is **not** more elementary than the other two.
Any proof of any member is a proof of stable `K₂(C_2(𝔽₂)) = 0`: the degree-two part of the
Ara–Brustenga–Cortiñas `K`-equivalence `𝔽₂ → C_2(𝔽₂)`.

The second module, `CycleBreakSplit.lean`, splits `S` into the downstream Leavitt endpoint and a
strictly weaker relative statement.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic

/-- **`K₂(N, 𝔽₂)` is trivial for `N ≥ 3`.**  An element of `K₂` acts trivially on `𝔽₂^N`, and
the vector action of `St_N(𝔽₂)` is faithful for `N ≥ 3` (`FieldTwo.inj_of_three_le`). -/
theorem cycleBreak_fieldTwo_K2_eq_one {N : ℕ} (hN : 3 ≤ N)
    {y : GroupApproximation.SteinbergGroup (Fin N) (ZMod 2)}
    (hy : y ∈ GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin N) (ZMod 2)) : y = 1 :=
  FieldTwo.inj_of_three_le hN y (FieldTwo.act_of_projection_eq_one ((mem_K2_iff y).mp hy))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cycleBreak_fieldTwo_K2_eq_one

/-- **The base-change witness is trivial.**  At a stage `N ≥ 3`, a witness `(y, ι y = pad k)` of
`CohnBaseChangeK2Statement` forces the padded `k` to be `1`.  So the statement carries no
`𝔽₂`-information beyond stable `K₂(C_2(𝔽₂)) = 0`. -/
theorem cycleBreak_baseChange_witness_trivial {n N : ℕ} (hN3 : 3 ≤ N) (h : n ≤ N)
    {k : GroupApproximation.SteinbergGroup (Fin n) (CohnTwo (ZMod 2))}
    {y : GroupApproximation.SteinbergGroup (Fin N) (ZMod 2)}
    (hy : y ∈ GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin N) (ZMod 2))
    (hyk : GroupApproximation.SteinbergGroup.ringMap
        (algebraMap (ZMod 2) (CohnTwo (ZMod 2))) y =
      GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h) k) :
    GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h) k = 1 := by
  rw [← hyk, cycleBreak_fieldTwo_K2_eq_one hN3 hy, map_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cycleBreak_baseChange_witness_trivial

/-- `B → S`, unconditionally: `FieldTwoStableK2Statement` is proved. -/
theorem cycleBreak_cohnStableK2_of_baseChange (hB : CohnBaseChangeK2Statement) :
    BinaryCohnStableK2TrivialStatement :=
  cohnStableK2_of_baseChange hB FieldTwo.fieldTwoStableK2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cycleBreak_cohnStableK2_of_baseChange

/-- `J → S`, unconditionally. -/
theorem cycleBreak_cohnStableK2_of_conj (hC : CohnBaseChangeConjStatement) :
    BinaryCohnStableK2TrivialStatement :=
  cohnStableK2_of_conj hC FieldTwo.fieldTwoStableK2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cycleBreak_cohnStableK2_of_conj

/-- `S → J` (take `y = 1`, `g = 1`). -/
theorem cycleBreak_conj_of_cohnStableK2 (hS : BinaryCohnStableK2TrivialStatement) :
    CohnBaseChangeConjStatement :=
  conj_of_cohnBaseChange (baseChange_of_cohnStableK2 hS)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cycleBreak_conj_of_cohnStableK2

/-- **Collapse, part 1.**  The base-change statement is exactly stable `K₂(C_2(𝔽₂)) = 0`. -/
theorem cycleBreak_baseChange_iff_cohnStableK2 :
    CohnBaseChangeK2Statement ↔ BinaryCohnStableK2TrivialStatement :=
  ⟨cycleBreak_cohnStableK2_of_baseChange, baseChange_of_cohnStableK2⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cycleBreak_baseChange_iff_cohnStableK2

/-- **Collapse, part 2.**  The conjugation statement is exactly stable `K₂(C_2(𝔽₂)) = 0`. -/
theorem cycleBreak_conj_iff_cohnStableK2 :
    CohnBaseChangeConjStatement ↔ BinaryCohnStableK2TrivialStatement :=
  ⟨cycleBreak_cohnStableK2_of_conj, cycleBreak_conj_of_cohnStableK2⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cycleBreak_conj_iff_cohnStableK2

/-- The conjugation form gives the downstream Leavitt endpoint with no field hypothesis. -/
theorem cycleBreak_leavittK2_of_conj (hC : CohnBaseChangeConjStatement) :
    BinaryLeavittStableK2TrivialStatement :=
  leavittK2_of_conj hC FieldTwo.fieldTwoStableK2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.cycleBreak_leavittK2_of_conj

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
