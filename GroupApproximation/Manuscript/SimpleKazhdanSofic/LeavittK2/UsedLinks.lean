import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.UsedStatement
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnK2.BaseChangeProof
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVH2GL3.RankFive
import GroupApproximation.Meta.AxiomGuard

/-!
# Links of `LeavittK2UsedStatement` to the other stable-`K₂` chains (lane sk-leavitt-24)

`simple_kazhdan_sofic_group.tex` l.733–735 (`sec:questions`).  Let `L = L_{𝔽₂}(1,2)`.

The repo states stable `K₂(L) = 0` twice:

* `LeavittK2.BinaryLeavittStableK2TrivialStatement` (`StableReduction/StableKTwo`), produced by the
  Cohn chain `leavittK2_of_conj` (lane sk-leavitt-22);
* `Full.LVH2GL3.StableK2Trivial L` (`Full/LVH2GL3/RankFive`).  Its consumer
  `binaryLeavittUnits_isSuperperfect_of_stable` uses it only at `n = 5`, through
  `projection_ker_eq_bot_of_stable`.

This module does three things:

* it re-proves the LVH2GL3 consumer from the used rank-five instance
  (`isSuperperfect_of_leavittK2Used`);
* it derives the used instance from the LVH2GL3 statement (`leavittK2Used_of_stableK2Trivial`);
* it routes the Cohn chain to it (`leavittK2Used_of_conj`).

## Truth check

Every theorem here is an implication whose hypotheses are true (Ara–Brustenga–Cortiñas 2009 for
stable `K₂`, Khanh arXiv:2609.08428 Thm 2.2 for stability).  The proofs are formal.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

/-- **Truth check (LVH2GL3 form).**  `Full.LVH2GL3.StableK2Trivial L` gives the used rank-five
instance. -/
theorem leavittK2Used_of_stableK2Trivial
    (hS : GroupApproximation.Full.LVH2GL3.StableK2Trivial
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) :
    LeavittK2UsedStatement :=
  fun k hk => hS 5 k ((GroupApproximation.BooneHigman.SteinbergBasic.mem_K2_iff k).mp hk)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.leavittK2Used_of_stableK2Trivial

/-- **LVH2GL3 consumer re-proved.**  Superperfect `Lˣ` from the used rank-five instance and
rank-by-rank injective stability from rank five. -/
theorem isSuperperfect_of_leavittK2Used (hU : LeavittK2UsedStatement)
    (hT : ∀ m, 5 ≤ m → GroupApproximation.Full.LVH2GL3.K2StabInjective
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) m) :
    GroupApproximation.Full.LVSuperperfect.IsSuperperfect
      ((GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ) := by
  apply GroupApproximation.Full.LVSuperperfect.binaryLeavittUnits_isSuperperfect_of_K2_eq_bot
    (n := 5) le_rfl
  refine (Subgroup.eq_bot_iff_forall _).mpr ?_
  intro k hk
  have hk' : GroupApproximation.SteinbergGroup.projection k = 1 := MonoidHom.mem_ker.mp hk
  obtain ⟨N, h, hN⟩ :=
    hU k ((GroupApproximation.BooneHigman.SteinbergBasic.mem_K2_iff k).mpr hk')
  exact GroupApproximation.Full.LVH2GL3.eq_one_of_indexMap_eq_one hT hk' N h hN

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.isSuperperfect_of_leavittK2Used

/-- **Cohn chain routed to the used instance.**  The conjugation form of the base change
`K₂(𝔽₂) → K₂(C_2(𝔽₂))` and stable `K₂(𝔽₂) = 0` give the used rank-five instance. -/
theorem leavittK2Used_of_conj (hC : CohnBaseChangeConjStatement)
    (hF : FieldTwoStableK2Statement) : LeavittK2UsedStatement :=
  leavittK2Used_of_binaryLeavittStableK2Trivial (leavittK2_of_conj hC hF)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.leavittK2Used_of_conj

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
