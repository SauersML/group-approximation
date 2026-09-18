import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVWire.Chain
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.StableK2
import GroupApproximation.Meta.AxiomGuard

/-!
# Frontier item #2 in its registered form, from stable `K₂` of the Cohn colimit

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735.  The frontier registers item #2
(stable `K₂(C_2(𝔽₂)) = 0`) as `LeavittK2.BinaryCohnStableK2TrivialStatement`
(`LeavittK2/CohnTwo/StableK2.lean`, not imported by the library root).  That statement is about
`LeavittK2.CohnTwo (ZMod 2) = RingQuot (LeavittK2.CohnRelation (ZMod 2))`, while the chain
proves it for `LVCohnRelK1.CohnTwoF2 = RingQuot LVCohnRelK1.CohnRel`.  The two relations are
distinct inductives with the same four constructors `tᵢ sⱼ = δᵢⱼ`, so the rings are only
propositionally equal.  Bridges:

* `skLVWire_cohnRel_eq`: `LVCohnRelK1.CohnRel = LeavittK2.CohnRelation (ZMod 2)` (funext,
  propext, case analysis);
* `skLVWire_stableK2Trivial_ringQuot_congr`: `StableK2Trivial` transports along an equality of
  relations (`subst`);
* `BooneHigman.SteinbergBasic.mem_K2_iff`: `k ∈ K₂(n, R) ↔ projection k = 1`.

Route: `hD` → `LVWire.skLVWire_cohnStableK2_of_cohnLimit` (Chain) → bridges → this statement.
This file imports the otherwise unimported module `LeavittK2.CohnTwo.StableK2`, whose closure
adds the unbuilt modules `CohnRelativeK1.Words`, `CohnTwo.Basic`, `CohnTwo.Quotient`,
`CohnTwo.Relative` and `StableReduction.StableKTwo` (all on disk).
-/

namespace GroupApproximation.Full.LVWire

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 in
/-- The two Cohn relations `tᵢ sⱼ = δᵢⱼ` on `BinaryLeavitt.Free (ZMod 2)` coincide
(tex l.733-735). -/
theorem skLVWire_cohnRel_eq : LVCohnRelK1.CohnRel = CohnRelation (ZMod 2) := by
  funext a b
  apply propext
  constructor
  · intro h
    cases h
    exacts [.t0_s0, .t0_s1, .t1_s0, .t1_s1]
  · intro h
    cases h
    exacts [.t0_s0, .t0_s1, .t1_s0, .t1_s1]

#audit_axioms GroupApproximation.Full.LVWire.skLVWire_cohnRel_eq

/-- Stable `K₂ = 0` transports along an equality of defining relations (tex l.733-735). -/
theorem skLVWire_stableK2Trivial_ringQuot_congr {R : Type*} [Ring R] {r s : R → R → Prop}
    (h : r = s) (hr : LVH2GL3.StableK2Trivial (RingQuot r)) :
    LVH2GL3.StableK2Trivial (RingQuot s) := by
  subst h
  exact hr

#audit_axioms GroupApproximation.Full.LVWire.skLVWire_stableK2Trivial_ringQuot_congr

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 in
/-- **#2 for `LeavittK2.CohnTwo (ZMod 2)`**: stable `K₂(C_2(𝔽₂)) = 0` from stable `K₂` of the
Cohn colimit (ABC 2009, Thm 3.6; tex l.733-735). -/
theorem skLVWire_cohnTwoStableK2_of_cohnLimit
    (hD : LVH2GL3.StableK2Trivial LVCohnColimit.CohnLimit) :
    LVH2GL3.StableK2Trivial (CohnTwo (ZMod 2)) := by
  have h := skLVWire_stableK2Trivial_ringQuot_congr skLVWire_cohnRel_eq
    (skLVWire_cohnStableK2_of_cohnLimit hD)
  exact h

#audit_axioms GroupApproximation.Full.LVWire.skLVWire_cohnTwoStableK2_of_cohnLimit

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 in
/-- **#2, registered form**: `LeavittK2.BinaryCohnStableK2TrivialStatement` from stable `K₂` of
the Cohn colimit (tex l.733-735). -/
theorem skLVWire_binaryCohnStatement_of_cohnLimit
    (hD : LVH2GL3.StableK2Trivial LVCohnColimit.CohnLimit) :
    BinaryCohnStableK2TrivialStatement := by
  intro n k hk
  exact skLVWire_cohnTwoStableK2_of_cohnLimit hD n k
    ((BooneHigman.SteinbergBasic.mem_K2_iff k).mp hk)

#audit_axioms GroupApproximation.Full.LVWire.skLVWire_binaryCohnStatement_of_cohnLimit

end GroupApproximation.Full.LVWire
