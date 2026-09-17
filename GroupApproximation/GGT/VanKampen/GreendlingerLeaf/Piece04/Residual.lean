import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.DiffKind
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Gap
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04: the residual branches of GapSpan

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.4.  The two branches of `GapSpanResidualStatement`
(module `Piece04.Gap`).  **All theorems of this module are best attempts at open mathematics; the
proofs of `rCell_attempt` and `fullWordDiffKind_attempt` are expected not to elaborate.**

* `rCell_attempt` (OPEN): `OsinLemma94ClassCaseOneRCellStatement`.  The attempt shows that a pair with
  no gap endpoint is single-side, against its hypothesis.  The endpoint `b'` is inside no gap, so it
  lies inside the word of its side; that part holds.  The claims `a' ≤ off + |w_s|` and
  `b ≤ off' + |w_t|`, that the segments do not cross from one side into the next, are false for
  spanning pairs, and the two final `omega` calls are expected to fail.  The real argument is the
  class analogue of the enclosed-subdiagram argument of `osinLemma94CaseOneSameCell`, and the gap darts
  are not on the face walk.
* `fullWordDiffKind_attempt` (OPEN): `ClassFullWordDiffKindStatement`.  The attempt refutes the mixed
  start pair with `false_of_forwardBackwardPair`, which needs `|C.startConnector| + 2 ≤ ε`, while the
  pair has `|C.startConnector| + 1 = ε`.  The final `omega` is expected to fail.
* `gapSpanResidual_attempt`: the two together.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- **The relator-cell branch of GapSpan** (OPEN: the enclosed-subdiagram argument on class words is
missing).  Best attempt; expected not to elaborate. -/
theorem rCell_attempt : OsinLemma94ClassCaseOneRCellStatement.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨3, fun _ _ => ⟨1, Nat.one_pos, fun _ _ => ?_⟩⟩
  intro _ _ _ _ _ _ _ _ _ _ P _ Q k C hback hnogap hnotsingle
  have hfwd := C.source_forward
  have ha' := C.a'_le
  have hbl := C.b_le
  have hngB' : ¬ Q.InGap k C.target C.b' := fun h => hnogap (Or.inr (Or.inr (Or.inr h)))
  obtain ⟨s, off, hs, h1, -⟩ := exists_sideAt_block Q k C.source (x := C.a) (by omega)
  obtain ⟨t, off', ht, h1', h2'⟩ := exists_sideAt_block Q k C.target (x := C.b') (by omega)
  have hB' : C.b' ≤ off' + (P.word k t).length := by
    by_contra hne
    exact hngB' ⟨t, off', ht, by omega, h2'⟩
  -- OPEN: the segments may cross a side boundary.  Expected elaboration failure: the two `omega`
  -- calls below, `C.a' ≤ off + |w_s|` and `C.b ≤ off' + |w_t|`.
  refine hnotsingle ⟨⟨s, off, hs, h1, ?_⟩, t, off', ht, by omega, h1', ?_, hB'⟩
  · omega
  · omega

/-- **The full-word different-kind branch of GapSpan** (OPEN: the mixed step pair has a connector of
length up to `ε + 1`).  Best attempt; expected not to elaborate. -/
theorem fullWordDiffKind_attempt : ClassFullWordDiffKindStatement.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨3, fun _ h3 => ⟨1, Nat.one_pos, fun _ _ => ?_⟩⟩
  intro _ _ _ _ _ _ _ _ _ _ _ _ Q k C hback hnogap _ hcut hkind _ _ _ _ hstart _
  have hst := wordDist_start_eq Q C
  have hfwd := C.source_forward
  have ha' := C.a'_le
  -- OPEN: the step pair needs `|C.startConnector| + 2 ≤ ε`.  Expected elaboration failure: the last
  -- `omega`, since `hstart` gives `|C.startConnector| + 1 = ε`.
  exact false_of_forwardBackwardPair Q h3 C.source_lt C.target_lt C.distinct C.source_mem
    C.target_mem C.source_admissible C.target_admissible hcut hkind (by omega)
    (fun h => hnogap (Or.inl h)) (by omega) C.b_le (fun h => hnogap (Or.inr (Or.inr (Or.inl h))))
    (by omega)

/-- **The remaining gap of piece 04** (OPEN), from the two best attempts. -/
theorem gapSpanResidual_attempt : GapSpanResidualStatement.{u, w, v} :=
  ⟨rCell_attempt, fullWordDiffKind_attempt⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.rCell_attempt
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.fullWordDiffKind_attempt
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.gapSpanResidual_attempt
