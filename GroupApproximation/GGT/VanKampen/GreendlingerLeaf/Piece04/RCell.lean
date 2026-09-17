import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.SideCover
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassSameCell
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 04: the relator-cell branch

`OsinLemma94ClassCaseOneRCellStatement` covers a backwards class-word pair of one relator cell,
with no endpoint strictly inside a gap and not single-side.

## Route

The branch is refuted by showing that such a pair is single-side, against its hypothesis
(`singleSidePair_of_noGap`). The positions are placed in blocks of sides
(`exists_sideAt_block`).

* The endpoint `b'` is inside no gap, so it lies inside the word of its side. That half is proved.
* The flagged claims are `a' ≤ off + |w s|` and `b ≤ off' + |w t|`: the segments do not cross
  from one side into the next.

## The remaining mathematical gap

The flagged claims are false for spanning pairs. The real argument is the class analogue of the
enclosed-subdiagram argument of the side-level `osinLemma94CaseOneSameCell`. The class windows `p`
and `q` are arcs of one cell `Π` with face walk `X T Y S`. When no rotation `q B p A` has
`X B = 1` or `Y A = 1`, the loops `X B` or `Y A` enclose a subdiagram. That subdiagram contradicts
least area or dart minimality. The gap darts are not on the face walk, so the side-level surgery
does not transfer directly.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- **A pair with no gap endpoint is single-side (flagged).**  The endpoint `b'` lies inside its
side word, since it is inside no gap. The two remaining bounds say that the segments do not cross
a side boundary: that is the remaining gap of the relator-cell branch. -/
theorem singleSidePair_of_noGap (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps)
    (hback : C.b' < C.b) (hnogap : ¬ Q.GapEndpoint k C) : Q.SingleSidePair k C := by
  have hfwd := C.source_forward
  have ha' := C.a'_le
  have hbl := C.b_le
  have hngB' : ¬ Q.InGap k C.target C.b' := fun h => hnogap (Or.inr (Or.inr (Or.inr h)))
  obtain ⟨s, off, hs, h1, -⟩ := exists_sideAt_block Q k C.source (x := C.a) (by omega)
  obtain ⟨t, off', ht, h1', h2'⟩ := exists_sideAt_block Q k C.target (x := C.b') (by omega)
  have hB' : C.b' ≤ off' + (P.word k t).length := by
    by_contra hne
    exact hngB' ⟨t, off', ht, by omega, h2'⟩
  refine ⟨⟨s, off, hs, h1, ?_⟩, t, off', ht, by omega, h1', ?_, hB'⟩
  · omega
  · omega

/-- **The relator-cell branch** of the gap-spanning case. -/
theorem rCell : OsinLemma94ClassCaseOneRCellStatement.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨3, fun _ _ => ⟨1, Nat.one_pos, fun _ _ => ?_⟩⟩
  intro _ _ _ _ _ _ _ _ _ _ _ _ Q k C hback hnogap hnotsingle
  exact absurd (singleSidePair_of_noGap Q k C hback hnogap) hnotsingle

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.rCell
