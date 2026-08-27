import GroupApproximation.Manuscript.OneSidedMFRadical.ReducedCStarConsequence
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceSimpleDefectInferenceClosure

/-!
# `thm:headline` with the printed finite-generation clause, exactly

`non_mf_groups_exist.tex`, Theorem `thm:headline` (Theorem B) opens: "Put
`R = L_{𝔽₂}(1,2)` and `H = EL₁₂(R)`.  Then `H` is finitely generated,
nontrivial, simple, has property `(T)`, and `Rad_MF(H) = H`. … Every
homomorphism from `H` to an MF group is trivial.  So `H` is non-MF, and
`C*_r(H)` is separable and stably finite but not MF."

`ReducedCStarConsequence.PrintedHeadline` already assembles every clause of
this theorem except that its first conjunct is `Countable H` rather than the
printed "finitely generated".  `Countable H` is the weaker fact used
downstream (it is all `IsCDEOperatorMF` and the reduced-C⋆ construction
need), and it was stated there because it is what `HeadlineConclusion`
lacked; but it is not the literal printed adjective.  `H` is in fact finitely
generated — `RankTwelveEndpoint.finitelyGenerated : Group.FG H`, proved in
`RankTwelveEndpoints.lean` from the elementary-group generation calculation —
and finite generation implies countability, so nothing about `PrintedHeadline`
was ever false.  `PrintedHeadlineExact` restates the theorem with the exact
printed clause in the exact printed position, so that a reader checking
`thm:headline` word for word has a single declaration to check against.

* `PrintedHeadlineExact` — the printed theorem, clause for clause, in printed
  order: finitely generated; nontrivial, simple, property `(T)`,
  `Rad_MF(H) = H`, every MF-target homomorphism trivial, `H` not MF (these six
  bundled as `RankTwelveEndpoint.HeadlineConclusion`, itself in printed
  order); and the reduced-C⋆ clause `ReducedCStarConsequence`.
* `manuscriptPrintedHeadlineExact` — proved from three already-closed
  theorems, with no new mathematics: `RankTwelveEndpoint.finitelyGenerated`,
  `manuscriptBinaryLeavittHeadline`, `manuscriptReducedCStarConsequence`.
* `normalClosure_eq_top_of_simple` — the printed one-line inference at the end
  of the proof of Proposition `prop:defect`, "Since `H` is simple, the
  nontrivial element `d` normally generates `H`", stated for an arbitrary
  nonidentity element of `H` rather than only for the printed `d`.  It is the
  same abstract step `SentenceSimpleDefectInferenceClosure` already proves for
  `defect` itself (`manuscriptSentence67_simplicity_gives_defect_normalGeneration`);
  this declaration is that step's statement, generalized over the element and
  named for the printed sentence rather than for the census row that first
  used it.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open RankTwelveEndpoint

/-! ## The printed theorem, with the printed finite-generation clause -/

/-- **`thm:headline` exactly as printed, as one proposition.**  With
`R = L_{𝔽₂}(1,2)` and `H = EL₁₂(R)`: `H` is finitely generated, nontrivial,
simple, has property `(T)`, and `Rad_MF(H) = H` — equivalently every
homomorphism from `H` to an MF group is trivial, so in particular `H` is not
MF — and its reduced group C⋆-algebra `C*_r(H)` is separable and stably
finite but is not MF.

The three conjuncts are, in order, `Group.FG H` — the printed "finitely
generated", in place of the weaker `Countable H` used by
`ReducedCStarConsequence.PrintedHeadline` — the six clauses of
`RankTwelveEndpoint.HeadlineConclusion`, and the reduced-C⋆ clause
`ReducedCStarConsequence`.  As in `PrintedHeadline`, finite generation is a
separate conjunct because `HeadlineConclusion` does not carry it, and the
reduced-C⋆ clause is separate because `HeadlineConclusion` predates it. -/
def PrintedHeadlineExact : Prop :=
  Group.FG H ∧ HeadlineConclusion ∧ ReducedCStarConsequence

/-- **The printed theorem, proved, hypothesis-free.**  Each conjunct is
discharged by the endpoint that already owns it:
`RankTwelveEndpoint.finitelyGenerated`, `manuscriptBinaryLeavittHeadline` —
where simplicity enters via `RankTwelveEndpoint.manuscriptPropositionSimple`
— and `manuscriptReducedCStarConsequence`. -/
theorem manuscriptPrintedHeadlineExact : PrintedHeadlineExact :=
  ⟨RankTwelveEndpoint.finitelyGenerated, manuscriptBinaryLeavittHeadline,
    manuscriptReducedCStarConsequence⟩

/-! ## The printed simplicity inference of `prop:defect`, generalized -/

/-- **The printed one-line inference "Since `H` is simple, the nontrivial
element `d` normally generates `H`"**, the last sentence of the proof of
Proposition `prop:defect`, stated for an arbitrary nonidentity element of `H`
rather than only for the printed defect `d = e₀₂(q)`.

The proof is exactly the printed route: a normal subgroup of a simple group
containing a nonidentity element is the whole group, applied to the normal
subgroup `⟪d⟫_H`, which contains `d` by construction. `d ≠ 1` then rules out
the trivial alternative, leaving `⟪d⟫_H = H`.  This is the same abstract step
`top_le_normal_of_simple_of_nontrivial_mem` already isolated in
`SentenceSimpleDefectInferenceClosure`, and the same argument
`manuscriptSentence67_simplicity_gives_defect_normalGeneration` there applies
at the fixed element `defect`; here it is stated once for every nonidentity
`d : H`. -/
theorem normalClosure_eq_top_of_simple {d : H} (hd : d ≠ 1) :
    Subgroup.normalClosure ({d} : Set H) = ⊤ := by
  apply top_unique
  exact top_le_normal_of_simple_of_nontrivial_mem
    manuscriptPropositionSimple
    (Subgroup.normalClosure ({d} : Set H))
    Subgroup.normalClosure_normal hd
    (Subgroup.subset_normalClosure (Set.mem_singleton d))

end OneSidedMFRadical
end Manuscript
end GroupApproximation
