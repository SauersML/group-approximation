import GroupApproximation.GGT.VanKampen.Estimating.Incidence

/-!
# Loop separation is now unconditional

`EstimatingGraphData` needs three certificates: the hereditary planar edge
bound, `Embedded.SelfIncidenceSeparated`, and
`Embedded.ExteriorMergeAvailable`.  The second one asks that a *self-contiguous*
selected candidate, one whose target relator cell is its own source, has
disjoint source and target arcs.

Since `Embedded.Contiguity` carries `target_ne_source` -- Osin states Lemma
`O52` only for a contiguity of a cell to *another* cell (arXiv math/0411039,
`embed-final.tex`, Lemma `O52`) -- a self-contiguous candidate does not exist,
and the clause is vacuous for every family.  So one of the three certificates
is discharged outright, with no surgery and no planarity.

This strictly generalizes `Embedded.selfIncidenceSeparated_empty`, which had
the same conclusion only for the empty family.
-/

set_option linter.unusedVariables false

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

universe u w v

/-- **Loop separation holds for every selected family.**  A self-contiguous
candidate would violate `Contiguity.target_ne_source`, so the hypothesis of
`SelfIncidenceSeparated` is never met. -/
theorem selfIncidenceSeparated_of_target_ne_source
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta)) :
    SelfIncidenceSeparated selected := by
  intro candidate hmem hself d hsource htarget
  exact candidate.contiguity.target_ne_source
    candidate.contiguity.source hself rfl

end Embedded
end VanKampen
end GGT
end GroupApproximation
