import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassJoins
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BadJunctionExclusion
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: the bad junctions of the class producer from two residuals

Osin (math/0411039v3, §9), proof of Lemma 9.4.  ms-binary's class producer counts the other classes of
a polygon through its bad junctions, and states the budget `OsinLemma94BadJunctionInput`
(`Estimating/OsinLemma94ClassJoins`) over `P.nonJoinPolygons`, the polygons with an (A1) side and at
least two class-level non-joins.

`Estimating/OsinLemma94BadJunctionExclusion` proves that a bad same-cell junction is a gap of value
other than one, so once same-cell gaps have value one the bad junctions are the boundary bad
junctions.  This module assembles the budget from the two residuals stated there, over the same index
set (`nonJoinPolygons` unfolds to the index set spelled in the residuals).

* `osinLemma94BadJunctionInput_of_pieces`: `OsinLemma94BadJunctionInput` from
  `OsinLemma94CellJunctionValueInput` and `OsinLemma94BoundaryJunctionBudgetInput`, with the constant of
  the boundary budget.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4 inside the
proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

/-- **The bad-junction budget from the cell value input and the boundary budget.** -/
theorem osinLemma94BadJunctionInput_of_pieces
    (hval : OsinLemma94CellJunctionValueInput.{u, w, v})
    (hbound : OsinLemma94BoundaryJunctionBudgetInput.{u, w, v}) :
    OsinLemma94BadJunctionInput.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps1, heps1⟩ := hval D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps2, heps2⟩ := hbound D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max eps1 eps2, fun eps heps => ?_⟩
  obtain ⟨rho1, hrho1, hr1⟩ := heps1 eps (le_of_max_le_left heps)
  obtain ⟨K, rho2, -, hr2⟩ := heps2 eps (le_of_max_le_right heps)
  refine ⟨K, max rho1 rho2, lt_max_of_lt_left hrho1,
    fun rho hrho W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax => ?_⟩
  have hv := hr1 rho (le_of_max_le_left hrho) W hW Delta cuts hleast hpos hbelow S hcard hmin P
    hmax
  have hb := hr2 rho (le_of_max_le_right hrho) W hW Delta cuts hleast hpos hbelow S hcard hmin P
    hmax
  calc ∑ k ∈ P.nonJoinPolygons, (P.badJunctions k).card
      ≤ ∑ k ∈ P.nonJoinPolygons, (P.boundaryBadJunctions k).card :=
        P.sum_card_badJunctions_le_sum_boundaryBad _ fun k hk =>
          hv k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2
    _ ≤ K * Delta.rCellCount := hb

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94BadJunctionInput_of_pieces
