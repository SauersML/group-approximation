import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonRealization
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellArcs
import GroupApproximation.Meta.AxiomGuard

/-!
# The relator arcs piece of Lemma 9.4

Osin (math/0411039v3, §9), Lemma 9.4.  The sides of type (A1) of the component polygons are arcs
of relator cells, read from across.  `OsinLemma94CellArcsInput` asks that under
`C(ε, μ, λ, c, ρ)` every such arc be `(λ, c + 2)`-quasi-geodesic over the symmetric label
alphabet.  This file proves it (`osinLemma94CellArcsInput_holds`).

An arc of a relator cell read from across spells the formal inverse of a prefix of a cyclic shift
of the relator word of the cell (`CyclicArc.dartWord_invDarts_darts_cellDarts`).  The words of `W`
are `(λ, c)`-quasi-geodesic and closed under cyclic shifts and formal inversion, so the arc is
`(λ, c)`-quasi-geodesic over `D` (`CyclicArc.isLambdaCQuasiGeodesicWord_invDarts_darts_cellDarts`).
The symmetric label alphabet has more legal letters and the same generating set, so the word is
quasi-geodesic over it too, and a larger additive constant only weakens the condition.  The
hypothesis `0 ≤ c` is not used.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded

/-- **To the symmetric label alphabet, with a larger constant.**  A word that is
`(λ, c)`-quasi-geodesic over `D` is `(λ, c')`-quasi-geodesic over the symmetric label alphabet
once `c ≤ c'`. -/
theorem isLambdaCQuasiGeodesicWord_symmetricLabelAlphabet {G : Type u} [Group G]
    {Lambda : Type w} {D : RelGenSet G Lambda} {lambda c c' : ℝ}
    {word : List (RelLetter G Lambda)} (hword : IsLambdaCQuasiGeodesicWord D lambda c word)
    (hc : c ≤ c') : IsLambdaCQuasiGeodesicWord (symmetricLabelAlphabet D) lambda c' word := by
  refine ⟨symmetricLabelAlphabet.admissible D hword.1, fun i j hij hj => ?_⟩
  rw [symmetricLabelAlphabet.carrier_eq]
  have hlower := hword.2 i j hij hj
  linarith

/-- **`OsinLemma94CellArcsInput` holds.**  Under `C(ε, μ, λ, c, ρ)` every arc of a relator cell,
read from across, is `(λ, c + 2)`-quasi-geodesic over the symmetric label alphabet. -/
theorem osinLemma94CellArcsInput_holds : OsinLemma94CellArcsInput.{u, w, v} := by
  intro _ _ _ _ D lambda c _ _ _ S _ _ hcond _ _ arc
  have harc : IsLambdaCQuasiGeodesicWord D lambda c (dartWord S.diagram arc.reverseDarts) :=
    CyclicArc.isLambdaCQuasiGeodesicWord_invDarts_darts_cellDarts hcond arc
  exact isLambdaCQuasiGeodesicWord_symmetricLabelAlphabet harc (by linarith)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.isLambdaCQuasiGeodesicWord_symmetricLabelAlphabet
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CellArcsInput_holds
