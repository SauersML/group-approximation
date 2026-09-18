import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraNonMetab
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraNonDisjWitStatements
import GroupApproximation.Meta.AxiomGuard

/-!
# Local non-metabelianity of `[[T]]`, part 4: bridge to the lane `sk-flip-07` interface

Infrastructure lane `sk-flip-05` (census row `2e7c7d9ab149`, absent from the current tex).

Lane `sk-flip-07` states this lane's result as `NonDisjWitNonMetabelianStatement` (for spaces in
`Type`).  This module discharges that `Statement` from `TowerPermEmbeddingStatement` (lane
`sk-flip-04` interface), via `exists_nonMetabelian_supportedIn_of_towerPermEmbedding`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

/-- The lane `sk-flip-07` interface for lane `sk-flip-05` follows from the lane `sk-flip-04`
interface (lane `sk-flip-03` is on disk). -/
theorem nonDisjWitNonMetabelian_of_towerPermEmbedding (h04 : TowerPermEmbeddingStatement.{0}) :
    NonDisjWitNonMetabelianStatement := by
  intro X _ _ _ _ _ _ T hT W hW hne
  exact exists_nonMetabelian_supportedIn_of_towerPermEmbedding h04 hT hW hne

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.nonDisjWitNonMetabelian_of_towerPermEmbedding
