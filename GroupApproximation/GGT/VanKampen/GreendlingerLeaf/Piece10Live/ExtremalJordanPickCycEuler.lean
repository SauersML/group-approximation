import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCyc
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCountParityCycles
import GroupApproximation.Meta.AxiomGuard

/-!
# The Euler class count from the Bound half alone

Lane gl-p10-44 proves the orbit-count parity law `ExtremalJordanPickCountParityCyclesStatement`
outright (`extremalJordanPickCyc_cycles`). This file feeds it into
`extremalJordanPickCountParity_euler_of_bound`, so the Euler class count
`ExtremalJordanPickCountEulerStatement` now needs only the Bound half.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

/-- **The Euler class count from the Bound half alone.** -/
theorem extremalJordanPickCyc_euler_of_bound
    (hb : ExtremalJordanPickCountParityBoundStatement.{u, w, v}) :
    ExtremalJordanPickCountEulerStatement.{u, w, v} :=
  extremalJordanPickCountParity_euler_of_bound hb extremalJordanPickCyc_cycles

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_euler_of_bound

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion
