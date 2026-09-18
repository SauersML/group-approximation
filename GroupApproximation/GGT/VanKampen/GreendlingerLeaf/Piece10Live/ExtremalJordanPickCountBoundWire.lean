import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCycEuler
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCountBoundArith
import GroupApproximation.Meta.AxiomGuard

/-!
# The Euler class count, wired

Lane gl-p10-42.  Euler's bound `2 + excess ≤ #L + #O` holds for every pocket with a closed
boundary walk (`extremalJordanPickCountBound_bound`).  So the Bound half
`ExtremalJordanPickCountParityBoundStatement` holds outright
(`extremalJordanPickCountBound_boundStatement`), and it drops all of its other premises.  Lane
gl-p10-44 proved the orbit-count parity law (`extremalJordanPickCyc_euler_of_bound`).  Feeding the
Bound half into it gives, with no remaining premise:

* the Euler class count `ExtremalJordanPickCountEulerStatement`
  (`extremalJordanPickCountBound_euler`);
* the three-class count `ExtremalJordanPickEulerCountStatement`
  (`extremalJordanPickCountBound_count`);
* the Three statement `ExtremalJordanPickRegionThreeStatement`
  (`extremalJordanPickCountBound_three`).

Independently of gl-p10-44, the Parity half alone also gives the count
(`extremalJordanPickCountBound_count_of_parity`).

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

/-- **The Bound half** holds outright. -/
theorem extremalJordanPickCountBound_boundStatement :
    ExtremalJordanPickCountParityBoundStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hhi hla hlabel K hK hft hsrc htgt hpin hrose htwo hloc
  exact extremalJordanPickCountBound_bound K hK

/-- **The Euler class count** holds outright. -/
theorem extremalJordanPickCountBound_euler : ExtremalJordanPickCountEulerStatement.{u, w, v} :=
  extremalJordanPickCyc_euler_of_bound extremalJordanPickCountBound_boundStatement

/-- **The three-class count** holds outright. -/
theorem extremalJordanPickCountBound_count : ExtremalJordanPickEulerCountStatement.{u, w, v} :=
  extremalJordanPickCount_count_of_euler extremalJordanPickCountBound_euler

/-- **The Three statement** holds outright. -/
theorem extremalJordanPickCountBound_three : ExtremalJordanPickRegionThreeStatement.{u, w, v} :=
  extremalJordanPickCount_three_of_euler extremalJordanPickCountBound_euler

/-- **The Euler class count from the Parity half.** -/
theorem extremalJordanPickCountBound_euler_of_parity
    (h : ExtremalJordanPickCountParityStatement.{u, w, v}) :
    ExtremalJordanPickCountEulerStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hhi hla hlabel K hK hft hsrc htgt hpin hrose htwo hloc
  exact ⟨extremalJordanPickCountBound_bound K hK,
    h D eps X lo hi hhi hla hlabel K hK hft hsrc htgt hpin hrose htwo hloc⟩

/-- **The three-class count from the Parity half.** -/
theorem extremalJordanPickCountBound_count_of_parity
    (h : ExtremalJordanPickCountParityStatement.{u, w, v}) :
    ExtremalJordanPickEulerCountStatement.{u, w, v} :=
  extremalJordanPickCount_count_of_euler (extremalJordanPickCountBound_euler_of_parity h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_boundStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_euler
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_count
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_three
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_euler_of_parity
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountBound_count_of_parity
