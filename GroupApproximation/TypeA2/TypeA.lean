import GroupApproximation.TypeA2.HalfLineCover
import GroupApproximation.TypeA2.Witness

/-!
# The Question 5.8 witness is of type [A₂]

The witness `WitnessGroup ↷ WitnessSet` is the cover `geoF 0 ⋊ F₂` of geometric Thompson `F`,
with `F₂` acting through periodic replicas, on the positive dyadic rationals.  It is an instance of
`isTypeA2_halfLineCover`.

* `witness_stabilizer_fg`: point stabilizers of `WitnessGroup ↷ WitnessSet` are finitely generated.
* `witness_finite_orbits_pairs`: `WitnessGroup` has finitely many orbits on `WitnessSet × WitnessSet`.
-/

open MulAction

namespace GroupApproximation.TypeA2

/-- The witness action is of type [A₂]. -/
theorem witness_isTypeA2_of_cover : IsTypeA2 WitnessGroup WitnessSet :=
  isTypeA2_halfLineCover witnessPhi witnessPhi_mem_normalizer witnessPhi_mapsTo

/-- Point stabilizers of the witness action are finitely generated. -/
theorem witness_stabilizer_fg (s : WitnessSet) : (stabilizer WitnessGroup s).FG :=
  witness_isTypeA2_of_cover.2.2.1 s

/-- The witness group has finitely many orbits on pairs. -/
theorem witness_finite_orbits_pairs :
    Finite (orbitRel.Quotient WitnessGroup (WitnessSet × WitnessSet)) :=
  witness_isTypeA2_of_cover.2.2.2

end GroupApproximation.TypeA2
