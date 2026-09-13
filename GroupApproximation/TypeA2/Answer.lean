/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.TypeA2.Statement
import GroupApproximation.TypeA2.Witness
import GroupApproximation.TypeA2.ActorFinitelyPresented
import GroupApproximation.TypeA2.TypeA
import GroupApproximation.TypeA2.ImageNotFinitelyPresented

/-!
# Fournier-Facio–Wu–Zaremsky Question 5.8: the answer

This module assembles the positive answer `question58 : Question58`.

The witness action `WitnessGroup ↷ WitnessSet` (`GroupApproximation.TypeA2.Witness`) is built
from Thompson's group `F`, realised as `HigmanThompson.geoF 0`, acting on the positive dyadic
rationals.  `WitnessGroup` is the semidirect product `geoF 0 ⋊ FreeGroup (Fin 2)`: the free
group acts by conjugation through periodic replicas of two elements of `F` that generate
`ℤ ≀ ℤ`.  The action is of type [A₂] by these four facts:
* `witnessSet_nonempty`;
* `witnessGroup_isFinitelyPresented`, from `GroupApproximation.TypeA2.ActorFinitelyPresented`;
* `witness_stabilizer_fg` and `witness_finite_orbits_pairs`, from `GroupApproximation.TypeA2.TypeA`.

Its image modulo the kernel is not finitely presented by
`witness_quotient_not_isFinitelyPresented`, from
`GroupApproximation.TypeA2.ImageNotFinitelyPresented`: that quotient retracts onto `ℤ ≀ ℤ`.
-/

namespace GroupApproximation.TypeA2

/-- The witness action is of type [A₂]. -/
theorem witness_isTypeA2 : IsTypeA2 WitnessGroup WitnessSet :=
  ⟨witnessSet_nonempty, witnessGroup_isFinitelyPresented, witness_stabilizer_fg,
    witness_finite_orbits_pairs⟩

/-- **FFWZ Question 5.8 has a positive answer**: the witness action is of type [A₂], and
its image `WitnessGroup ⧸ ker(WitnessGroup ↷ WitnessSet)` is not finitely presented. -/
theorem question58 : Question58 :=
  ⟨WitnessGroup, inferInstance, WitnessSet, inferInstance, witness_isTypeA2,
    witness_quotient_not_isFinitelyPresented⟩

end GroupApproximation.TypeA2
