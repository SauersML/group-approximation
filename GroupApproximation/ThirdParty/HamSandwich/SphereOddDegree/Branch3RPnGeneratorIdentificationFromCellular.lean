import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnGeneratorIdentification
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCupProductStructureFinal
import Mathlib

/-!
# Branch 3 generator identification from the additive cellular datum alone (Prompt 03)

Prompt 44 is closed: `construct_RPnCupProductStructure n c` builds the cellular
cup-product datum `RPnCupProductStructure c` from `c : RPnCellularCochainStructure n`
alone. Consequently every Branch-3 result that used to carry a free hypothesis

```text
cup : RPnCupProductStructure c
```

whenever `c : RPnCellularCochainStructure n` is available can drop that hypothesis.

This file provides the unconditional-from-`c` constructor for the Branch-3 target
`RPnGeneratorIdentification n`, using the completed Prompt-44 constructor internally.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- Branch 3 generator identification from the additive cellular datum alone.
The cup-product structure is now built by the completed Prompt-44 theorem
`construct_RPnCupProductStructure`. -/
def rpNGeneratorIdentification_from_cellular
    (n : ℕ) (hn : 1 ≤ n) (c : RPnCellularCochainStructure n) :
    RPnGeneratorIdentification n :=
  rpNGeneratorIdentification n hn c (construct_RPnCupProductStructure n c)

/-- Convenience alias with the order often used in final assembly files. -/
def rpnGeneratorIdentification_of_cellular
    {n : ℕ} (hn : 1 ≤ n) (c : RPnCellularCochainStructure n) :
    RPnGeneratorIdentification n :=
  rpNGeneratorIdentification_from_cellular n hn c

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

