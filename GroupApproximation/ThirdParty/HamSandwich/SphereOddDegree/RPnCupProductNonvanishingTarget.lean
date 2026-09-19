import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCupProductStructureConstruction

/-!
# Branch 3 Prompt 41: normalizing the cup-nonvanishing target API for `RPⁿ`

This file does **not** solve the hard RPⁿ cup-product geometry. Its purpose is to
normalize the API for the next prompts by:

* packaging the still-open nonvanishing fact as an explicit witness structure
  `RPnGeneratorCupNonzeroWitness n`, and
* providing the final assembly theorem
  `construct_RPnCupProductStructure_of_nonzeroWitness`, which turns such a witness
  into the full multiplicative datum `RPnCupProductStructure c` via the already
  proved reduction `branch3_construct_RPnCupProductStructure_of_cup_nonzero`.

The genuinely missing theorem is the nonvanishing of the actual cup product of the
canonical RPⁿ generators
(`cupZMod2 (rpCohomologyGenerator c p hp) (rpCohomologyGenerator c q hq) ≠ 0`).
That is the content of `H^*(RPⁿ;F₂) = F₂[α]/(αⁿ⁺¹)`, which is Mathlib-absent
topology and deferred to later prompts. Per the prompt, it is **not** introduced
here as an axiom, opaque declaration, or `sorry`-theorem; it will be added only
once genuinely proved.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Witness** for the cup-nonvanishing of the canonical RPⁿ generators: the cup
product of canonical degree-`p` and degree-`q` generators is nonzero whenever
`p + q ≤ n`. This packages exactly the single remaining unconditional input needed
to build the full cellular cup-product structure on `RPⁿ` over `F₂`. -/
structure RPnGeneratorCupNonzeroWitness (n : ℕ) where
  nonzero : ∀ (c : RPnCellularCochainStructure n)
    (p q : ℕ) (hp : p ≤ n) (hq : q ≤ n) (_hpq : p + q ≤ n),
      cupZMod2
        (rpCohomologyGenerator c p hp)
        (rpCohomologyGenerator c q hq) ≠ 0

/-- **Final assembly.** From a cup-nonvanishing witness, construct the full cellular
cup-product structure `RPnCupProductStructure c`, using the already proved reduction
`branch3_construct_RPnCupProductStructure_of_cup_nonzero` (whose unit field is
supplied internally by `branch3_one_eq_generator_zero`). -/
theorem construct_RPnCupProductStructure_of_nonzeroWitness
    {n : ℕ} (W : RPnGeneratorCupNonzeroWitness n)
    (c : RPnCellularCochainStructure n) :
    RPnCupProductStructure c :=
  branch3_construct_RPnCupProductStructure_of_cup_nonzero c
    (fun p q hp hq hpq => W.nonzero c p q hp hq hpq)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

