import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnActualAlphaPowersGenerate
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnActualAlphaPowerNonvanishing

/-!
# Assembling the `RPnGeneratorIdentification n` branch (Prompt 32)

This file gives the **single canonical constructed term** of the third-branch
structure

```text
RPnGeneratorIdentification n
```

(defined in `RPnCupProductGenerator.lean`), built from the project's honest
topological inputs, and re-exports the branch's load-bearing consequences with
`RPnGeneratorIdentification n` **no longer appearing as a root hypothesis** —
everywhere below it is a *constructed* term, not a free assumption.

## The constructed term

```text
rpNGeneratorIdentification n hn c cup : RPnGeneratorIdentification n
```

is the project-style positive-dimensional construction. Its three fields are all
filled by genuine proofs (no free `Φ`, no free monodromy assumption):

* `monodromy := monodromyFunctional n` — the **actual** monodromy functional,
  constructed unconditionally in `RPnMonodromyFunctional.lean` /
  `ActualRPAlpha.lean` from the first Stiefel–Whitney class of the double cover
  `Sⁿ → RPⁿ` (input **(A)**; already parameterless);
* `toModel := rpCohomologyToModelHom c cup` — the graded ring bridge
  `H^*(RPⁿ; F₂) → F₂[α]/(αⁿ⁺¹)`, genuinely constructed
  (`RPnCupProductModelCompatibility.lean`) from the two honest topological
  inputs (input **(B)**);
* `alpha_eq` — the (free) compatibility `toModel.alpha = rpAlpha n monodromy`,
  discharged because the bridge's degree-one class is taken to be the actual
  class (`RPAlphaEqualsModelGenerator.lean`).

## Remaining honest inputs

The construction takes `1 ≤ n` together with the two genuinely Mathlib-absent
topological data of `RPⁿ`:

* `c : RPnCellularCochainStructure n` — the cellular-approximation identification
  of the singular cochain complex of `RPⁿ` with the cellular model
  (`RPnAdditiveCohomology.lean`);
* `cup : RPnCupProductStructure c` — the `RPⁿ` cup-product computation
  (`RPnCupProductModelCompatibility.lean`).

These remain the branch's irreducible honest inputs (a fully parameterless
`(n : ℕ) → RPnGeneratorIdentification n` would require constructing `c` and `cup`
from `n` alone, the recorded remaining blocker; see
`docs/current/Construct_RPnGeneratorIdentification_Result.md`). No fake `α`, no
fake ring isomorphism, and no placeholder is introduced.
-/

noncomputable section

open CategoryTheory AlgebraicTopology Module

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## 1. The constructed branch term -/

/-- **The constructed `RPnGeneratorIdentification n`** (project-style,
positive-dimensional). From `1 ≤ n` and the two honest topological inputs
`c : RPnCellularCochainStructure n` and `cup : RPnCupProductStructure c`, this
assembles the full third-branch structure with all three fields filled by genuine
proofs and its degree-one class taken to be the actual monodromy class
`rpAlpha n (monodromyFunctional n) = actualRPAlpha n`. This is the canonical
entry point that replaces every former free hypothesis
`I : RPnGeneratorIdentification n`. -/
def rpNGeneratorIdentification (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) :
    RPnGeneratorIdentification n :=
  rpNGeneratorIdentification_of_cellular_cup n hn c cup

@[simp] theorem rpNGeneratorIdentification_monodromy (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) :
    (rpNGeneratorIdentification n hn c cup).monodromy = monodromyFunctional n := rfl

@[simp] theorem rpNGeneratorIdentification_toModel (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) :
    (rpNGeneratorIdentification n hn c cup).toModel = rpCohomologyToModelHom c cup := rfl

/-- The degree-one class of the constructed identification is the actual class. -/
theorem rpAlpha_rpNGeneratorIdentification (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) :
    rpAlpha n (rpNGeneratorIdentification n hn c cup).monodromy = actualRPAlpha n := rfl

/-- The branch target is inhabited from the honest inputs. -/
theorem nonempty_rpNGeneratorIdentification (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) :
    Nonempty (RPnGeneratorIdentification n) :=
  ⟨rpNGeneratorIdentification n hn c cup⟩

/-! ## 2. Exported consequences (no `RPnGeneratorIdentification n` hypothesis)

Each of the branch's load-bearing consequences, restated from the honest inputs
`(hn, c, cup)` with the constructed `rpNGeneratorIdentification` in place of a
free `I`. These re-export the conditional results of `RPnCupProductGenerator.lean`
at the actual class. -/

/-- **Sub-truncation nonvanishing** `αᵏ ≠ 0` (`k ≤ n`) for the actual class, from
the honest inputs. -/
theorem rpAlpha_actual_power_ne_zero_of_cellular_cup (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c)
    {k : ℕ} (hk : k ≤ n) :
    cupPowZMod2 (actualRPAlpha n) k ≠ 0 :=
  actualRPAlpha_power_ne_zero n hn c cup hk

/-- **Top-power nonvanishing** `αⁿ ≠ 0` for the actual class, from the honest
inputs — the load-bearing class for the final odd-degree theorem. -/
theorem rpAlpha_actual_power_top_ne_zero_of_cellular_cup (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) :
    cupPowZMod2 (actualRPAlpha n) n ≠ 0 :=
  actualRPAlpha_topPower_ne_zero n hn c cup

/-- **The actual powers generate** `Hᵏ(RPⁿ; F₂)` (`k ≤ n`), from the honest
inputs. -/
theorem rpAlpha_power_generates_of_cellular_cup (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c)
    {k : ℕ} (hk : k ≤ n) (w : rpCohomology n k) :
    ∃ d : ZMod 2, d • cupPowZMod2 (actualRPAlpha n) k = w :=
  actualRPAlpha_power_generates n hn c cup hk w

/-- **The actual powers form a basis** of `Hᵏ(RPⁿ; F₂)` (`k ≤ n`), from the honest
inputs. -/
noncomputable def rpAlpha_power_basis_of_cellular_cup (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c)
    {k : ℕ} (hk : k ≤ n) : Module.Basis (Fin 1) (ZMod 2) (rpCohomology n k) :=
  actualRPAlpha_power_basis n hn c cup hk

/-! ## 3. The final odd-map assembly without a free generator identification

The most reduced final odd-map degree theorem `finalComparison_topPowerInput`
previously carried the RPⁿ-cohomology side as a single **free hypothesis**
`I : RPnGeneratorIdentification n`. Here we discharge it with the constructed term,
so the final entry point's RPⁿ-cohomology input is the honest data `(hn, c, cup)`
and `RPnGeneratorIdentification n` is no longer a root assumption of the final
theorem. -/

/-- **The final odd-map degree theorem, RPⁿ side constructed.**

```text
f odd  ⇒  Odd (degree f),
```

with the RPⁿ-cohomology side supplied by the **constructed**
`rpNGeneratorIdentification n hn c cup` rather than a free
`I : RPnGeneratorIdentification n`. The remaining hypotheses are the genuine
non-RPⁿ-cohomology branches (`e : SphereTopHomologyIso n`,
`hcmp : ModTwoTopClassComparison e`, `htr : RPnTopClassTransfer n`) together with
the honest RPⁿ inputs `1 ≤ n`, `c`, `cup`. -/
theorem finalComparison_topPowerInput_of_cellular_cup {n : ℕ}
    (e : SphereTopHomologyIso n) (hcmp : ModTwoTopClassComparison e)
    (hn : 1 ≤ n) (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c)
    (htr : RPnTopClassTransfer n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso e f) :=
  finalComparison_topPowerInput e hcmp (rpNGeneratorIdentification n hn c cup) htr f hf

/-- **`OddMapFixesTopClass n` from the honest inputs and the transfer**, with the
generator identification constructed rather than assumed. -/
theorem oddMapFixesTopClass_of_cellular_cup {n : ℕ} (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c)
    (htr : RPnTopClassTransfer n) :
    OddMapFixesTopClass n :=
  oddMapFixesTopClass_of_generatorIdentification (rpNGeneratorIdentification n hn c cup) htr

/-! ## 4. Final integration: the final theorem with no `RPnGeneratorIdentification`
assumption (Prompt 33)

The theorem below is the canonical final entry point of the third branch. It is
the final odd-map degree theorem

```text
f odd  ⇒  Odd (degree f)
```

with **no `RPnGeneratorIdentification n` hypothesis anywhere**: the entire
RPⁿ-cohomology generator identification is supplied internally by the constructed
term `rpNGeneratorIdentification n hn c cup`, and the load-bearing top-power
nonvanishing `αⁿ ≠ 0` is the actual theorem
`rpAlpha_actual_power_top_ne_zero_of_cellular_cup` threaded through the same
assembly. The only remaining hypotheses are the genuine *other* branches plus the
honest RPⁿ topological data:

* `e : SphereTopHomologyIso n` — integral top-homology identification (pins the
  integer degree); **sphere top homology** branch;
* `hcmp : ModTwoTopClassComparison e` — `F₂` degree comparison; **mod-two**
  branch;
* `htr : RPnTopClassTransfer n` — double-cover `F₂` transfer; **transfer/top-class
  bridge** branch;
* `1 ≤ n`, `c : RPnCellularCochainStructure n`, `cup : RPnCupProductStructure c`
  — the honest, Mathlib-absent RPⁿ inputs (cellular approximation and the
  cup-product computation).
-/

/-- **Final integration (Prompt 33): the final odd-map degree theorem with no
`RPnGeneratorIdentification n` assumption.**

```text
f odd  ⇒  Odd (degree f),
```

This is the canonical statement of `finalComparison_topPowerInput_of_cellular_cup`
under the closing name requested by the integration prompt: the third branch's
generator identification is no longer a free hypothesis, it is the constructed
term `rpNGeneratorIdentification n hn c cup`. The remaining assumptions are the
three genuine non-RPⁿ-cohomology branches (`e`, `hcmp`, `htr`) together with the
honest RPⁿ topological data (`1 ≤ n`, `c`, `cup`). -/
theorem finalComparison_without_RPnGeneratorIdentification {n : ℕ}
    (e : SphereTopHomologyIso n) (hcmp : ModTwoTopClassComparison e)
    (hn : 1 ≤ n) (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c)
    (htr : RPnTopClassTransfer n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso e f) :=
  finalComparison_topPowerInput_of_cellular_cup e hcmp hn c cup htr f hf

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

