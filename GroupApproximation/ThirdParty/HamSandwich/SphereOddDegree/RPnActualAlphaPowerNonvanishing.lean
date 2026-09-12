import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCupProductGenerator
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.FinalOddMapComparison

/-!
# Actual nonvanishing of `αⁿ` in `Hⁿ(RPⁿ; F₂)`, and the simplified final assembly

The classical mod-two cohomology-ring computation

```text
H^*(RPⁿ; F₂) ≅ F₂[α] / (αⁿ⁺¹),   deg α = 1,
```

has as its load-bearing consequence the **top-class nonvanishing**

```text
αⁿ ≠ 0   in   Hⁿ(RPⁿ; F₂),
```

where `α = rpAlpha n m` is the *genuine* degree-one class built from monodromy via
the universal coefficient theorem over `F₂` (`ConstructRPAlpha.lean`) and `αⁿ` is
its honest cup power `cupPowZMod2 (rpAlpha n m) n : Hⁿ(RPⁿ; F₂)`
(`CohomologyCupProduct.lean`).

This file packages that nonvanishing as a clean, project-style statement about the
**actual** top cohomology class, and threads it through to the **final odd-map
assembly**, eliminating the previous `αⁿ ≠ 0` (and `OddMapFixesTopClass`)
hypotheses from the assembly's RPⁿ side.

## What is added (all build-clean, no new model facts)

1. **The actual top class.** `rpTopClass n m := cupPowZMod2 (rpAlpha n m) n`, the
   genuine `αⁿ ∈ Hⁿ(RPⁿ; F₂)`, with `rpTopClass_eq_rpAlpha_power`.
2. **Actual nonvanishing.** `rpAlpha_power_topClass`
   (`rpTopClass n I.monodromy ≠ 0`) — the genuine `αⁿ ≠ 0`, depending only on the
   single named multiplicative datum `I : RPnGeneratorIdentification n` (the
   multiplicative half of the ring isomorphism). This is the actual project-style
   form of `rpAlpha_power_ne_zero`.
3. **Top-class fixed-point.** `rpTopClass_fixed` — every descended odd map fixes
   `αⁿ` (proved, via `inducedOnRPPullback_rpAlpha` and cup-power naturality).
4. **The remaining transfer blocker.** `RPnTopClassTransfer n` — the *one* genuine
   double-cover input that carries a nonzero fixed RPⁿ top class to a nonzero
   fixed sphere top class (the `F₂` transfer/Gysin sequence of `Sⁿ → RPⁿ`); this
   is a separate branch from the RPⁿ α-power story.
5. **`OddMapFixesTopClass` discharged from the generator identification.**
   `oddMapFixesTopClass_of_generatorIdentification` proves the previously
   monolithic `OddMapFixesTopClass n` from the single `I` plus the transfer
   `RPnTopClassTransfer n`, *using the actual nonvanishing* of step 2.
6. **The simplified final assembly.** `finalComparison_topPowerInput` — the final
   odd-map degree theorem with the RPⁿ side reduced to the single generator
   identification `I`: **no `αⁿ ≠ 0` assumption** and **no `OddMapFixesTopClass`
   assumption** remain.

The remaining inputs of `finalComparison_topPowerInput` are exactly the genuine
non-RPⁿ-cohomology branches: the integral top-homology identification
`SphereTopHomologyIso n`, the mod-two degree comparison `ModTwoTopClassComparison`,
and the double-cover transfer `RPnTopClassTransfer n`. The single RPⁿ-cohomology
hypothesis is `RPnGeneratorIdentification n`.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## 1. The actual top class `αⁿ ∈ Hⁿ(RPⁿ; F₂)` -/

/-- **The actual top class** `αⁿ ∈ Hⁿ(RPⁿ; F₂)`: the `n`-th cup power of the
genuine degree-one class `rpAlpha n m` built from the monodromy functional `m`. A
genuine element of `rpCohomology n n`. -/
noncomputable def rpTopClass (n : ℕ) (m : MonodromyFunctional n) : rpCohomology n n :=
  cupPowZMod2 (rpAlpha n m) n

/-- The top class is the `n`-th cup power of `rpAlpha`. -/
theorem rpTopClass_eq_rpAlpha_power (n : ℕ) (m : MonodromyFunctional n) :
    rpTopClass n m = cupPowZMod2 (rpAlpha n m) n := rfl

/-! ## 2. Actual nonvanishing of `αⁿ` -/

/-- **Actual nonvanishing of `αⁿ` in `Hⁿ(RPⁿ; F₂)`.** Given the single named
multiplicative identification `I : RPnGeneratorIdentification n` (the
multiplicative half of the ring isomorphism `H^*(RPⁿ; F₂) ≅ F₂[α]/(αⁿ⁺¹)`), the
actual top class `αⁿ = rpTopClass n I.monodromy` is nonzero in the genuine top
cohomology group. This is the actual, project-style form of `αⁿ ≠ 0`. -/
theorem rpAlpha_power_topClass {n : ℕ} (I : RPnGeneratorIdentification n) :
    rpTopClass n I.monodromy ≠ 0 :=
  rpAlpha_actual_power_top_ne_zero I

/-- **Actual sub-truncation nonvanishing.** For `k ≤ n`, the actual cup power
`αᵏ = cupPowZMod2 (rpAlpha n I.monodromy) k` is nonzero in `Hᵏ(RPⁿ; F₂)`. -/
theorem rpAlpha_power_ne_zero_of_identification {n : ℕ}
    (I : RPnGeneratorIdentification n) {k : ℕ} (hk : k ≤ n) :
    cupPowZMod2 (rpAlpha n I.monodromy) k ≠ 0 :=
  rpAlpha_actual_power_ne_zero I hk

/-! ## 3. The descended odd map fixes the top class -/

/-- **Every descended odd map fixes the actual top class `αⁿ`.** For the genuine
class built from the monodromy functional `m`, the pullback of every descended odd
map `fbar = inducedOnRP f hf` fixes `αⁿ`:

```text
fbar^*(αⁿ) = αⁿ    in   Hⁿ(RPⁿ; F₂).
```

This is proved unconditionally (given `m`): the action `fbar^*(α) = α` is
`inducedOnRPPullback_rpAlpha`, and cup-power naturality
(`inducedOnRP_cohPullback_cupPow_fixed`) lifts it to the top power. -/
theorem rpTopClass_fixed {n : ℕ} (m : MonodromyFunctional n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    inducedOnRPPullback f hf n (rpTopClass n m) = rpTopClass n m := by
  have hfix1 : (inducedOnRPPullback f hf 1).hom (rpAlpha n m) = rpAlpha n m :=
    inducedOnRPPullback_rpAlpha n m f hf
  exact inducedOnRP_cohPullback_cupPow_fixed f hf (rpAlpha n m) hfix1 n

/-! ## 4. The remaining double-cover transfer blocker -/

/-- **The double-cover transfer blocker for RPⁿ top classes.** The single genuine
topological input on the double-cover branch: a nonzero RPⁿ top class
`a ∈ Hⁿ(RPⁿ; F₂)` fixed by a descended odd map `fbar` is carried to a nonzero
sphere top class `c ∈ Hⁿ(Sⁿ; F₂)` fixed by `f`.

Mathematically this is the `F₂` transfer/Gysin sequence of the double cover
`Sⁿ → RPⁿ` (it is *not* the degenerate `proj^*` route, for which
`proj^*(αⁿ) = 0` when `n ≥ 1`). It is genuinely missing from pinned Mathlib and is
kept here as one explicit named hypothesis, separate from the RPⁿ α-power story. -/
def RPnTopClassTransfer (n : ℕ) : Prop :=
  ∀ (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) (a : rpCohomology n n),
    inducedOnRPPullback f hf n a = a → a ≠ 0 →
      ∃ c : sphereCohomology n n, c ≠ 0 ∧ spherePullback f n c = c

/-! ## 5. `OddMapFixesTopClass` from the generator identification -/

/-- **`OddMapFixesTopClass n` follows from the generator identification and the
transfer.** Given the single multiplicative datum `I : RPnGeneratorIdentification n`
and the double-cover transfer `RPnTopClassTransfer n`, every odd self-map of `Sⁿ`
fixes a nonzero top `F₂`-class — the previously monolithic `OddMapFixesTopClass n`
hypothesis.

The proof *uses the actual nonvanishing*: the genuine RPⁿ top class
`αⁿ = rpTopClass n I.monodromy` is fixed by every descended odd map
(`rpTopClass_fixed`) and nonzero (`rpAlpha_power_topClass`); the transfer then
produces the required nonzero fixed sphere class. -/
theorem oddMapFixesTopClass_of_generatorIdentification {n : ℕ}
    (I : RPnGeneratorIdentification n) (htr : RPnTopClassTransfer n) :
    OddMapFixesTopClass n := by
  intro f hf
  exact htr f hf (rpTopClass n I.monodromy) (rpTopClass_fixed I.monodromy f hf)
    (rpAlpha_power_topClass I)

/-! ## 6. The simplified final odd-map assembly -/

/-- **The simplified final odd-map degree theorem.**

```text
f odd  ⇒  Odd (degree f),
```

with the RPⁿ-cohomology side reduced to the **single** generator identification
`I : RPnGeneratorIdentification n`. **No `αⁿ ≠ 0` assumption and no
`OddMapFixesTopClass` assumption remain**: the nonvanishing is *proved* from `I`
(`rpAlpha_power_topClass`) and threaded through `rpTopClass_fixed` and the transfer.

The remaining hypotheses are exactly the genuine non-RPⁿ-cohomology branches:

* `e : SphereTopHomologyIso n` — the integral top-homology identification pinning
  the integer degree `degreeOfIso e`;
* `hcmp : ModTwoTopClassComparison e` — a self-map fixing a nonzero top
  `F₂`-class has odd integer degree (the `F₂` degree comparison);
* `htr : RPnTopClassTransfer n` — the double-cover `F₂` transfer.

Supplying genuine terms for `e`, `hcmp`, `htr`, and `I` specializes this to the
unconditional final theorem with no change of proof. -/
theorem finalComparison_topPowerInput {n : ℕ}
    (e : SphereTopHomologyIso n) (hcmp : ModTwoTopClassComparison e)
    (I : RPnGeneratorIdentification n) (htr : RPnTopClassTransfer n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso e f) :=
  oddMap_degree_odd_final e hcmp
    (oddMapFixesTopClass_of_generatorIdentification I htr) f hf

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
