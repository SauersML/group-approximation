import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCohomologyRingBridge
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.ConstructRPAlpha
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnAdditiveCohomology
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Identifying the cup-product generator of `RPⁿ`: actual `rpAlpha` and its powers

The classical mod-two cohomology ring of real projective space is

```text
H^*(RPⁿ; F₂) ≅ F₂[α] / (αⁿ⁺¹),   deg α = 1,
```

so that `1, α, α², …, αⁿ` is an `F₂`-basis with `αᵏ` generating `Hᵏ(RPⁿ; F₂)`.

The project already contains the two halves of this picture, both genuine:

* the **actual degree-one class** `rpAlpha n m : H¹(RPⁿ; F₂)`, constructed from a
  monodromy functional via the universal coefficient theorem over `F₂`
  (`ConstructRPAlpha.lean`), together with its cup powers
  `cupPowZMod2 (rpAlpha n m) k : Hᵏ(RPⁿ; F₂)`
  (`CohomologyCupProduct.lean`);
* the **algebraic model ring** `RPnCohomologyRingModel n = F₂[α]/(αⁿ⁺¹)` with its
  generator `modelAlpha n` and the model facts `αᵏ ≠ 0 ↔ k ≤ n`, `αⁿ⁺¹ = 0`,
  `dim = n+1` (`RPnCohomologyRingModel.lean`), plus the model-side ring bridge
  `RPnCohomologyToModelHom n` / `RPnCohomologyRingModelEmbedding n`
  (`RPnCohomologyRingBridge.lean`);
* the **additive computation** `Hᵏ(RPⁿ; F₂) ≅ F₂` (dimension one) for `k ≤ n`,
  conditional on the cellular-cochain hypothesis `RPnCellularCochainStructure n`
  (`RPnAdditiveCohomology.lean`).

This file is the **multiplicative bridge** between the actual class and the model
ring. It introduces the single, explicit, named *multiplicative identification*

```text
RPnGeneratorIdentification n :
  the actual rpAlpha n m  =  the model bridge's degree-one generator,
```

and derives, **stated entirely on the actual cohomology cup powers
`cupPowZMod2 (rpAlpha n m) k`**:

* `rpAlpha_eq_modelGenerator` / `rpAlpha_eq_cellularGenerator` — the bridge
  carries the actual `rpAlpha` to `modelAlpha n`;
* `rpAlpha_actual_power_ne_zero` / `rpAlpha_actual_power_top_ne_zero` — `αᵏ ≠ 0`
  for `k ≤ n`, in particular `αⁿ ≠ 0`, **with no extra model-identification
  assumption** beyond the named structure;
* `rpAlpha_actual_power_succ_eq_zero` / `rpAlpha_actual_power_eq_zero_iff` — the
  truncation `αⁿ⁺¹ = 0` and the full characterisation `αᵏ = 0 ↔ n+1 ≤ k` (given
  the injective embedding strengthening);
* `rpAlpha_power_generates` / `rpAlpha_power_ne_zero_of_additive_computation` /
  `rpAlpha_power_basis` — combined with the additive computation
  (`RPnCellularCochainStructure n`), each power `αᵏ` *spans* / *is a basis of* the
  one-dimensional group `Hᵏ(RPⁿ; F₂)` for `k ≤ n`.

The identification `RPnGeneratorIdentification n` is a genuine constraint (it
forces `toFun 1 (rpAlpha n m) = modelAlpha n ≠ 0`), so every theorem below is
non-vacuous; they are exactly conditional on the (still-open) multiplicative
identification of the actual `rpAlpha` with the model generator.

**No fake `α`, no fake cohomology ring, no fake ring isomorphism is asserted
unconditionally.** Everything is parameterised by the explicit named hypotheses.
-/

noncomputable section

open CategoryTheory AlgebraicTopology Module

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- **The multiplicative generator identification for `RPⁿ`.** This is the single,
explicit, named hypothesis connecting the *actual* degree-one cohomology class
`rpAlpha n monodromy` (built from monodromy via the universal coefficient theorem)
to the *model* degree-one generator `modelAlpha n`. It bundles:

* a monodromy functional `monodromy : MonodromyFunctional n`, which produces the
  genuine class `rpAlpha n monodromy ∈ H¹(RPⁿ; F₂)`;
* the model-side ring bridge `toModel : RPnCohomologyToModelHom n` (a graded ring
  homomorphism `H^*(RPⁿ; F₂) → F₂[α]/(αⁿ⁺¹)` carrying its chosen degree-one class
  to `modelAlpha n`);
* the **identification** `alpha_eq : toModel.alpha = rpAlpha n monodromy`, saying
  the bridge's chosen degree-one class is exactly the actual monodromy class.

This is precisely the multiplicative datum requested by the prompt: once it is
supplied, the powers of the *actual* `rpAlpha` inherit all the model-ring
properties (nonvanishing below the truncation, vanishing at and above it). -/
structure RPnGeneratorIdentification (n : ℕ) where
  /-- The monodromy functional producing the actual degree-one class. -/
  monodromy : MonodromyFunctional n
  /-- The model-side ring bridge. -/
  toModel : RPnCohomologyToModelHom n
  /-- The bridge's degree-one class is the actual monodromy class `rpAlpha n m`. -/
  alpha_eq : toModel.alpha = rpAlpha n monodromy

namespace RPnGeneratorIdentification

variable {n : ℕ}

/-- The actual degree-one class identified by `I`. -/
def alphaClass (I : RPnGeneratorIdentification n) : rpCohomology n 1 :=
  rpAlpha n I.monodromy

@[simp] theorem alphaClass_eq (I : RPnGeneratorIdentification n) :
    I.alphaClass = rpAlpha n I.monodromy := rfl

end RPnGeneratorIdentification

/-- **The actual `rpAlpha` is the model degree-one generator.** Under the
identification `I`, the model bridge carries the genuine monodromy class
`rpAlpha n I.monodromy` to `modelAlpha n`. -/
theorem rpAlpha_eq_modelGenerator {n : ℕ} (I : RPnGeneratorIdentification n) :
    I.toModel.toFun 1 (rpAlpha n I.monodromy) = modelAlpha n := by
  rw [← I.alpha_eq]; exact I.toModel.alpha_spec

/-- Alias of `rpAlpha_eq_modelGenerator`: the actual `rpAlpha` is carried to the
model (cellular) degree-one generator `modelAlpha n`. -/
theorem rpAlpha_eq_cellularGenerator {n : ℕ} (I : RPnGeneratorIdentification n) :
    I.toModel.toFun 1 (rpAlpha n I.monodromy) = modelAlpha n :=
  rpAlpha_eq_modelGenerator I

/-- The bridge carries the `k`-th cup power of the actual `rpAlpha` to
`modelAlpha n ^ k`. -/
theorem rpAlpha_cupPow_eq_modelPow {n : ℕ} (I : RPnGeneratorIdentification n) (k : ℕ) :
    I.toModel.toFun k (cupPowZMod2 (rpAlpha n I.monodromy) k) = modelAlpha n ^ k := by
  rw [← I.alpha_eq]; exact I.toModel.map_cupPow k

/-- **Sub-truncation nonvanishing for the actual class.** Under the multiplicative
identification `I`, the `k`-th cup power of the genuine `rpAlpha n I.monodromy` is
nonzero in `Hᵏ(RPⁿ; F₂)` for every `k ≤ n` — with no extra model-identification
assumption. -/
theorem rpAlpha_actual_power_ne_zero {n : ℕ} (I : RPnGeneratorIdentification n)
    {k : ℕ} (hk : k ≤ n) : cupPowZMod2 (rpAlpha n I.monodromy) k ≠ 0 := by
  rw [← I.alpha_eq]; exact rpAlpha_power_ne_zero I.toModel hk

/-- **Top-class nonvanishing for the actual class** — the load-bearing
`αⁿ ≠ 0` in the genuine `Hⁿ(RPⁿ; F₂)`, depending only on the named identification
`I`. This is exactly the input a downstream top-class argument needs. -/
theorem rpAlpha_actual_power_top_ne_zero {n : ℕ} (I : RPnGeneratorIdentification n) :
    cupPowZMod2 (rpAlpha n I.monodromy) n ≠ 0 :=
  rpAlpha_actual_power_ne_zero I le_rfl

/-- **The full multiplicative generator identification (with injectivity).** This
strengthens `RPnGeneratorIdentification` by requiring the model bridge to be a
graded ring *embedding* (`RPnCohomologyRingModelEmbedding n`, injective in every
degree). It pins the truncation relation `αⁿ⁺¹ = 0` of the actual class as well as
the nonvanishing. -/
structure RPnGeneratorIdentificationEmbedding (n : ℕ) where
  /-- The monodromy functional producing the actual degree-one class. -/
  monodromy : MonodromyFunctional n
  /-- The model-side ring embedding (injective graded ring homomorphism). -/
  toModel : RPnCohomologyRingModelEmbedding n
  /-- The embedding's degree-one class is the actual monodromy class. -/
  alpha_eq : toModel.alpha = rpAlpha n monodromy

namespace RPnGeneratorIdentificationEmbedding

variable {n : ℕ}

/-- The underlying (non-injective) generator identification. -/
def toIdentification (E : RPnGeneratorIdentificationEmbedding n) :
    RPnGeneratorIdentification n :=
  { monodromy := E.monodromy
    toModel := E.toModel.toRPnCohomologyToModelHom
    alpha_eq := E.alpha_eq }

end RPnGeneratorIdentificationEmbedding

/-- **Truncation relation for the actual class.** Under the injective
identification `E`, the `(n+1)`-st cup power of the genuine `rpAlpha` vanishes:
`αⁿ⁺¹ = 0` in `Hⁿ⁺¹(RPⁿ; F₂)`. -/
theorem rpAlpha_actual_power_succ_eq_zero {n : ℕ}
    (E : RPnGeneratorIdentificationEmbedding n) :
    cupPowZMod2 (rpAlpha n E.monodromy) (n + 1) = 0 := by
  rw [← E.alpha_eq]; exact rpAlpha_power_succ_eq_zero E.toModel

/-- **Full power-vanishing characterisation for the actual class.** Under the
injective identification `E`, the cup power `αᵏ` vanishes in `Hᵏ(RPⁿ; F₂)` exactly
at and beyond the truncation bound: `αᵏ = 0 ↔ n+1 ≤ k`. -/
theorem rpAlpha_actual_power_eq_zero_iff {n : ℕ}
    (E : RPnGeneratorIdentificationEmbedding n) (k : ℕ) :
    cupPowZMod2 (rpAlpha n E.monodromy) k = 0 ↔ n + 1 ≤ k := by
  rw [← E.alpha_eq]; exact rpAlpha_power_eq_zero_iff E.toModel k

/-! ## Powers generate the additive cohomology groups

Combining the multiplicative identification with the additive computation
(`RPnCellularCochainStructure n`, giving `dim Hᵏ(RPⁿ; F₂) = 1` for `k ≤ n`),
each nonzero power `αᵏ` spans, hence is a basis of, the one-dimensional group
`Hᵏ(RPⁿ; F₂)`. -/

/-- **The additive cellular computation of `RPⁿ` together with the generator
identification.** Bundles the multiplicative identification of the actual
`rpAlpha` with the cellular-cochain hypothesis that computes the additive groups
`Hᵏ(RPⁿ; F₂) ≅ F₂` (dimension one) for `k ≤ n`. From it, the powers of the actual
`rpAlpha` generate the cohomology groups. -/
structure RPnGeneratorIdentificationWithAdditive (n : ℕ) where
  /-- The multiplicative generator identification. -/
  identification : RPnGeneratorIdentification n
  /-- The cellular-cochain hypothesis computing the additive groups. -/
  cochain : RPnCellularCochainStructure n

namespace RPnGeneratorIdentificationWithAdditive

variable {n : ℕ}

/-- The actual degree-one class. -/
def alphaClass (J : RPnGeneratorIdentificationWithAdditive n) : rpCohomology n 1 :=
  rpAlpha n J.identification.monodromy

end RPnGeneratorIdentificationWithAdditive

/-- **The powers of the actual `rpAlpha` are nonzero (from the additive
computation).** For `k ≤ n` the cup power `αᵏ` is a nonzero class in
`Hᵏ(RPⁿ; F₂)`. (Restatement of `rpAlpha_actual_power_ne_zero` for the bundled
data, emphasising the role of the additive computation in the generation results
below.) -/
theorem rpAlpha_power_ne_zero_of_additive_computation {n : ℕ}
    (J : RPnGeneratorIdentificationWithAdditive n) {k : ℕ} (hk : k ≤ n) :
    cupPowZMod2 (rpAlpha n J.identification.monodromy) k ≠ 0 :=
  rpAlpha_actual_power_ne_zero J.identification hk

section Generation

set_option maxHeartbeats 1000000

variable {n : ℕ}

/-- The additive computation `Hᵏ(RPⁿ; F₂) ≅ F₂` (`k ≤ n`) as a linear equivalence to
the honest field `ZMod 2`. -/
noncomputable def rpCohomologyAddEquiv (J : RPnGeneratorIdentificationWithAdditive n)
    {k : ℕ} (hk : k ≤ n) : rpCohomology n k ≃ₗ[ZMod 2] ZMod 2 :=
  (rpModTwoCohomologyAdditive J.cochain k hk).toLinearEquiv

/-- Under the additive iso, the `k`-th power of the actual `rpAlpha` is sent to a
nonzero scalar. -/
theorem rpCohomologyAddEquiv_power_ne_zero (J : RPnGeneratorIdentificationWithAdditive n)
    {k : ℕ} (hk : k ≤ n) :
    rpCohomologyAddEquiv J hk (cupPowZMod2 (rpAlpha n J.identification.monodromy) k) ≠ 0 := by
  simp only [rpCohomologyAddEquiv, ne_eq, EmbeddingLike.map_eq_zero_iff]
  exact rpAlpha_power_ne_zero_of_additive_computation J hk

/-- Under the additive iso, the `k`-th power of the actual `rpAlpha` is sent to `1`
(the unique nonzero element of `F₂`). -/
theorem rpCohomologyAddEquiv_power_eq_one (J : RPnGeneratorIdentificationWithAdditive n)
    {k : ℕ} (hk : k ≤ n) :
    rpCohomologyAddEquiv J hk (cupPowZMod2 (rpAlpha n J.identification.monodromy) k) = 1 := by
  have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  exact key _ (rpCohomologyAddEquiv_power_ne_zero J hk)

/-- **The powers generate the cohomology groups.** For `k ≤ n`, every class in
`Hᵏ(RPⁿ; F₂)` is an `F₂`-multiple of the single cup power `αᵏ`:

```text
∀ w ∈ Hᵏ(RPⁿ; F₂), ∃ c : F₂, c • αᵏ = w.
```

This holds because `Hᵏ(RPⁿ; F₂) ≅ F₂` is one-dimensional (additive computation) and
`αᵏ ≠ 0` (multiplicative identification): the additive iso sends `αᵏ` to a nonzero
scalar, which is a unit in the field `F₂`. -/
theorem rpAlpha_power_generates (J : RPnGeneratorIdentificationWithAdditive n)
    {k : ℕ} (hk : k ≤ n) (w : rpCohomology n k) :
    ∃ c : ZMod 2, c • cupPowZMod2 (rpAlpha n J.identification.monodromy) k = w := by
  refine ⟨rpCohomologyAddEquiv J hk w, ?_⟩
  apply (rpCohomologyAddEquiv J hk).injective
  rw [map_smul, rpCohomologyAddEquiv_power_eq_one J hk, smul_eq_mul, mul_one]

/-- **The powers span the cohomology groups.** For `k ≤ n`, the singleton `{αᵏ}`
spans `Hᵏ(RPⁿ; F₂)` over `F₂`. -/
theorem rpAlpha_power_span_eq_top (J : RPnGeneratorIdentificationWithAdditive n)
    {k : ℕ} (hk : k ≤ n) :
    Submodule.span (ZMod 2) {cupPowZMod2 (rpAlpha n J.identification.monodromy) k} = ⊤ := by
  rw [eq_top_iff]
  intro w _
  rw [Submodule.mem_span_singleton]
  exact rpAlpha_power_generates J hk w

/-- **The powers form a basis.** For `k ≤ n`, the single cup power `αᵏ` is an
`F₂`-basis of the one-dimensional group `Hᵏ(RPⁿ; F₂)`. -/
noncomputable def rpAlpha_power_basis (J : RPnGeneratorIdentificationWithAdditive n)
    {k : ℕ} (hk : k ≤ n) : Module.Basis (Fin 1) (ZMod 2) (rpCohomology n k) :=
  (Module.Basis.singleton (Fin 1) (ZMod 2)).map (rpCohomologyAddEquiv J hk).symm

/-- **The basis vector is exactly the cup power `αᵏ`.** -/
@[simp] theorem rpAlpha_power_basis_apply (J : RPnGeneratorIdentificationWithAdditive n)
    {k : ℕ} (hk : k ≤ n) (i : Fin 1) :
    rpAlpha_power_basis J hk i = cupPowZMod2 (rpAlpha n J.identification.monodromy) k := by
  rw [rpAlpha_power_basis, Module.Basis.map_apply, Module.Basis.singleton_apply,
    ← rpCohomologyAddEquiv_power_eq_one J hk, LinearEquiv.symm_apply_apply]

end Generation

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
