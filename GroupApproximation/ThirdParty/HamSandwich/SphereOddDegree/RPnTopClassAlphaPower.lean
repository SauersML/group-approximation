import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCohomologyRingModel
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.InducedOnRPCohomology

/-!
# The `RPⁿ` top class and the nonvanishing of `αⁿ`

The classical mod-two cohomology-ring computation

```text
H^*(RPⁿ; F₂) ≅ F₂[α] / (αⁿ⁺¹),   deg α = 1,
```

has as its load-bearing consequence the **top-class nonvanishing**

```text
αⁿ ≠ 0   in   Hⁿ(RPⁿ; F₂),
```

with `αⁿ` the (nonzero) top class of `RPⁿ`. This file assembles the largest
build-clean layer toward that statement that the current project API supports,
*without faking* `α`, `αⁿ`, the cup product, the top class, or the topological
cohomology ring `H^*(RPⁿ; F₂)` (policy: `Axioms_And_Placeholders.md`).

What is genuine and present in the project today:

* the genuine **algebraic model ring** `RPnCohomologyRingModel n = F₂[α]/(αⁿ⁺¹)`
  with its generator `modelAlpha n` and the proven facts `αⁿ⁺¹ = 0`, `αⁿ ≠ 0`,
  `αᵏ = 0 ↔ n+1 ≤ k`, `dim_F₂ = n+1` (`RPnCohomologyRingModel.lean`);
* the genuine **cohomology functor** and the genuine topological cohomology
  objects `rpCohomology n k = Hᵏ(RPⁿ; F₂)` (`InducedOnRPCohomology.lean`);
* the genuine **cochain-level cup product / powers** `cochainCup`, `cochainPow`
  and their naturality / fixed-point lemmas (`CupProduct.lean`,
  `CupProductPowers.lean`).

What remains genuinely **absent** (and is *not* faked here): the cohomology-level
cup product (gated on the Leibniz/coboundary identity), the degree-one class
`α ∈ H¹(RPⁿ; F₂)` (gated on the degree-one universal coefficient theorem), and the
ring isomorphism `H^*(RPⁿ; F₂) ≅ F₂[α]/(αⁿ⁺¹)` (gated additionally on the
LES/Mayer–Vietoris induction). See
`docs/current/RPn_Top_Class_Alpha_Power_Nonvanishing_Result.md` for the exact
dependency DAG.

## What this file adds (all fully proved, build-clean)

1. **Top-degree target abbreviations.** `rpTopCohomology n = Hⁿ(RPⁿ; F₂)`,
   `sphereTopCohomology n = Hⁿ(Sⁿ; F₂)`, and the top-degree pullback
   `rpTopPullback f hf` of a descended odd map.
2. **The model top class.** `modelTopClass n = αⁿ` in the model ring, with
   `modelTopClass_ne_zero` (the model-side `αⁿ ≠ 0`) and the annihilation
   `α · αⁿ = 0`. A `Nontrivial` instance on the model ring.
3. **Cup-power notation.** Scoped notation `φ ^⌣ n` for the cochain cup power
   `cochainPow φ n`.
4. **Conditional nonvanishing interfaces.** If a ring map (resp. ring
   isomorphism) carries a candidate class `a` to `modelAlpha n`, then `aᵏ ≠ 0`
   for `k ≤ n` (resp. `aᵏ = 0 ↔ n+1 ≤ k`). These are exactly the interfaces the
   full computation plugs into: once `H^*(RPⁿ; F₂) ≅ F₂[α]/(αⁿ⁺¹)` is supplied,
   `αⁿ ≠ 0` and the truncation transport verbatim.
5. **Low-dimensional cases.** The `n = 0` and `n = 1` instances on the model
   side: `modelAlpha 0 = 0` but `α⁰ = 1 ≠ 0` (the `H⁰` top class), and
   `modelAlpha 1 ≠ 0`, `α² = 0` for `RP¹`.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## 1. Top-degree target abbreviations -/

/-- The **top mod-two cohomology** `Hⁿ(RPⁿ; F₂)` of real projective `n`-space, the
target group of the top class `αⁿ`. A genuine object: `rpCohomology n n`. -/
noncomputable def rpTopCohomology (n : ℕ) : ModuleCat.{0} (ZMod 2) := rpCohomology n n

/-- The **top mod-two cohomology** `Hⁿ(Sⁿ; F₂)` of the `n`-sphere. -/
noncomputable def sphereTopCohomology (n : ℕ) : ModuleCat.{0} (ZMod 2) := sphereCohomology n n

theorem rpTopCohomology_eq (n : ℕ) : rpTopCohomology n = rpCohomology n n := rfl

theorem sphereTopCohomology_eq (n : ℕ) : sphereTopCohomology n = sphereCohomology n n := rfl

/-- The **top-degree pullback** `fbar^* : Hⁿ(RPⁿ; F₂) → Hⁿ(RPⁿ; F₂)` of the
descended odd map `fbar = inducedOnRP f hf`. This is the endomorphism whose
triviality (`= id`) on the nonzero top class `αⁿ` would yield `degree f ≡ 1 mod 2`
in the final theorem. -/
noncomputable def rpTopPullback {n : ℕ} (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    rpTopCohomology n ⟶ rpTopCohomology n :=
  inducedOnRPPullback f hf n

@[simp] theorem rpTopPullback_id (n : ℕ) :
    rpTopPullback (ContinuousMap.id (Sphere n)) (isOddMap_id n) = 𝟙 (rpTopCohomology n) :=
  inducedOnRPPullback_id n n

/-- The descended antipodal map acts as the identity on the top cohomology. -/
@[simp] theorem rpTopPullback_antipodal (n : ℕ) :
    rpTopPullback (antipodal n) (isOddMap_antipodal n) = 𝟙 (rpTopCohomology n) :=
  inducedOnRPPullback_antipodal n n

/-! ## 2. The model top class -/

/-- The model ring `F₂[α]/(αⁿ⁺¹)` is nontrivial (it has the nonzero element
`αⁿ`). -/
instance (n : ℕ) : Nontrivial (RPnCohomologyRingModel n) :=
  nontrivial_of_ne _ _ (modelAlpha_pow_top_ne_zero n)

/-- The **model top class** `αⁿ ∈ F₂[α]/(αⁿ⁺¹)` — the model-side avatar of the
top class of `Hⁿ(RPⁿ; F₂)`. -/
noncomputable def modelTopClass (n : ℕ) : RPnCohomologyRingModel n := modelAlpha n ^ n

theorem modelTopClass_eq (n : ℕ) : modelTopClass n = modelAlpha n ^ n := rfl

/-- **The model top class is nonzero** — the model-side form of `αⁿ ≠ 0`. -/
theorem modelTopClass_ne_zero (n : ℕ) : modelTopClass n ≠ 0 :=
  modelAlpha_pow_top_ne_zero n

/-- The generator annihilates the top class: `α · αⁿ = αⁿ⁺¹ = 0`. -/
theorem modelAlpha_mul_modelTopClass (n : ℕ) :
    modelAlpha n * modelTopClass n = 0 := by
  rw [modelTopClass_eq, ← pow_succ', modelAlpha_pow_succ_eq_zero]

/-! ## 3. Cup-power notation -/

/-- Notation `φ ^⌣ n` for the `n`-th cochain cup power `cochainPow φ n` of a
degree-one cochain. -/
scoped notation:75 φ:75 " ^⌣ " n:76 => cochainPow φ n

/-! ## 4. Conditional nonvanishing interfaces

These are the honest interfaces the full computation plugs into. None of them
assert nonvanishing in `Hⁿ(RPⁿ; F₂)` unconditionally; each derives it from a
*hypothesised* ring map / isomorphism matching the algebraic model. Once the
(still missing) ring isomorphism `H^*(RPⁿ; F₂) ≅ F₂[α]/(αⁿ⁺¹)` is supplied, these
yield `αⁿ ≠ 0` and the truncation `αᵏ = 0 ↔ n+1 ≤ k` verbatim. -/

/-- **Conditional sub-truncation nonvanishing.** If a ring homomorphism `Φ` from a
commutative ring `R` to the model `F₂[α]/(αⁿ⁺¹)` carries `a : R` to the model
generator `modelAlpha n`, then `aᵏ ≠ 0` for every `k ≤ n`. (No injectivity of `Φ`
is needed: the image `Φ(aᵏ) = αᵏ` is already nonzero.) -/
theorem pow_ne_zero_of_ringHom_modelAlpha {R : Type*} [CommRing R] {n : ℕ}
    (Φ : R →+* RPnCohomologyRingModel n) {a : R} (ha : Φ a = modelAlpha n)
    {k : ℕ} (hk : k ≤ n) : a ^ k ≠ 0 := by
  intro h
  apply modelAlpha_pow_ne_zero n k hk
  rw [← ha, ← map_pow, h, map_zero]

/-- **Conditional top-power nonvanishing** — the conditional `αⁿ ≠ 0`. If a ring
homomorphism carries `a` to `modelAlpha n`, then `aⁿ ≠ 0`. -/
theorem pow_top_ne_zero_of_ringHom_modelAlpha {R : Type*} [CommRing R] {n : ℕ}
    (Φ : R →+* RPnCohomologyRingModel n) {a : R} (ha : Φ a = modelAlpha n) :
    a ^ n ≠ 0 :=
  pow_ne_zero_of_ringHom_modelAlpha Φ ha le_rfl

/-- **Conditional power-vanishing characterization.** If a ring *isomorphism*
carries `a` to `modelAlpha n`, then `aᵏ = 0 ↔ n+1 ≤ k`: exactly the powers below
the truncation bound are nonzero. -/
theorem pow_eq_zero_iff_of_ringEquiv {R : Type*} [CommRing R] {n : ℕ}
    (e : R ≃+* RPnCohomologyRingModel n) {a : R} (ha : e a = modelAlpha n) (k : ℕ) :
    a ^ k = 0 ↔ n + 1 ≤ k := by
  rw [← map_eq_zero_iff e e.injective, map_pow, ha, modelAlpha_pow_eq_zero_iff]

/-- **Conditional truncation relation.** If a ring isomorphism carries `a` to
`modelAlpha n`, then `aⁿ⁺¹ = 0`. -/
theorem pow_succ_eq_zero_of_ringEquiv {R : Type*} [CommRing R] {n : ℕ}
    (e : R ≃+* RPnCohomologyRingModel n) {a : R} (ha : e a = modelAlpha n) :
    a ^ (n + 1) = 0 :=
  (pow_eq_zero_iff_of_ringEquiv e ha (n + 1)).2 le_rfl

/-- **Conditional top-power nonvanishing, isomorphism form.** -/
theorem pow_top_ne_zero_of_ringEquiv {R : Type*} [CommRing R] {n : ℕ}
    (e : R ≃+* RPnCohomologyRingModel n) {a : R} (ha : e a = modelAlpha n) :
    a ^ n ≠ 0 := by
  rw [Ne, pow_eq_zero_iff_of_ringEquiv e ha]; omega

/-! ## 5. Low-dimensional cases (model side) -/

/-- For `RP⁰` the generator itself is zero: `modelAlpha 0 = 0` (the model ring is
`F₂[α]/(α) ≅ F₂`). -/
@[simp] theorem modelAlpha_zero_eq_zero : modelAlpha 0 = 0 := by
  have := modelAlpha_pow_succ_eq_zero 0
  simpa using this

/-- For `RP⁰` the top class is the unit: `α⁰ = 1`, and it is nonzero — the genuine
`H⁰` top class on the model side. -/
@[simp] theorem modelTopClass_zero : modelTopClass 0 = 1 := pow_zero _

theorem modelTopClass_zero_ne_zero : modelTopClass 0 ≠ 0 := modelTopClass_ne_zero 0

/-- For `RP¹` the generator is nonzero: `α ≠ 0`. -/
theorem modelAlpha_one_ne_zero : modelAlpha 1 ≠ 0 := by
  have := modelAlpha_pow_top_ne_zero 1
  simpa using this

/-- For `RP¹` the top class is `α` itself. -/
@[simp] theorem modelTopClass_one : modelTopClass 1 = modelAlpha 1 := pow_one _

/-- For `RP¹` the square of the generator vanishes: `α² = 0`. -/
theorem modelAlpha_one_sq_eq_zero : modelAlpha 1 ^ 2 = 0 :=
  modelAlpha_pow_succ_eq_zero 1

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
