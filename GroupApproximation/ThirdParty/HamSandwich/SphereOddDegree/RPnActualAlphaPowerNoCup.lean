import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnGysinConnectingCup
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnGysinConnectingInjectiveLt
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPAlphaEqualsModelGenerator

/-!
# Unconditional nonvanishing of the powers of the actual class `α = actualRPAlpha`

This file proves, **without** any of the cup-product / cellular / generator
structures (`RPnCupProductStructure`, `RPnGeneratorIdentification`,
`RPnMultiplicativeCellularCochainStructure`,
`RPnSingularCellularCupComparison`), that the cup powers of the canonical
double-cover class `α = actualRPAlpha n ∈ H¹(RPⁿ; F₂)` are nonzero in the whole
range `1 ≤ k ≤ n`:

```text
cupPowZMod2 (actualRPAlpha n) k ≠ 0        (1 ≤ k ≤ n).
```

## Proof

By induction on `k`, using the Smith/Gysin machinery:

* **Base case** `k = 1`: `α¹ = α`, nonzero by `actualRPAlpha_ne_zero`.
* **Step** `k → k + 1` (for `1 ≤ k < n`):
  `αᵏ⁺¹ = αᵏ ⌣ α = δ(αᵏ)` where `δ = rpGysinConnecting n k` is the Smith/Gysin
  connecting map (`rpGysinConnecting_eq_cup_actualRPAlpha`).  If `αᵏ⁺¹ = 0` then
  `δ(αᵏ) = 0`, and injectivity of `δ` in degree `k` (`0 < k < n`,
  `rpGysinConnecting_injective_of_lt`) forces `αᵏ = 0`, contradicting the
  induction hypothesis.
-/

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

open AlexanderWhitney

/-
The back `1`-face of a `1`-simplex, with empty front part, is the simplex
itself (`backFace 0 1` is the identity).
-/
theorem backSimplex_zero_one {X : TopCat.{0}} (σ : singularSimplices X (0 + 1)) :
    backSimplex X 0 1 σ = σ := by
  -- By definition of `back Face`, we know that `back Face 0 1` is the identity function.
  have h_back_Face_id : backFace 0 1 = 𝟙 (SimplexCategory.mk 1) :=
    SimplexCategory.Hom.ext_one_left (backFace 0 1) (𝟙 (SimplexCategory.mk 1)) rfl rfl
  simp [backSimplex, h_back_Face_id]

/-
Left unitality of the cochain cup in the degree `(0, 1)` case:
`1 ⌣ φ = φ`.
-/
theorem cochainCup_one_left {X : TopCat.{0}} (φ : singularCochainGroup (ZMod 2) X 1) :
    cochainCup 0 1 (cochainOne (R := ZMod 2) (Z := X)) φ = φ := by
  apply cochain_ext;
  intro τ;
  rw [ cochainCup_eval ];
  rw [ cochainOne_eval, one_mul, backSimplex_zero_one ]

/-
Left unitality of the cohomology cup product in degree one:
`1 ⌣ a = a` for `a ∈ H¹(X; F₂)`.
-/
theorem cupZMod2_oneZMod2_left {X : TopCat.{0}} (a : cohomologyZMod2 X 1) :
    cupZMod2 (oneZMod2 X) a = a := by
  obtain ⟨ φ, hφ, rfl ⟩ := cocycleClass_surjective X 1 a;
  rw [ oneZMod2, cupZMod2_mk ];
  convert cocycleClass_congr X 1 _ _ _;
  exact cochainCup_one_left φ

/-- The first cup power of a degree-one class is the class itself. -/
theorem cupPowZMod2_one {X : TopCat.{0}} (a : cohomologyZMod2 X 1) :
    cupPowZMod2 a 1 = a := by
  have h : cupPowZMod2 a 1 = cupZMod2 (oneZMod2 X) a := rfl
  rw [h, cupZMod2_oneZMod2_left]

/-- **Unconditional α-power nonvanishing.** For `1 ≤ k ≤ n`,
`cupPowZMod2 (actualRPAlpha n) k ≠ 0`, proved by the Smith/Gysin induction with
no cup-product structure assumption. -/
theorem actualRPAlpha_power_ne_zero_no_cup
    (n : ℕ) (hn : 1 ≤ n) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    cupPowZMod2 (actualRPAlpha n) k ≠ 0 := by
  revert hkn
  induction k, hk1 using Nat.le_induction with
  | base =>
    intro _
    rw [cupPowZMod2_one]
    exact actualRPAlpha_ne_zero n hn
  | succ k hk1 ih =>
    intro hkn
    have hklt : k < n := hkn
    have hpow : cupPowZMod2 (actualRPAlpha n) k ≠ 0 := ih (Nat.le_of_succ_le hkn)
    intro hzero
    rw [cupPowZMod2_succ] at hzero
    have hconn : (rpGysinConnecting n k).hom (cupPowZMod2 (actualRPAlpha n) k)
        = cupZMod2 (cupPowZMod2 (actualRPAlpha n) k) (actualRPAlpha n) :=
      rpGysinConnecting_eq_cup_actualRPAlpha n k _
    rw [← hconn] at hzero
    exact hpow
      (rpGysinConnecting_eq_zero_imp_zero_of_lt n k (by omega) hklt
        (cupPowZMod2 (actualRPAlpha n) k) hzero)

/-- **Unconditional top-power nonvanishing.** `cupPowZMod2 (actualRPAlpha n) n ≠ 0`
for `n ≥ 1`, the `n`-th cup power of the canonical class in `Hⁿ(RPⁿ; F₂)`. -/
theorem actualRPAlpha_topPower_ne_zero_no_cup (n : ℕ) (hn : 1 ≤ n) :
    cupPowZMod2 (actualRPAlpha n) n ≠ 0 :=
  actualRPAlpha_power_ne_zero_no_cup n hn hn le_rfl

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
