import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CupProduct

/-!
# Cup-product naturality and powers: fixed-point powers and reusable algebra

This file advances the cup-product *naturality and powers* track on top of the
genuine cochain-level cup product of `CupProduct.lean`. It proves the strongest
build-clean statements currently available toward the final-theorem target

```text
fbar^*(α) = α  ⟹  fbar^*(αⁿ) = αⁿ          (α ∈ H¹(RPⁿ; F₂))
```

without introducing any fake `cup`, fake powers, fake `α`, or fake final theorem
(per `Axioms_And_Placeholders.md`).

## Status of the cup product (unchanged from `CupProduct.lean`)

* **Cochain level: present and genuine.** `cochainCup` (Alexander–Whitney
  formula), full `R`-bilinearity, naturality `cochainCup_naturality`
  (`f^*(φ⌣ψ)=f^*φ⌣f^*ψ`), the unit `cochainOne`, powers `cochainPow`, and powers
  naturality `cochainPow_naturality` (`f^*(φⁿ)=(f^*φ)ⁿ`).
* **Cohomology level: present** (over `ZMod 2`), in
  `CohomologyCupProduct.lean`: the cochain Leibniz / coboundary identity now
  descends the cup product to singular cohomology (`cupZMod2`, `cupZMod2_mk`),
  with naturality (`cohPullback_cupZMod2`), powers (`cupPowZMod2`), power
  naturality (`cohPullback_cupPowZMod2`), and the fixed-point power theorem
  (`cohPullback_cupPowZMod2_fixed`). The abstract `GradedCupPullback` API of this
  file remains the reusable algebraic core.

## What this file adds

1. **Reusable algebra lemmas** (`Monoid`/`MonoidHom`/`RingHom`): a multiplicative,
   unital self-map preserves powers, hence fixes the powers of any fixed point.
   These are exactly the algebraic step that closes the final target once a
   cohomology *ring* with a `RingHom` pullback exists: `f^*(αⁿ)=(f^*α)ⁿ=αⁿ`.
2. **An abstract graded multiplicative-pullback API** `GradedCupPullback`: any
   degreewise product with unit and a multiplicative degreewise pullback has
   `pull(xⁿ) = (pull x)ⁿ` and the fixed-point corollary `pull(xⁿ)=xⁿ`. This is the
   "power preservation from any multiplicative pullback API" requested; the future
   cohomology-level cup product will instantiate it directly.
3. **The cochain-level realization**: the unit is pullback-stable
   (`cochainPullback_one`), the cochain cup product/unit/pullback of a self-map
   `f : X ⟶ X` assemble into a `GradedCupPullback`
   (`cochainCupPullback`), and the **fixed-point power theorem**
   `cochainPow_fixed` (`f^*φ=φ ⟹ f^*(φⁿ)=φⁿ`) with its `ZMod 2` specialization
   `cochainPow_fixedZMod2`. This is the cochain-level form of the final target.

The descent of all of this to cohomology is now carried out in
`CohomologyCupProduct.lean`: the cohomology analogue of `cochainPow_fixed` is
`cohPullback_cupPowZMod2_fixed` (`fbar^* a = a ⟹ fbar^*(aⁿ) = aⁿ`), and
`InducedOnRPCohomology.lean` specializes it to the descended odd map on `RP n`
(`inducedOnRP_cohPullback_cupPow_fixed`). The remaining input to the final theorem
is the degree-1 class `α ∈ H¹(RPⁿ; F₂)` from the universal coefficient theorem.
-/

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## 1. Reusable algebra: powers under multiplicative maps -/

/-- A multiplicative, unital self-map of a monoid preserves powers:
`φ(aⁿ) = (φ a)ⁿ`. (Unbundled form, for use before a `MonoidHom` is available.) -/
theorem mulMap_pow {M : Type*} [Monoid M] {φ : M → M}
    (hmul : ∀ a b, φ (a * b) = φ a * φ b) (hone : φ 1 = 1) (a : M) :
    ∀ n, φ (a ^ n) = (φ a) ^ n
  | 0 => by simpa using hone
  | (n + 1) => by rw [pow_succ, pow_succ, hmul, mulMap_pow hmul hone a n]

/-- A multiplicative, unital self-map of a monoid fixes the powers of any fixed
point: if `φ a = a` then `φ(aⁿ) = aⁿ`. -/
theorem mulMap_pow_fixed {M : Type*} [Monoid M] {φ : M → M}
    (hmul : ∀ a b, φ (a * b) = φ a * φ b) (hone : φ 1 = 1) {a : M}
    (ha : φ a = a) (n : ℕ) : φ (a ^ n) = a ^ n := by
  rw [mulMap_pow hmul hone, ha]

/-- A monoid homomorphism fixes the powers of any fixed point: `φ a = a ⟹
φ(aⁿ) = aⁿ`. This is the algebraic shape of the final target
`fbar^*(α)=α ⟹ fbar^*(αⁿ)=αⁿ` once the pullback is a (multiplicative) ring map. -/
theorem MonoidHom.map_pow_fixed {M : Type*} [Monoid M] (φ : M →* M) {a : M}
    (ha : φ a = a) (n : ℕ) : φ (a ^ n) = a ^ n := by rw [map_pow, ha]

/-- A ring homomorphism fixes the powers of any fixed point: `φ a = a ⟹
φ(aⁿ) = aⁿ`. The cohomology pullback `fbar^*` will be such a ring map once the
cohomology-level cup product exists; this is then the verbatim final step. -/
theorem RingHom.map_pow_fixed {R : Type*} [Semiring R] (φ : R →+* R) {a : R}
    (ha : φ a = a) (n : ℕ) : φ (a ^ n) = a ^ n := by rw [map_pow, ha]

/-! ## 2. Abstract graded multiplicative-pullback API

This packages exactly the structure a (future) cohomology-level cup product with
a multiplicative pullback provides — a degreewise product, a unit, and a
degreewise pullback satisfying multiplicativity and unitality — and derives that
the pullback preserves cup powers of a degree-one class, plus the fixed-point
corollary. It is independent of singular cohomology and reusable. -/

/-- An abstract graded multiplicative pullback on a graded family `A : ℕ → Type*`:
a degreewise product `cup`, a degree-`0` unit `one`, and a degreewise self-map
`pull` that is multiplicative (`pull (cup a b) = cup (pull a) (pull b)`) and
unital (`pull one = one`). -/
structure GradedCupPullback (A : ℕ → Type*) where
  /-- The degreewise product `A p → A q → A (p+q)`. -/
  cup : ∀ {p q : ℕ}, A p → A q → A (p + q)
  /-- The degree-`0` unit. -/
  one : A 0
  /-- The degreewise pullback self-map. -/
  pull : ∀ {p : ℕ}, A p → A p
  /-- The pullback fixes the unit. -/
  pull_one : pull one = one
  /-- The pullback is multiplicative for the graded product. -/
  pull_cup : ∀ {p q : ℕ} (a : A p) (b : A q), pull (cup a b) = cup (pull a) (pull b)

namespace GradedCupPullback

variable {A : ℕ → Type*}

/-- The `n`-th cup power `xⁿ ∈ A n` of a degree-one element `x ∈ A 1`, by
`x⁰ = one` and `xⁿ⁺¹ = xⁿ ⌣ x`. -/
def pow (G : GradedCupPullback A) (x : A 1) : (n : ℕ) → A n
  | 0 => G.one
  | (n + 1) => G.cup (G.pow x n) x

@[simp] theorem pow_zero (G : GradedCupPullback A) (x : A 1) : G.pow x 0 = G.one := rfl

@[simp] theorem pow_succ (G : GradedCupPullback A) (x : A 1) (n : ℕ) :
    G.pow x (n + 1) = G.cup (G.pow x n) x := rfl

/-- **Pullback preserves powers.** `pull(xⁿ) = (pull x)ⁿ`. -/
theorem pull_pow (G : GradedCupPullback A) (x : A 1) :
    ∀ n, G.pull (G.pow x n) = G.pow (G.pull x) n
  | 0 => G.pull_one
  | (n + 1) => by rw [pow, pow, G.pull_cup, pull_pow]

/-- **Fixed-point powers.** If `pull x = x` then `pull(xⁿ) = xⁿ` for all `n`. -/
theorem pull_pow_fixed (G : GradedCupPullback A) {x : A 1} (hx : G.pull x = x) (n : ℕ) :
    G.pull (G.pow x n) = G.pow x n := by rw [pull_pow, hx]

end GradedCupPullback

/-! ## 3. Cochain-level realization

The pullback of a self-map `f : X ⟶ X` together with the cochain cup product and
unit form a `GradedCupPullback`, from which the fixed-point power theorem follows.
-/

/-- **Pullback fixes the unit cochain.** `f^*(1) = 1`. -/
@[simp] theorem cochainPullback_one {R : Type} [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y) :
    cochainPullback f 0 (cochainOne (R := R) (Z := Y)) = cochainOne (R := R) (Z := X) := by
  apply cochain_ext; intro σ
  rw [cochainPullback_eval, cochainOne_eval, cochainOne_eval]

/-- The cochain cup product, unit, and pullback of a self-map `f : X ⟶ X` assemble
into a `GradedCupPullback` on the graded family of singular cochain groups. Its
`pow` is `cochainPow` and its `pull_pow`/`pull_pow_fixed` specialize to the
cochain-level power naturality / fixed-point theorems. -/
noncomputable def cochainCupPullback {R : Type} [CommRing R] {X : TopCat.{0}} (f : X ⟶ X) :
    GradedCupPullback (fun p => singularCochainGroup R X p) where
  cup {p q} φ ψ := cochainCup p q φ ψ
  one := cochainOne
  pull {p} φ := cochainPullback f p φ
  pull_one := cochainPullback_one f
  pull_cup {p q} φ ψ := cochainCup_naturality f p q φ ψ

/-- The abstract `pow` of `cochainCupPullback` is the cochain power `cochainPow`. -/
theorem cochainCupPullback_pow {R : Type} [CommRing R] {X : TopCat.{0}} (f : X ⟶ X)
    (φ : singularCochainGroup R X 1) (n : ℕ) :
    (cochainCupPullback f).pow φ n = cochainPow φ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [GradedCupPullback.pow_succ, cochainPow_succ, ih]; rfl

/-- **Fixed-point powers at cochain level.** If a degree-one cochain `φ` is fixed
by the pullback `f^*` of a self-map `f : X ⟶ X` (i.e. `f^*φ = φ`), then so are all
its cup powers: `f^*(φⁿ) = φⁿ`. This is the cochain-level form of the final
target `fbar^*(α)=α ⟹ fbar^*(αⁿ)=αⁿ`. -/
theorem cochainPow_fixed {R : Type} [CommRing R] {X : TopCat.{0}} (f : X ⟶ X)
    (φ : singularCochainGroup R X 1) (hφ : cochainPullback f 1 φ = φ) (n : ℕ) :
    cochainPullback f n (cochainPow φ n) = cochainPow φ n := by
  rw [cochainPow_naturality, hφ]

/-- `ZMod 2` specialization of the cochain-level fixed-point power theorem:
`f^*φ = φ ⟹ f^*(φⁿ) = φⁿ` over `ZMod 2`. -/
theorem cochainPow_fixedZMod2 {X : TopCat.{0}} (f : X ⟶ X)
    (φ : singularCochainGroup (ZMod 2) X 1) (hφ : cochainPullback f 1 φ = φ) (n : ℕ) :
    cochainPullback f n (cochainPowZMod2 φ n) = cochainPowZMod2 φ n :=
  cochainPow_fixed f φ hφ n

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
