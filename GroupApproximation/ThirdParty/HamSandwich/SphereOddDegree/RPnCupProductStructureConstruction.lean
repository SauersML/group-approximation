import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCupProductModelCompatibility

/-!
# Branch 3 Prompt 44: the cellular cup-product structure for `RPⁿ` over `F₂`

This file works towards the multiplicative datum `RPnCupProductStructure c` for the
cellular cochain structure `c : RPnCellularCochainStructure n`, whose two fields are

```text
cup_gen   : gen_p ⌣ gen_q = gen_{p+q}      (p + q ≤ n)
one_eq_gen: 1 = gen_0
```

over `F₂`, where `gen_k = rpCohomologyGenerator c k hk` is the canonical
degree-`k` cohomology generator (the unique nonzero element of the
one-dimensional `F₂`-space `Hᵏ(RPⁿ; F₂)`, `0 ≤ k ≤ n`).

What is proved here, all build-clean and free of `sorry`/`axiom`:

* **Bilinearity** of the cohomology cup product over `F₂` (re-exported under the
  branch-3 names from `RPnCupProductModelCompatibility.lean`).
* **Right unitality** of the cohomology cup product, `a ⌣ 1 = a`
  (`cupZMod2_oneZMod2_right`), descended from the cochain-level right unitality
  `cochainCup_one`.
* **The unit is nonzero** in `H⁰(RPⁿ; F₂)` (`oneZMod2_ne_zero_RP`), a direct
  consequence of right unitality and `gen₀ ≠ 0`.
* **The unit field** `one_eq_gen` outright (`branch3_one_eq_generator_zero`):
  `1 = gen₀`, since over `F₂` a one-dimensional space has a unique nonzero element.
* **The whole structure from the minimal cup-nonvanishing fact**
  (`branch3_construct_RPnCupProductStructure_of_cup_nonzero`): given only that the
  cup product of canonical generators is nonzero in range, both fields follow (the
  equality `gen_p ⌣ gen_q = gen_{p+q}` reduces, over `F₂`, to nonvanishing in the
  one-dimensional target).

The remaining unconditional input is exactly the **cup-nonvanishing**
`gen_p ⌣ gen_q ≠ 0` (`p + q ≤ n`), i.e. the genuine RPⁿ cup-product computation
(`H^*(RPⁿ;F₂) = F₂[α]/(αⁿ⁺¹)`). This is Mathlib-absent topology: it cannot be
derived from the purely additive cochain isomorphism `c` alone, and inside the
project it is exactly the content packaged by `RPnCupProductStructure`. It is
isolated here as the single nonvanishing hypothesis of
`branch3_construct_RPnCupProductStructure_of_cup_nonzero`.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

variable {n : ℕ}

/-! ## 1. Bilinearity (branch-3 names) -/

/-- Left scalar-linearity of the cohomology cup product over `F₂`. -/
theorem branch3_cupZMod2_smul_left {X : TopCat.{0}} {p q : ℕ} (s : ZMod 2)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 X q) :
    cupZMod2 (s • a) b = s • cupZMod2 a b :=
  cupZMod2_smul_left s a b

/-- Right scalar-linearity of the cohomology cup product over `F₂`. -/
theorem branch3_cupZMod2_smul_right {X : TopCat.{0}} {p q : ℕ} (s : ZMod 2)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 X q) :
    cupZMod2 a (s • b) = s • cupZMod2 a b :=
  cupZMod2_smul_right s a b

/-! ## 2. A one-dimensional `F₂`-space has a unique nonzero element -/

/-- Over `F₂`, in a one-dimensional module any two nonzero elements coincide. -/
theorem eq_of_finrank_one_of_ne_zero {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (h : Module.finrank (ZMod 2) M = 1) {x y : M} (hx : x ≠ 0) (hy : y ≠ 0) :
    x = y := by
  have h_sub : Submodule.span (ZMod 2) {y} = ⊤ :=
    (finrank_eq_one_iff_of_nonzero y hy).mp h
  obtain ⟨c, hc⟩ : ∃ c : ZMod 2, x = c • y := by
    exact Submodule.mem_span_singleton.mp ( h_sub.symm ▸ Submodule.mem_top ) |> fun ⟨ c, hc ⟩ => ⟨ c, hc.symm ⟩;
  fin_cases c <;> simp_all +decide

/-! ## 3. Right unitality of the cohomology cup product -/

/-- **Right unitality.** `a ⌣ 1 = a` for the cohomology cup product over `F₂`. -/
theorem cupZMod2_oneZMod2_right {X : TopCat.{0}} {p : ℕ} (a : cohomologyZMod2 X p) :
    cupZMod2 a (oneZMod2 X) = a := by
  obtain ⟨ φ, hφ, rfl ⟩ := cocycleClass_surjective X p a;
  rw [ oneZMod2, cupZMod2_mk ];
  rw [ cocycleClass_congr ];
  convert rfl;
  · convert cochainCup_one p φ;
  · exact hφ

/-! ## 4. The unit is nonzero, and equals the degree-zero generator -/

/-- **The unit class is nonzero** in `H⁰(RPⁿ; F₂)`. If it were zero, then by right
unitality `gen₀ = gen₀ ⌣ 1 = gen₀ ⌣ 0 = 0`, contradicting `gen₀ ≠ 0`. -/
theorem oneZMod2_ne_zero_RP (c : RPnCellularCochainStructure n) :
    oneZMod2 (TopCat.of (RP n)) ≠ 0 := by
  intro h
  -- Right unitality: `gen₀ ⌣ 1 = gen₀`; if `1 = 0` then `gen₀ = gen₀ ⌣ 0 = 0`.
  have hgen : rpCohomologyGenerator c 0 (Nat.zero_le n) = 0 := by
    have hr := cupZMod2_oneZMod2_right (rpCohomologyGenerator c 0 (Nat.zero_le n))
    rw [h, ← zero_smul (ZMod 2) (oneZMod2 (TopCat.of (RP n))), cupZMod2_smul_right,
      zero_smul] at hr
    exact hr.symm
  exact rpCohomologyGenerator_ne_zero c 0 (Nat.zero_le n) hgen

/-- **The unit field `one_eq_gen`.** The unit class `1 ∈ H⁰(RPⁿ; F₂)` is the
degree-zero canonical generator. -/
theorem branch3_one_eq_generator_zero (c : RPnCellularCochainStructure n) :
    oneZMod2 (TopCat.of (RP n))
      = rpCohomologyGenerator c 0 (Nat.zero_le n) :=
  eq_of_finrank_one_of_ne_zero (rpModTwoCohomology_dim c 0 (Nat.zero_le n))
    (oneZMod2_ne_zero_RP c) (rpCohomologyGenerator_ne_zero c 0 (Nat.zero_le n))

/-! ## 5. The structure from the minimal cup-nonvanishing input -/

/-- **Construction of `RPnCupProductStructure c` from cup-nonvanishing.** Given the
single nonvanishing input — the cup product of canonical generators is nonzero in
range — the full multiplicative structure follows: over `F₂` the one-dimensional
target makes `gen_p ⌣ gen_q ≠ 0` force `gen_p ⌣ gen_q = gen_{p+q}`, and the unit
field is proved outright (`branch3_one_eq_generator_zero`).

The nonvanishing hypothesis is the genuine RPⁿ cup-product computation
(`H^*(RPⁿ;F₂) = F₂[α]/(αⁿ⁺¹)`), which is Mathlib-absent and cannot be derived from
the additive cochain isomorphism `c` alone. -/
def branch3_construct_RPnCupProductStructure_of_cup_nonzero
    (c : RPnCellularCochainStructure n)
    (hcup : ∀ (p q : ℕ) (hp : p ≤ n) (hq : q ≤ n), p + q ≤ n →
      cupZMod2 (rpCohomologyGenerator c p hp) (rpCohomologyGenerator c q hq) ≠ 0) :
    RPnCupProductStructure c where
  cup_gen := fun p q hp hq hpq =>
    eq_of_finrank_one_of_ne_zero (rpModTwoCohomology_dim c (p + q) hpq)
      (hcup p q hp hq hpq) (rpCohomologyGenerator_ne_zero c (p + q) hpq)
  one_eq_gen := branch3_one_eq_generator_zero c

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
