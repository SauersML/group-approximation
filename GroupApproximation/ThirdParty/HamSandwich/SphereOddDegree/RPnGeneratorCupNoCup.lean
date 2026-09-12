import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnActualAlphaPowerEqGeneratorNoCup

/-!
# Cup product of `RPⁿ` generators, from actual α-powers (no cup-product structure)

This file proves the genuine singular cup-product formula on the canonical
additive generators of `Hᵏ(RPⁿ; F₂)`:

```text
cupZMod2 gen_p gen_q = gen_{p+q}      (p + q ≤ n)
```

**without** assuming any `RPnCupProductStructure`, multiplicative cellular cochain
structure, singular–cellular cup comparison, or the abstract generator
nonvanishing hypothesis.

## Strategy

Each generator is identified with an actual cup-power of the canonical
double-cover class `α = actualRPAlpha n` by Prompt 72
(`actualRPAlpha_power_eq_rpCohomologyGenerator_no_cup`):

```text
gen_p = αᵖ,   gen_q = αᵍ,   gen_{p+q} = αᵖ⁺ᵍ
```

so the statement reduces to the **cup-power addition law**

```text
cupZMod2 (cupPowZMod2 α p) (cupPowZMod2 α q) = cupPowZMod2 α (p + q).
```

That law is proved here from scratch: it descends (`cupPowZMod2_add`) from the
cochain-level power-addition law `cochainCup_pow_add`, whose inductive step is the
right-associativity instance `cochainCup_assoc_one` of the Alexander–Whitney
cochain cup product. Associativity in turn rests on three combinatorial
front/back face-composition identities.
-/

noncomputable section

open CategoryTheory AlgebraicTopology Limits
  GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## 1. Face-map composition identities -/

/-- Composing the front `p`-face into `⦋p+q⦌` with the front `(p+q)`-face into
`⦋p+q+1⦌` gives the front `p`-face into `⦋p+(q+1)⦌`. -/
lemma frontFace_comp_frontFace (p q : ℕ) :
    frontFace p q ≫ frontFace (p + q) 1 = frontFace p (q + 1) := by
  ext x : 3
  apply Fin.ext
  have hL : ((frontFace (p + q) 1).toOrderHom ((frontFace p q).toOrderHom x) : ℕ) = x.val := rfl
  have hR : ((frontFace p (q + 1)).toOrderHom x : ℕ) = x.val := rfl
  exact hL.trans hR.symm

/-- The back `q`-face followed by the front `(p+q)`-face equals the front
`q`-face followed by the back `p`-face (both send vertex `i ↦ i + p`). -/
lemma backFace_comp_frontFace (p q : ℕ) :
    backFace p q ≫ frontFace (p + q) 1 = frontFace q 1 ≫ backFace p (q + 1) := by
  ext x : 3
  apply Fin.ext
  have hL : ((frontFace (p + q) 1).toOrderHom ((backFace p q).toOrderHom x) : ℕ) = x.val + p := rfl
  have hR : ((backFace p (q + 1)).toOrderHom ((frontFace q 1).toOrderHom x) : ℕ) = x.val + p := rfl
  exact hL.trans hR.symm

/-- Composing the back `1`-face into `⦋q+1⦌` with the back `p`-face into
`⦋p+(q+1)⦌` gives the back `1`-face into `⦋(p+q)+1⦌`. -/
lemma backFace_comp_backFace (p q : ℕ) :
    backFace q 1 ≫ backFace p (q + 1) = backFace (p + q) 1 := by
  ext x : 3
  apply Fin.ext
  show ((backFace p (q + 1)).toOrderHom ((backFace q 1).toOrderHom x) : ℕ)
    = ((backFace (p + q) 1).toOrderHom x : ℕ)
  simp only [backFace_apply]
  omega

/-! ## 2. Simplex-level face-composition identities -/

/-- Front of the front is a longer front face (simplex level). -/
lemma frontSimplex_frontSimplex (Z : TopCat.{0}) (p q : ℕ)
    (σ : singularSimplices Z (p + q + 1)) :
    frontSimplex Z p q (frontSimplex Z (p + q) 1 σ) = frontSimplex Z p (q + 1) σ := by
  show (TopCat.toSSet.obj Z).map (frontFace p q).op
        ((TopCat.toSSet.obj Z).map (frontFace (p + q) 1).op σ)
      = (TopCat.toSSet.obj Z).map (frontFace p (q + 1)).op σ
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, frontFace_comp_frontFace]

/-- Back of the front equals front of the back (simplex level). -/
lemma backSimplex_frontSimplex (Z : TopCat.{0}) (p q : ℕ)
    (σ : singularSimplices Z (p + q + 1)) :
    backSimplex Z p q (frontSimplex Z (p + q) 1 σ)
      = frontSimplex Z q 1 (backSimplex Z p (q + 1) σ) := by
  show (TopCat.toSSet.obj Z).map (backFace p q).op
        ((TopCat.toSSet.obj Z).map (frontFace (p + q) 1).op σ)
      = (TopCat.toSSet.obj Z).map (frontFace q 1).op
        ((TopCat.toSSet.obj Z).map (backFace p (q + 1)).op σ)
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, backFace_comp_frontFace]

/-- Back of the back is a back face at the top (simplex level). -/
lemma backSimplex_backSimplex (Z : TopCat.{0}) (p q : ℕ)
    (σ : singularSimplices Z (p + q + 1)) :
    backSimplex Z (p + q) 1 σ = backSimplex Z q 1 (backSimplex Z p (q + 1) σ) := by
  show (TopCat.toSSet.obj Z).map (backFace (p + q) 1).op σ
      = (TopCat.toSSet.obj Z).map (backFace q 1).op
        ((TopCat.toSSet.obj Z).map (backFace p (q + 1)).op σ)
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, backFace_comp_backFace]

/-! ## 3. Cochain-level associativity instance and power addition -/

/-- **Right-associativity of the cochain cup product** (with the right-most factor
in degree `1`): `A ⌣ (B ⌣ χ) = (A ⌣ B) ⌣ χ`, where the degrees `p + (q+1)` and
`(p+q) + 1` agree definitionally. -/
theorem cochainCup_assoc_one {R : Type} [CommRing R] {Z : TopCat.{0}} (p q : ℕ)
    (A : singularCochainGroup R Z p) (B : singularCochainGroup R Z q)
    (χ : singularCochainGroup R Z 1) :
    cochainCup p (q + 1) A (cochainCup q 1 B χ)
      = cochainCup (p + q) 1 (cochainCup p q A B) χ := by
  apply cochain_ext; intro σ
  show cochainEval (p + (q + 1)) (cochainCup p (q + 1) A (cochainCup q 1 B χ)) σ
    = cochainEval (p + q + 1) (cochainCup (p + q) 1 (cochainCup p q A B) χ) σ
  rw [cochainCup_eval p (q + 1), cochainCup_eval q 1, cochainCup_eval (p + q) 1,
    cochainCup_eval p q, frontSimplex_frontSimplex, backSimplex_frontSimplex,
    backSimplex_backSimplex]
  ring

/-- **Cochain-level power addition.** For a degree-one cochain `φ`,
`φᵖ ⌣ φᵍ = φᵖ⁺ᵍ`. -/
theorem cochainCup_pow_add {R : Type} [CommRing R] {Z : TopCat.{0}}
    (φ : singularCochainGroup R Z 1) (p q : ℕ) :
    cochainCup p q (cochainPow φ p) (cochainPow φ q) = cochainPow φ (p + q) := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      rw [cochainPow_succ, cochainCup_assoc_one, ih]
      rfl

/-! ## 4. Cohomology-level power addition -/

/-- **Cohomology-level cup-power addition.** For a degree-one class
`a ∈ H¹(X; F₂)`, `aᵖ ⌣ aᵍ = aᵖ⁺ᵍ`. -/
theorem cupPowZMod2_add {X : TopCat.{0}} (a : cohomologyZMod2 X 1) (p q : ℕ) :
    cupZMod2 (cupPowZMod2 a p) (cupPowZMod2 a q) = cupPowZMod2 a (p + q) := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective X 1 a
  rw [cupPowZMod2_mk φ hφ p, cupPowZMod2_mk φ hφ q, cupZMod2_mk, cupPowZMod2_mk φ hφ (p + q)]
  exact cocycleClass_congr X (p + q) (cochainCup_pow_add φ p q) _ _

/-! ## 5. Target theorems: cup of `RPⁿ` generators -/

/-- **Cup product of `RPⁿ` generators (no cup-product structure).** For
`1 ≤ n` and `p + q ≤ n`, the singular cup product of the canonical additive
generators of `Hᵖ` and `Hᵍ` is the canonical additive generator of `Hᵖ⁺ᵍ`. The
proof rewrites each generator as an actual α-power (Prompt 72) and applies the
cup-power addition law `cupPowZMod2_add`; no `RPnCupProductStructure`,
multiplicative cellular structure, or generator-nonvanishing hypothesis is used. -/
theorem branch3_rp_generator_cup_eq_generator_no_cup
    (n : ℕ) (hn : 1 ≤ n) (c : RPnCellularCochainStructure n)
    {p q : ℕ} (hp : p ≤ n) (hq : q ≤ n) (hpq : p + q ≤ n) :
    cupZMod2
      (rpCohomologyGenerator c p hp)
      (rpCohomologyGenerator c q hq)
    = rpCohomologyGenerator c (p + q) hpq := by
  rw [← actualRPAlpha_power_eq_rpCohomologyGenerator_no_cup n hn c hp,
    ← actualRPAlpha_power_eq_rpCohomologyGenerator_no_cup n hn c hq,
    ← actualRPAlpha_power_eq_rpCohomologyGenerator_no_cup n hn c hpq,
    cupPowZMod2_add]

/-- **Nonvanishing of the generator cup product (no cup-product structure).** -/
theorem branch3_rp_generator_cup_ne_zero_no_cup
    (n : ℕ) (hn : 1 ≤ n) (c : RPnCellularCochainStructure n)
    {p q : ℕ} (hp : p ≤ n) (hq : q ≤ n) (hpq : p + q ≤ n) :
    cupZMod2
      (rpCohomologyGenerator c p hp)
      (rpCohomologyGenerator c q hq)
    ≠ 0 := by
  rw [branch3_rp_generator_cup_eq_generator_no_cup n hn c hp hq hpq]
  exact rpCohomologyGenerator_ne_zero c (p + q) hpq

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
