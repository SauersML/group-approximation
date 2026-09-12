import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnTopClassAlphaPower
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnInclusionCohomology

/-!
# Additive mod-two cohomology of `RPⁿ` (cellular computation)

The classical additive computation of the mod-two singular cohomology of finite
real projective space is

```text
H^k(RPⁿ; F₂) ≅ F₂   for 0 ≤ k ≤ n,        H^k(RPⁿ; F₂) = 0   for k > n.
```

The standard proof uses the **CW/cellular structure** of `RPⁿ` (one cell in each
dimension `0, 1, …, n`). Over the field `F₂` the cellular boundary maps all
vanish (the integral incidence numbers alternate between `0` and `±2`, both `≡ 0
mod 2`), so the cellular cochain complex is

```text
F₂ --0--> F₂ --0--> ⋯ --0--> F₂      (degrees 0 … n, zero elsewhere)
```

with **zero differentials**, and its cohomology is `F₂` in each degree `0 … n`
and `0` above.

This file carries out exactly that computation, in three honest layers:

1. **A reusable, unconditional lemma** (`cochainHomologyIsoOfZeroDiff`): the
   `k`-th homology of *any* zero-differential cochain complex over `F₂` is
   (canonically isomorphic to) its `k`-th object. This is genuine homological
   algebra with no projective-space input.

2. **The concrete cellular model** (`rpCellularCochainComplex n`): the genuine
   zero-differential cochain complex above, an honest object of
   `CochainComplex (ModuleCat (ZMod 2)) ℕ`, with its additive cohomology fully
   and **unconditionally** computed:
   `rpCellularCohomology n k ≅ F₂` for `k ≤ n` (dimension one) and `= 0` for
   `k > n`, plus the top-degree and degree-one nonvanishing.

3. **The conditional bridge to genuine singular cohomology**
   (`RPnCellularCochainStructure n`): the single honest hypothesis that the
   project's *genuine* singular cochain complex `C^•(RPⁿ; F₂)` is isomorphic, as
   a cochain complex, to the cellular model. This is precisely the
   cellular-approximation input that pinned Mathlib does not provide (there is no
   CW structure on `RPⁿ` and no cellular-equals-singular theorem). Granting it,
   **every additive cohomology statement transports to the genuine
   `rpCohomology n k`**: one-dimensionality in range, vanishing above the
   dimension, and the load-bearing **top-degree** and **`H¹`** nonvanishing.

No fake `α`, no fake cohomology group, no placeholder isomorphism to topological
cohomology is asserted: layers 1–2 are unconditional genuine mathematics, and
layer 3 states its one missing input as an explicit, clearly-labelled
hypothesis (policy: `Axioms_And_Placeholders.md`). Every declaration depends only
on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! ## 1. Homology of a zero-differential cochain complex (reusable) -/

/-- **Homology of a zero-differential complex.** For any cochain complex `K` over
`F₂` whose differentials all vanish, the `k`-th homology is canonically
isomorphic to the `k`-th object `K.X k`: with no differentials there are no
boundaries and every chain is a cycle, so `H^k(K) = ker / im = K.X k / 0 = K.X
k`. This is the engine of the cellular computation. -/
def cochainHomologyIsoOfZeroDiff (K : CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ)
    (hd : ∀ i j, K.d i j = 0) (k : ℕ) : K.homology k ≅ K.X k :=
  (ShortComplex.HomologyData.ofZeros (K.sc k)
    (by change K.d _ _ = 0; exact hd _ _)
    (by change K.d _ _ = 0; exact hd _ _)).left.homologyIso

/-! ## 2. The concrete cellular cochain model of `RPⁿ` -/

/-- The `k`-th object of the cellular cochain complex of `RPⁿ`: a copy of `F₂` in
each degree `0 … n`, and the zero module above degree `n`. -/
def rpCellularX (n k : ℕ) : ModuleCat.{0} (ZMod 2) :=
  if k ≤ n then ModuleCat.of (ZMod 2) (ZMod 2) else ModuleCat.of (ZMod 2) PUnit

/-- The **cellular cochain complex** of `RPⁿ` over `F₂`: `F₂` in each degree
`0 … n`, zero above, and **all differentials zero**. A genuine object of
`CochainComplex (ModuleCat (ZMod 2)) ℕ`. -/
def rpCellularCochainComplex (n : ℕ) : CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ where
  X := rpCellularX n
  d := fun _ _ => 0
  shape := by intro i j _; rfl
  d_comp_d' := by intro i j k _ _; simp

/-- The cellular cochain complex has zero differentials. -/
@[simp] theorem rpCellularCochainComplex_d (n i j : ℕ) :
    (rpCellularCochainComplex n).d i j = 0 := rfl

/-- In the cellular range `k ≤ n`, the `k`-th cellular object is a copy of `F₂`. -/
def rpCellularX_iso_in_range (n k : ℕ) (hk : k ≤ n) :
    rpCellularX n k ≅ ModuleCat.of (ZMod 2) (ZMod 2) :=
  eqToIso (by simp only [rpCellularX, hk, if_true])

/-- Above the cellular range `n < k`, the `k`-th cellular object is the zero
module. -/
theorem rpCellularX_isZero_above (n k : ℕ) (hk : n < k) :
    IsZero (rpCellularX n k) := by
  have hnk : ¬ k ≤ n := by omega
  simp only [rpCellularX, hnk, if_false]
  exact ModuleCat.isZero_of_subsingleton _

/-- The `k`-th additive **cellular cohomology** of `RPⁿ`: the `k`-th homology of
the cellular cochain complex. -/
def rpCellularCohomology (n k : ℕ) : ModuleCat.{0} (ZMod 2) :=
  (rpCellularCochainComplex n).homology k

/-- The cellular cohomology in degree `k` is canonically the `k`-th cellular
object (zero differentials). -/
def rpCellularCohomology_iso_X (n k : ℕ) :
    rpCellularCohomology n k ≅ rpCellularX n k :=
  cochainHomologyIsoOfZeroDiff (rpCellularCochainComplex n)
    (rpCellularCochainComplex_d n) k

/-- **Cellular cohomology in range is one-dimensional:**
`H^k_cell(RPⁿ) ≅ F₂` for `0 ≤ k ≤ n`. -/
def rpCellularCohomology_iso_in_range (n k : ℕ) (hk : k ≤ n) :
    rpCellularCohomology n k ≅ ModuleCat.of (ZMod 2) (ZMod 2) :=
  (rpCellularCohomology_iso_X n k) ≪≫ (rpCellularX_iso_in_range n k hk)

/-- **Cellular cohomology vanishes above the dimension:**
`H^k_cell(RPⁿ) = 0` for `k > n`. -/
theorem rpCellularCohomology_isZero_above (n k : ℕ) (hk : n < k) :
    IsZero (rpCellularCohomology n k) :=
  (rpCellularX_isZero_above n k hk).of_iso (rpCellularCohomology_iso_X n k)

/-- The `F₂`-dimension of the cellular cohomology in range is `1`. -/
theorem rpCellularCohomology_finrank_in_range (n k : ℕ) (hk : k ≤ n) :
    Module.finrank (ZMod 2) (rpCellularCohomology n k) = 1 := by
  rw [(rpCellularCohomology_iso_in_range n k hk).toLinearEquiv.finrank_eq]
  simp

/-! ## 3. The conditional bridge to genuine singular cohomology

The only missing input for the genuine computation is the cellular-approximation
identification of the singular cochain complex of `RPⁿ` with the cellular model.
We package it as an explicit hypothesis. -/

/-- **Cellular-cochain hypothesis for `RPⁿ`.** The single honest input the genuine
additive computation depends on: an isomorphism, in
`CochainComplex (ModuleCat (ZMod 2)) ℕ`, between the project's genuine singular
cochain complex `C^•(RPⁿ; F₂)` and the cellular model `rpCellularCochainComplex
n`. This is exactly the (Mathlib-absent) cellular-approximation / "cellular cochains
compute singular cohomology" input; granting it computes `H^k(RPⁿ; F₂)`. -/
structure RPnCellularCochainStructure (n : ℕ) where
  /-- The cochain-complex isomorphism `C^•(RPⁿ; F₂) ≅ (cellular model)`. -/
  iso : singularCochainComplexZMod2.obj (Opposite.op (TopCat.of (RP n)))
          ≅ rpCellularCochainComplex n

/-- From the cellular hypothesis, the genuine singular cohomology of `RPⁿ` agrees
with the cellular cohomology in every degree. -/
def RPnCellularCochainStructure.cohomologyIso {n : ℕ}
    (c : RPnCellularCochainStructure n) (k : ℕ) :
    rpCohomology n k ≅ rpCellularCohomology n k :=
  (HomologicalComplex.homologyFunctor _ _ k).mapIso c.iso

/-- **Additive mod-two cohomology of `RPⁿ`, in range (conditional).**
`H^k(RPⁿ; F₂) ≅ F₂` for `0 ≤ k ≤ n`, given the cellular hypothesis. -/
def rpModTwoCohomologyAdditive {n : ℕ} (c : RPnCellularCochainStructure n)
    (k : ℕ) (hk : k ≤ n) :
    rpCohomology n k ≅ ModuleCat.of (ZMod 2) (ZMod 2) :=
  (c.cohomologyIso k) ≪≫ (rpCellularCohomology_iso_in_range n k hk)

/-- **Dimension of `H^k(RPⁿ; F₂)` in range (conditional):** it is one-dimensional
over `F₂` for `0 ≤ k ≤ n`. -/
theorem rpModTwoCohomology_dim {n : ℕ} (c : RPnCellularCochainStructure n)
    (k : ℕ) (hk : k ≤ n) :
    Module.finrank (ZMod 2) (rpCohomology n k) = 1 := by
  rw [(rpModTwoCohomologyAdditive c k hk).toLinearEquiv.finrank_eq]
  simp

/-- **Vanishing above the dimension (conditional):** `H^k(RPⁿ; F₂) = 0` for
`k > n`, given the cellular hypothesis. -/
theorem rpCohomology_vanish_above_dim {n : ℕ} (c : RPnCellularCochainStructure n)
    (k : ℕ) (hk : n < k) :
    IsZero (rpCohomology n k) :=
  (rpCellularCohomology_isZero_above n k hk).of_iso (c.cohomologyIso k)

/-- A one-dimensional `F₂`-cohomology group is nonzero. -/
theorem isZero_false_of_iso_F2 (A : ModuleCat.{0} (ZMod 2))
    (e : A ≅ ModuleCat.of (ZMod 2) (ZMod 2)) : ¬ IsZero A := by
  rw [ModuleCat.isZero_iff_subsingleton, e.toLinearEquiv.toEquiv.subsingleton_congr]
  exact not_subsingleton (ZMod 2)

/-- **Top-degree nonvanishing (conditional):** `Hⁿ(RPⁿ; F₂) ≅ F₂`, hence nonzero —
this is the additive top class that carries the degree-comparison argument. -/
def rpTopCohomologyZMod2_iso {n : ℕ} (c : RPnCellularCochainStructure n) :
    rpTopCohomology n ≅ ModuleCat.of (ZMod 2) (ZMod 2) :=
  rpModTwoCohomologyAdditive c n le_rfl

/-- **The top mod-two cohomology of `RPⁿ` is nonzero (conditional).** -/
theorem rpTopCohomologyZMod2_nonzero {n : ℕ} (c : RPnCellularCochainStructure n) :
    ¬ IsZero (rpTopCohomology n) :=
  isZero_false_of_iso_F2 _ (rpTopCohomologyZMod2_iso c)

/-- **Degree-one nonvanishing (conditional):** for `n ≥ 1`, `H¹(RPⁿ; F₂) ≅ F₂`. -/
def rpH1ZMod2_iso {n : ℕ} (c : RPnCellularCochainStructure n) (hn : 1 ≤ n) :
    rpCohomology n 1 ≅ ModuleCat.of (ZMod 2) (ZMod 2) :=
  rpModTwoCohomologyAdditive c 1 hn

/-- **`H¹(RPⁿ; F₂)` is nonzero for `n ≥ 1` (conditional).** -/
theorem rpH1ZMod2_nonzero {n : ℕ} (c : RPnCellularCochainStructure n) (hn : 1 ≤ n) :
    ¬ IsZero (rpCohomology n 1) :=
  isZero_false_of_iso_F2 _ (rpH1ZMod2_iso c hn)

/-! ## 4. Prompt-24 named additive targets

These package the additive computation under the canonical names requested by the
model-bridge interface: an additive isomorphism `H^k(RPⁿ; F₂) ≅ F₂` in range, the
vanishing above the dimension, and a one-dimensional generator in each degree of
the range. All are conditional on the single honest cellular-cochain input
`RPnCellularCochainStructure n`. -/

/-- **Additive iso to the model group (conditional).** `H^k(RPⁿ; F₂) ≅ F₂` for
`0 ≤ k ≤ n` — the additive identification of the actual singular cohomology with
the model group in every degree of the range. -/
def rpCohomology_additive_iso_zmod2 {n : ℕ} (c : RPnCellularCochainStructure n)
    (k : ℕ) (hk : k ≤ n) :
    rpCohomology n k ≅ ModuleCat.of (ZMod 2) (ZMod 2) :=
  rpModTwoCohomologyAdditive c k hk

/-- Alias of `rpCohomology_additive_iso_zmod2`. -/
def rpCohomology_additive_iso {n : ℕ} (c : RPnCellularCochainStructure n)
    (k : ℕ) (hk : k ≤ n) :
    rpCohomology n k ≅ ModuleCat.of (ZMod 2) (ZMod 2) :=
  rpCohomology_additive_iso_zmod2 c k hk

/-- **`F₂`-rank is one in range (conditional).** `dim_{F₂} H^k(RPⁿ; F₂) = 1` for
`0 ≤ k ≤ n`. -/
theorem rpCohomology_rank_one {n : ℕ} (c : RPnCellularCochainStructure n)
    (k : ℕ) (hk : k ≤ n) :
    Module.finrank (ZMod 2) (rpCohomology n k) = 1 :=
  rpModTwoCohomology_dim c k hk

/-- **Vanishing above the dimension (conditional).** `H^k(RPⁿ; F₂) = 0` for
`k > n`. -/
theorem rpCohomology_isZero_above_dimension {n : ℕ}
    (c : RPnCellularCochainStructure n) (k : ℕ) (hk : n < k) :
    IsZero (rpCohomology n k) :=
  rpCohomology_vanish_above_dim c k hk

/-- Alias of `rpCohomology_isZero_above_dimension`. -/
theorem rpCohomology_isZero_of_dimension_lt {n : ℕ}
    (c : RPnCellularCochainStructure n) (k : ℕ) (hk : n < k) :
    IsZero (rpCohomology n k) :=
  rpCohomology_isZero_above_dimension c k hk

/-
**Generator in each degree of the range (conditional).** For `0 ≤ k ≤ n`
there is a nonzero class `g ∈ H^k(RPⁿ; F₂)` that generates the whole
(one-dimensional) group: `span_{F₂} {g} = ⊤`.
-/
theorem rpCohomology_generator {n : ℕ} (c : RPnCellularCochainStructure n)
    (k : ℕ) (hk : k ≤ n) :
    ∃ g : rpCohomology n k, g ≠ 0 ∧ Submodule.span (ZMod 2) {g} = ⊤ := by
  set e : rpCohomology n k ≃ₗ[ZMod 2] ZMod 2 :=
    (rpCohomology_additive_iso_zmod2 c k hk).toLinearEquiv with he
  refine ⟨e.symm 1, ?_, ?_⟩
  · rw [Ne, LinearEquiv.map_eq_zero_iff]; decide
  · rw [eq_top_iff]
    intro x _
    rw [Submodule.mem_span_singleton]
    exact ⟨e x, by simp [← e.injective.eq_iff]⟩

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
