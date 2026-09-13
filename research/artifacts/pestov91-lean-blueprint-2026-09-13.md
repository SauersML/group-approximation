# Pestov 9.1 in Lean: blueprint, part 1 of 2 (contract, witness, discharge map)

Lane `pc-architect`, 2026-09-13, **v2**. Main tip `d62ea043a`. Namespace `GroupApproximation.Pestov91`.
- Part 2 (`pestov91-lean-blueprint-2026-09-13-part2.md`): decisions, mismatches and the arbitration log.
- Skeleton: `wip/pestov91/skeleton/GroupApproximation/Pestov91/Witness.lean.txt`.
- Interface changes: SendMessage `pc-architect`.

This version pins the architecture the lanes have *already built*. Every name below is copied from a landed module
or a lane's WIP. v1 pinned a different representation; it was never landed and is withdrawn (part 2 §M5).

Mathematics: `research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md` ("A§"); reviews N1–N6.
q = 2.

## 1. The witness

- **Subshift (D1).** The period-doubling Toeplitz sequence `toeplitz n = Nat.bodd (padicValInt 2 n)`, with
  `toeplitzSubshift := orbitClosure toeplitz` and `ToeplitzSpace := ↥toeplitzSubshift.carrier`. It uses
  Mathlib's `Subshift Bool ℤ` and the action `(n +ᵥ y) h = y (n + h)`.
- **Homeomorphism.** `toeplitzShift : ToeplitzSpace ≃ₜ ToeplitzSpace := Homeomorph.vadd (1 : ℤ)`. So `σ = T`,
  with `(T x)_h = x_(h+1)`.
- **Ring (D3).** `WitnessRing : Type := CrossedProduct toeplitzShift`, which is
  `SkewMonoidAlgebra (LocallyConstant ToeplitzSpace (ZMod 2)) (ShiftIndex toeplitzShift)`, with
  `u f u⁻¹ = f ∘ σ⁻¹` (A§1.2).
- **Group (D4, D5).** `EL₃(WitnessRing) = elementaryGroup (Fin 3) WitnessRing`, as in the EJZ Prop. The centre is
  trivial over `ZMod 2`, so the witness is `EL₃(R)` itself (`Centre.elementaryModCentreEquiv`).
- **Simplicity (D6′).** The landed `SplitSimplicity.isSimpleGroup_elementaryGroup_crossedProduct` takes only ring
  inputs:
  - `IsSimpleRing`;
  - central elements are `0` or `1`;
  - `hconj`, `hspan`;
  - the localisation `hkey`, which `RingSimple.locallyConstant_cut_key` produces.

  The tower and root-detection plan of A§4.2 is off the critical path (part 2 §M3).
- **Endpoint (D7).**
  - The landed `Assembly.exists_infinite_simple_kazhdan_lef_of_elementary` takes, for `A := WitnessRing`: finite
    generation, `IsSimpleGroup EL₃`, `Infinite (EL₃/Z)` and `IsLEF EL₃`.
  - The Palomar `Pestov91.exists_infinite_simple_propertyT_hyperlinear` / `_sofic` consume it through the landed
    bridges in `Palomar/Pestov91Solution.lean`.

## 2. Landed or WIP contract (consume these; do not re-prove)

| Declaration (namespace `GroupApproximation.Pestov91` unless noted) | Where | State |
|---|---|---|
| `elementary_hasKazhdanPropertyT`, `..._of_surjective`, `elementaryModCentre_hasKazhdanPropertyT` | `Kazhdan.lean` | landed |
| `elementary_hasKazhdanPropertyTComplex` and its quotient forms | `KazhdanUnitary.lean` | landed |
| `isHyperlinear_of_isLEF` | `LEFHyperlinear.lean` | landed |
| `center_elementaryGroup_eq_bot_of_central_zero_or_one` (`hR : ∀ c, (∀ r, r * c = c * r) → c = 0 ∨ c = 1`), `elementaryModCentreEquiv`, `elementaryModCentre_infinite [Infinite R]`, `elementaryModCentre_nontrivial` | `Centre.lean` | landed |
| `skewMonoidAlgebra_infinite [Nontrivial k] [Infinite G]`, `locallyConstant_nontrivial` | `CentreSkew.lean` | landed |
| `isSimpleRing_of_minimal_free`, `isSimpleRing_of_free_of_cover`, `locallyConstant_cut_key`, `exists_finset_cover_of_dense_orbits`, `crossedProduct_isSimpleRing` | `RingSimple.lean` | landed |
| `isSimpleGroup_elementaryGroup_crossedProduct`, `isSimpleGroup_elementaryGroup_of_split`, `crossedProduct_split_annihilator`, `elGen_mem_of_single_root` | `SplitSimplicity.lean` | landed |
| `exists_infinite_simple_kazhdan_lef_of`, `..._of_elementary`, `isSimpleGroup_elementaryModCentre` | `Assembly.lean` | landed |
| `Pestov91.exists_infinite_simple_propertyT_hyperlinear`, `..._sofic` (shared block: `HasPropertyT`, `IsSoficGroup`, `IsHyperlinearGroup`) | `Palomar/Pestov91Challenge.lean` | landed |
| `CrossedProduct σ`, `ShiftIndex σ`, `CrossedProduct.single σ n f`, `.coeff r n`, `.support`, `.sum_single`, `.induction_on`, `.ext`, `.shift σ n` (`shift_apply : shift σ n f x = f ((σ ^ (-n)) x)`), `.single_mul_single`, `.C σ`, `.C_injective`, `.u σ`, `.val_u` | `CrossedProduct.lean` [pc-crossed-product] | WIP 671373851 |
| `Agree k x y`, `orbitClosure`, `AddAction ℤ X.carrier`, `CompactSpace`, `exists_radius_locallyConstant`, `isMinimal_orbitClosure`, `toeplitz`, `toeplitzSubshift`, `ToeplitzSpace`, `vadd_ne_self`, `instance AddAction.IsMinimal ℤ ToeplitzSpace`, `Nonempty`, `Infinite` | `Subshift.lean`, `SubshiftToeplitz.lean` [pc-subshift] | lane draft |
| `periodicToeplitz F`, `exists_periodic_model k B` | `SubshiftPeriodic.lean` [pc-subshift] | lane draft |
| `IsLocalMatrixModel F ψ`, `HasLocalMatrixModels R` (targets `Matrix (Fin N) (Fin N) (ZMod 2)`), `isLEF_units_matrix_of_hasLocalMatrixModels`, `isLEF_elementaryGroup_of_hasLocalMatrixModels (hR) (ι : Type)` | `RingLEF.lean` [pc-ring-lef] | WIP bef911bf4 |
| `skewModel coeff D p`, `skewModel_one`, `skewModel_mul`, `shiftMatrix N j` | `RingLEFModel.lean` [pc-ring-lef] | WIP 970f0290c |
| `isFinitelyGeneratedRing_of_covariant`, `..._covariant_neg` (for `X : Set (ℤ → Bool)`) and the σ-level form of 70a27b8ae | `RingFinitelyGenerated.lean` [pc-ring-fg] | WIP |
| `RootLocalization`, `LocalizedRootDetection`, `normal_le_center_or_eq_top`, `isSimpleGroup_of_rootLocalization` | `NormalSubgroups*.lean` [pc-normal-a] | WIP 4c0c59a50, off the critical path |

## 3. Discharge map for the binder-free endpoint (the remaining work)

Notation: `σ := toeplitzShift` and `R := WitnessRing`. `hconj` and `hspan` are the shapes shared by
`RingSimple`, `SplitSimplicity` and `RingFinitelyGenerated`:
`((u ^ j : Rˣ) : R) * φ a = φ (σ' j a) * ((u ^ j : Rˣ) : R)` and
`∀ x, ∃ S c, x = ∑ j ∈ S, φ (c j) * ((u ^ j : Rˣ) : R)`.

**G1 [pc-subshift], `SubshiftToeplitz.lean`:**

```lean
def toeplitzShift : ToeplitzSpace ≃ₜ ToeplitzSpace := Homeomorph.vadd (1 : ℤ)
theorem toeplitzShift_zpow_apply (n : ℤ) (y : ToeplitzSpace) : (toeplitzShift ^ n) y = n +ᵥ y
theorem toeplitzShift_free : ∀ j : ℤ, j ≠ 0 → ∀ y : ToeplitzSpace, (toeplitzShift ^ (-j)) y ≠ y
theorem toeplitzShift_dense_orbit : ∀ y : ToeplitzSpace, Dense (Set.range fun j : ℤ => (toeplitzShift ^ (-j)) y)
instance : TotallySeparatedSpace ToeplitzSpace
```

**G7 [pc-crossed-product]:** land `CrossedProduct.lean`, and add `WitnessRing.lean` (imports `CrossedProduct` and
`SubshiftToeplitz`):

```lean
instance (σ : X ≃ₜ X) : Infinite (ShiftIndex σ)
theorem CrossedProduct.u_zpow_mul_C (σ : X ≃ₜ X) (j : ℤ) (a : LocallyConstant X (ZMod 2)) :
    ((CrossedProduct.u σ ^ j : (CrossedProduct σ)ˣ) : CrossedProduct σ) * CrossedProduct.C σ a =
      CrossedProduct.C σ (CrossedProduct.shift σ j a) * ((CrossedProduct.u σ ^ j : (CrossedProduct σ)ˣ) : CrossedProduct σ)
theorem CrossedProduct.exists_eq_sum_C_mul_u_zpow (σ : X ≃ₜ X) (x : CrossedProduct σ) :
    ∃ (S : Finset ℤ) (c : ℤ → LocallyConstant X (ZMod 2)),
      x = ∑ j ∈ S, CrossedProduct.C σ (c j) * ((CrossedProduct.u σ ^ j : (CrossedProduct σ)ˣ) : CrossedProduct σ)
abbrev WitnessRing : Type := CrossedProduct toeplitzShift
instance : Infinite WitnessRing          -- skewMonoidAlgebra_infinite
```

**G2 [pc-ring-simple]:** `theorem isSimpleRing_witnessRing : IsSimpleRing WitnessRing`. Apply
`isSimpleRing_of_minimal_free` with:
- `ι := C σ`, `u := u σ`;
- `τ j := ⇑(σ ^ (-j))`, `σ' j := ⇑(shift σ j)`;
- G1 for freeness and density, G7 for `hconj` and `hspan`.

**G3 [pc-el-center]:**
`theorem central_zero_or_one_witnessRing : ∀ c : WitnessRing, (∀ r : WitnessRing, r * c = c * r) → c = 0 ∨ c = 1`.
This is A§1.4: commuting with `C σ (charFn W)` kills `coeff c j`, `j ≠ 0`, by freeness; commuting with `u σ` makes
`coeff c 0` shift-invariant, hence constant, by minimality.

**G4 [pc-normal-a]:** `theorem isSimpleGroup_witness : IsSimpleGroup ↥(elementaryGroup (Fin 3) WitnessRing)`. Apply
`isSimpleGroup_elementaryGroup_crossedProduct` with:
- `hR := G3`;
- `hkey := locallyConstant_cut_key τ hτ hfree hcover σ' hσ`, where `hcover` comes from
  `exists_finset_cover_of_dense_orbits` with G1.

It needs `[IsSimpleRing WitnessRing]` from G2.

**G5 [pc-ring-fg]:** `theorem isFinitelyGeneratedRing_witnessRing : IsFinitelyGeneratedRing WitnessRing`, using the
σ-level form of 70a27b8ae with `σ = T` reading the next coordinate.

**G6 [pc-ring-lef]:** `theorem hasLocalMatrixModels_witnessRing : HasLocalMatrixModels WitnessRing`.
- Construction: `skewModel` with `D := diag ∘ E`, where `E_n f := f y_n` and `y_n ∈ ToeplitzSpace` is a point
  whose radius-`k` window is `z`'s window at `n` (`exists_periodic_model k B`). Also `p := shiftMatrix N`.
- Radius: `k ≥ ρ + w` (N2), with `ρ` from `exists_radius_locallyConstant`.
- Separation: every nonzero coefficient is nonzero at a point whose window occurs in `z`.
- Consequence: `theorem isLEF_witness : IsLEF ↥(elementaryGroup (Fin 3) WitnessRing)`, by
  `isLEF_elementaryGroup_of_hasLocalMatrixModels hasLocalMatrixModels_witnessRing (Fin 3)`.

**G8 [pc-assembly], `Endpoint.lean`:** no binders.

```lean
theorem exists_infinite_simple_kazhdan_lef :
    ∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0, 0} E ∧ IsLEF E :=
  exists_infinite_simple_kazhdan_lef_of_elementary isFinitelyGeneratedRing_witnessRing isSimpleGroup_witness
    (elementaryModCentre_infinite (R := WitnessRing) (0 : Fin 3) 1 (by decide)) isLEF_witness
theorem exists_infinite_simple_kazhdan_sofic_hyperlinear :
    ∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0, 0} E ∧
      IsSofic E ∧ IsHyperlinear E
```

The closure gate for both is `[propext, Classical.choice, Quot.sound]`.

**G9 [pc-palomar]:** the Solution's two theorems without binders, from G8 through the landed bridges.

## 4. Dependency order

- G1 and G7, in parallel.
- Then G2, G3, G5 and G6, in parallel.
- Then G4, then G8, then G9.

Interim form: every lane may land its witness theorem now with the unlanded G-inputs as binders of exactly the
types above. The skeleton `Witness.lean.txt` shows the whole assembly in that form, against landed modules only.
