# Pestov 9.1 in Lean: blueprint, part 3 (v3 representation and SPLIT for helper lanes)

Lane `pc-architect`, 2026-09-13, **v3**, main tip `612084e22`. This part **supersedes part 1 §1 (ring line) and
§3 G1, G2, G4 and G7**. Everything else in parts 1–2 stands. Namespace `GroupApproximation.Pestov91`.

## V3. Representation: the landed `CrossedProduct.lean` over `Multiplicative ℤ` is canonical

Main now has `GroupApproximation/Pestov91/CrossedProduct.lean` and `CrossedProductFG.lean` (21147debe, probed
green), namespace `Pestov91.CrossedProduct`:
- `A ⋊ ℤ := SkewMonoidAlgebra A (Multiplicative ℤ)`, for any `[Ring A] [MulSemiringAction (Multiplicative ℤ) A]`;
- `C : A →+* _` and `unit : _ˣ`;
- `unit_zpow_mul_C (j a) : ↑(unit ^ j) * C a = C (ofAdd j • a) * ↑(unit ^ j)`;
- `exists_sum_C_mul_unit_zpow x : ∃ S c, x = ∑ j ∈ S, C (c j) * ↑(unit ^ j)`;
- `isFinitelyGeneratedRing_of_closure_translates` and `isFinitelyGeneratedRing_of_adjoin_translates`.

These are exactly the `hconj`/`hspan` shapes of `RingSimple` and `SplitSimplicity`. The landed `CentreSkew` and
`Assembly` `_crossedProduct` forms are stated over the same `Multiplicative ℤ`.

Consequences:
- The `ShiftIndex σ` WIP (`wip/.../CrossedProduct.lean.txt`, 671373851) is **withdrawn**. It cannot land at the
  now-occupied final path.
- The homeomorphism `toeplitzShift` is **not needed**.
- M1 is reversed: the `_crossedProduct` forms do apply to the witness.

**S1. `GroupApproximation/Pestov91/WitnessRing.lean`** [owner pc-crossed-product]. It imports `CrossedProduct`,
`SubshiftToeplitz` and `CentreSkew`.

```lean
/-- `LC(X, 𝔽₂)` for the Toeplitz subshift `X = ToeplitzSpace`. -/
abbrev WitnessCoeff : Type := LocallyConstant ToeplitzSpace (ZMod 2)
/-- `ofAdd j • f = f ∘ ((-j) +ᵥ ·)`, the automorphism `α^j` of A§1.2 (`T = 1 +ᵥ ·`). -/
instance : MulSemiringAction (Multiplicative ℤ) WitnessCoeff
@[simp] theorem ofAdd_smul_witnessCoeff_apply (j : ℤ) (f : WitnessCoeff) (y : ToeplitzSpace) :
    (Multiplicative.ofAdd j • f) y = f ((-j) +ᵥ y)
abbrev WitnessRing : Type := SkewMonoidAlgebra WitnessCoeff (Multiplicative ℤ)
instance : Infinite WitnessRing        -- skewMonoidAlgebra_infinite, locallyConstant_nontrivial
```

Re-pinned leaves, all binder-free (G3, G5, G6, G8 and G9 keep their part 1 names; `WitnessRing` is now the S1 abbrev):
- `isSimpleRing_witnessRing : IsSimpleRing WitnessRing` [pc-ring-simple]. Apply `isSimpleRing_of_minimal_free` with:
  - `ι := CrossedProduct.C`, `u := CrossedProduct.unit`;
  - `τ j := fun y => (-j) +ᵥ y`, `σ j := fun f => Multiplicative.ofAdd j • f`;
  - `hσ := ofAdd_smul_witnessCoeff_apply`, `hconj := unit_zpow_mul_C`, `hspan := exists_sum_C_mul_unit_zpow`;
  - hfree, hmin and continuity from P1.
- `isSimpleGroup_witness : IsSimpleGroup ↥(elementaryGroup (Fin 3) WitnessRing)` [pc-normal-a]. Apply
  `isSimpleGroup_elementaryGroup_crossedProduct (by simp) central_zero_or_one_witnessRing CrossedProduct.C
  CrossedProduct.unit (fun j f => Multiplicative.ofAdd j • f) unit_zpow_mul_C exists_sum_C_mul_unit_zpow hkey`, with
  `hkey := locallyConstant_cut_key τ hτ hfree hcover σ hσ` and `hcover` from `exists_finset_cover_of_dense_orbits`.
- `central_zero_or_one_witnessRing` [pc-el-center]. Apply pc-el-center's generic
  `skewMonoidAlgebra_central_zero_or_one (hinv) (hfree)` (WIP f005179f6, orientation `r * c = c * r`), with the two
  inputs from C1.

## SPLIT: long poles divided into independent files

A helper writes only its own file, and co-probes peers' unlanded files as overlays
(`pcprobe.sh <lane> <file> GroupApproximation/Pestov91/Bar.lean=$PC/lanes/<peer> -- <modules>`). Where a peer
theorem is unlanded, the helper states its own theorem with that peer's pinned type as a binder and lands; it drops
the binder later. FREE means no lane owns the file yet, so main can staff it now.

The long poles are LEF models (G6), crossed-product foundations (S1 plus the dynamics inputs), and centre and
simplicity inputs. The normal-subgroup cases are **not** a long pole: `SplitSimplicity` replaces them (part 2 §M3).

### Gate (owned, small, first)

| File | Owner | Status | Content |
|---|---|---|---|
| `Subshift.lean`, `SubshiftToeplitz.lean`, `SubshiftPeriodic.lean` | pc-subshift | lane drafts, land ASAP | as in part 1 §2 (`Agree`, `orbitClosure`, `ToeplitzSpace`, `vadd_ne_self`, `IsMinimal`, `exists_radius_locallyConstant`, `exists_periodic_model`) |
| `WitnessRing.lean` | pc-crossed-product | owned | S1 above |

### P1. `GroupApproximation/Pestov91/WitnessDynamics.lean` — **FREE**
It imports `SubshiftToeplitz`, and inputs the landed `RingSimple` hypotheses.

```lean
theorem witness_continuous_vadd (j : ℤ) : Continuous fun y : ToeplitzSpace => (-j) +ᵥ y
theorem witness_free : ∀ j : ℤ, j ≠ 0 → ∀ y : ToeplitzSpace, (-j) +ᵥ y ≠ y
theorem witness_dense_orbit : ∀ y : ToeplitzSpace, Dense (Set.range fun j : ℤ => (-j) +ᵥ y)
instance : TotallySeparatedSpace ToeplitzSpace
theorem witness_cover : ∀ W : Set ToeplitzSpace, IsOpen W → W.Nonempty →
    ∃ s : Finset ℤ, ∀ y, ∃ i ∈ s, (-i) +ᵥ y ∈ W
```

Routes:
- continuity from `ContinuousConstVAdd`;
- freeness from `vadd_ne_self`;
- density from `AddAction.IsMinimal` (the orbit is `range (j ↦ j +ᵥ y)`, re-indexed by `-j`);
- `witness_cover` from `exists_finset_cover_of_dense_orbits` (landed `RingSimple`);
- the instance from the subspace of the Cantor space `ℤ → Bool`.

### C1. `GroupApproximation/Pestov91/WitnessCentreInputs.lean` — **FREE**
It imports `WitnessRing` and `WitnessDynamics`, and supplies the inputs of pc-el-center's generic centre theorem.

```lean
theorem witness_invariant_zero_or_one :
    ∀ f : WitnessCoeff, (∀ g : Multiplicative ℤ, g • f = f) → f = 0 ∨ f = 1
theorem witness_action_free :
    ∀ g : Multiplicative ℤ, g ≠ 1 → ∃ a : WitnessCoeff, g • a ≠ a
```

Routes:
- invariance: an invariant `f` is constant on orbits, and orbits are dense while `f` is locally constant, so `f` is
  constant; then `decide` on `ZMod 2`;
- freeness: `g = ofAdd j` with `j ≠ 0`. Pick `y` and a clopen `U ∋ y` with `(-j) +ᵥ y ∉ U`, and take
  `a := LocallyConstant.charFn (ZMod 2) hU`.

### L1. `GroupApproximation/Pestov91/WitnessLEFEval.lean` — **FREE**
It imports `SubshiftPeriodic` and `WitnessRing`, and provides the evaluation points of the periodic models (A§3.1,
N2).

```lean
theorem exists_eval_points (k B : ℕ) :
    ∃ (N : ℕ) (pt : ZMod N → ToeplitzSpace), 0 < N ∧ B ≤ N ∧
      (∀ (n : ZMod N) (i : ℤ) (ρ : ℕ) (f : WitnessCoeff), ρ + i.natAbs ≤ k →
        (∀ y y' : ToeplitzSpace, Agree ρ (y : ℤ → Bool) y' → f y = f y') →
          (Multiplicative.ofAdd i • f) (pt n) = f (pt (n - (i : ZMod N)))) ∧
      (∀ (ρ : ℕ) (f : WitnessCoeff), ρ ≤ k →
        (∀ y y' : ToeplitzSpace, Agree ρ (y : ℤ → Bool) y' → f y = f y') →
          ∀ y : ToeplitzSpace, ∃ n : ZMod N, f (pt n) = f y)
```

Route: `exists_periodic_model k B` gives `z` and `N`. Take `pt n` to be a point agreeing with `shift n z` on radius
`k`. The compatibility clause is `shiftMatrix_mul_diagonal` read at `D := diag (n ↦ E_n)`.

### L2. `GroupApproximation/Pestov91/WitnessLEFCoeff.lean` — **FREE**
It imports `WitnessRing` and `SubshiftToeplitz`, and provides the coefficient map and radius bounds consumed by
`skewModel`.

```lean
noncomputable def witnessCoeffs : WitnessRing →+ (ℤ →₀ WitnessCoeff)
theorem witnessCoeffs_C_mul_unit_zpow (a : WitnessCoeff) (j : ℤ) :
    witnessCoeffs (CrossedProduct.C a * ((CrossedProduct.unit ^ j : WitnessRingˣ) : WitnessRing)) =
      Finsupp.single j a
theorem witnessCoeffs_sum (r : WitnessRing) :
    (witnessCoeffs r).sum (fun j a => CrossedProduct.C a * ((CrossedProduct.unit ^ j : WitnessRingˣ) : WitnessRing)) = r
theorem exists_radius_finset (F : Finset WitnessRing) :
    ∃ ρ w : ℕ, ∀ r ∈ F, ∀ j ∈ (witnessCoeffs r).support, j.natAbs ≤ w ∧
      ∀ y y' : ToeplitzSpace, Agree ρ (y : ℤ → Bool) y' → (witnessCoeffs r j) y = (witnessCoeffs r j) y'
```

Route:
- `witnessCoeffs := (Finsupp.mapDomain toAdd) ∘ SkewMonoidAlgebra.coeff`, as an additive map;
- `witnessCoeffs_sum` from `SkewMonoidAlgebra.sum_single`;
- the radii from `exists_radius_locallyConstant`, taking the maximum over the finite supports.

These are `skewModel`'s `hmono` and `hrepr`. `hcomm` is `unit_zpow_mul_C`, with
`σ i := MulSemiringAction.toRingHom (Multiplicative ℤ) WitnessCoeff (ofAdd i)`.

### L3. `WitnessLEF.lean` [pc-ring-lef, owned]
`hasLocalMatrixModels_witnessRing` and `isLEF_witness` (part 1 G6), from `skewModel`, L1 and L2. pc-ring-lef also
lands `RingLEF.lean` and `RingLEFModel.lean`.

### Other owned leaves (small, after the gate)

| File | Owner | Declaration |
|---|---|---|
| `WitnessSimpleRing.lean` | pc-ring-simple | `isSimpleRing_witnessRing` (V3) |
| `Center.lean` + `WitnessCentre.lean` | pc-el-center | `skewMonoidAlgebra_central_zero_or_one`, `central_zero_or_one_witnessRing` (V3, C1) |
| `WitnessSplit.lean` | pc-normal-a | `isSimpleGroup_witness` (V3) |
| `WitnessFG.lean` | pc-ring-fg | `isFinitelyGeneratedRing_witnessRing`, via `isFinitelyGeneratedRing_of_adjoin_translates (K := ZMod 2)` and pc-ring-fg's coordinate-indicator generation |
| `Endpoint.lean` | pc-assembly | G8, with `exists_infinite_simple_kazhdan_lef_of_elementary` and `Infinite WitnessRing` from S1 |
| `Palomar/Pestov91Solution.lean` | pc-palomar | G9 |

Idle lanes available for FREE files: pc-kazhdan (done), pc-normal-b and pc-normal-tower (superseded). pc-normal-a
could take one too, since G4 is short.

## Arbitration log, continued

- ~03:20.
  - **v3 representation:** the landed `CrossedProduct.lean` (21147debe) is canonical, and the `ShiftIndex σ` WIP is
    withdrawn. `WitnessRing := SkewMonoidAlgebra WitnessCoeff (Multiplicative ℤ)`.
  - Affected: pc-crossed-product (S1), pc-subshift (G1 homeomorphism dropped; P1 inputs), pc-ring-simple,
    pc-normal-a, pc-ring-fg, pc-ring-lef, pc-assembly.
- ~03:20, pc-kazhdan: do not build `SimpleGroup.lean` (part 2 §M6); it is covered by `SplitSimplicity`.
- ~03:20, pc-el-center: the generic `skewMonoidAlgebra_central_zero_or_one` is adopted for G3. M2 is resolved:
  `Center.lean` redeclares nothing from `Centre.lean`, and the orientation is `r * c = c * r`.
- ~03:20, team-lead: SPLIT added. FREE files are P1, C1, L1 and L2.
