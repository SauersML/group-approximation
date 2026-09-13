# Pestov 9.1 in Lean: blueprint, part 2 of 2 (decisions, mismatches, arbitration log)

Lane `pc-architect`, 2026-09-13, v2. Part 1 (`research/artifacts/pestov91-lean-blueprint-2026-09-13.md`) holds:
the witness, the contract table, and the discharge map G1–G9.

## Decisions

- **D1. Subshift.** The period-doubling Toeplitz sequence. pc-subshift chose and implemented it independently. Its
  cost is 2-adic arithmetic:
  - aperiodicity: `ν₂(n) = e`, `ν₂(n + j) = e + 1` for `n` in a residue class mod `2^(e+2)`;
  - minimality: recurrence under shifts by multiples of `2^K`;
  - periodic models: `periodicToeplitz F` has period `2^(F+1)` and the same short windows.

  Fibonacci and Thue–Morse would need substitution combinatorics.
- **D3. Ring.** Mathlib's `SkewMonoidAlgebra` over the index synonym `ShiftIndex σ` of `Multiplicative ℤ`, acting
  through the powers of `σ` (pc-crossed-product). The Ring instance comes by instance search, and the normal form is
  the `Finsupp`.
- **D4. Group.** `elementaryGroup (Fin 3) WitnessRing`, the EJZ Prop verbatim (`A : Type`,
  `IsFinitelyGeneratedRing`, `n = 3`, `HasKazhdanPropertyT.{0,0}`).
- **D5. Witness.** `EL₃(R)` itself: over `ZMod 2`, `Z(R)^× = 1`. The quotient type is kept only because
  `Assembly.exists_infinite_simple_kazhdan_lef_of_elementary` asks for `Infinite (EL₃/Z)`, which
  `elementaryModCentre_infinite` supplies.
- **D6′. Simplicity.** Through `SplitSimplicity` (d946a358a): split annihilators from `hkey`, one root spreads,
  and the level ideal is `⊤` by `IsSimpleRing`. No towers. Two alternatives fail for this ring:
  - Preusser (`isSimpleGroup_via_preusser`) needs finite right exchange partitions, which is not known here;
  - the repository's `isSimpleGroup_of_rootDetection` needs single-sandwich division, which fails because the
    ring is stably finite.
- **D7. Endpoint.** `∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0,0} E ∧ IsLEF E`,
  plus the sofic and hyperlinear form, in the repository. The Palomar surface uses the complex-unitary `HasPropertyT`,
  bridged by `KazhdanUnitary`.
- **D8. LEF.** `HasLocalMatrixModels`: additive everywhere, unital, injective and multiplicative on the test set,
  with target `Matrix (Fin N) (Fin N) (ZMod 2)`. The models are `skewModel` from periodic Toeplitz words.

## Mismatches found and how they are resolved

- **M1. `ShiftIndex σ` versus `Multiplicative ℤ`.**
  - The problem: `CentreSkew.elementaryModCentre_crossedProduct_infinite` and
    `Assembly.exists_infinite_simple_kazhdan_lef_of_crossedProduct` are stated for
    `SkewMonoidAlgebra (LocallyConstant X K) (Multiplicative ℤ)`, not for `CrossedProduct σ`. The action instance
    lives on the synonym, so they do not apply to the witness.
  - Decision: the witness uses `Assembly.exists_infinite_simple_kazhdan_lef_of_elementary` and
    `Centre.elementaryModCentre_infinite`. `Infinite WitnessRing` comes from `skewMonoidAlgebra_infinite` with
    `Infinite (ShiftIndex σ)` (G7).
  - Nothing landed changes; the two `_crossedProduct` forms stay unused by the witness.
- **M2. Centre hypothesis orientation.**
  - Canonical: `hR : ∀ c : R, (∀ r : R, r * c = c * r) → c = 0 ∨ c = 1`, as in landed `Centre.lean`,
    `SplitSimplicity.lean` and pc-normal-a's draft.
  - The WIP `wip/pestov91/GroupApproximation/Pestov91/Center.lean.txt` (022fd0448) uses `c * r = r * c`. It also
    re-declares `center_elementaryGroup_eq_bot_of_central_zero_or_one`, which is already landed in `Centre.lean`
    in the same namespace, so landing it would be a duplicate declaration.
  - Decision: pc-el-center adopts the canonical orientation and drops or renames the duplicate before any landing.
    G3 is the lane's remaining deliverable.
- **M3. Normal-subgroup plan superseded.**
  - `SplitSimplicity` proves `IsSimpleGroup` from ring inputs only. The tower subrings, absorption and the case
    (c)/(d) analysis of A§4.2 are not needed for the endpoint. Nor are `RootLocalization`,
    `LocalizedRootDetection` or `normal_le_center_or_eq_top`.
  - Lanes pc-normal-tower and pc-normal-b need not start. pc-normal-a's WIP is sound infrastructure but off the
    critical path; its critical deliverable is G4, a short instantiation.
  - Reallocating lanes is the coordinator's call.
- **M4. LEF interface.** The v1 name `HasLocalFiniteRingModels` is withdrawn; `HasLocalMatrixModels` (pc-ring-lef)
  is canonical.
- **M5. Representation.** v1's base-point `BlockCode` subring of `ℤ → ZMod 2` is withdrawn. The lanes built on
  `LocallyConstant X (ZMod 2)` with a topological `X`, and the landed `RingSimple` is stated for that.
- **M6. v1 `SimpleGroup.lean` [pc-kazhdan] withdrawn.** It is covered by `SplitSimplicity` and pc-normal-a's glue.
- **M7. Kazhdan.** Done: `Kazhdan.lean` and `KazhdanUnitary.lean` are landed.
- **M8. Convention of `σ`.**
  - `toeplitzShift = Homeomorph.vadd 1` is `T` (`(T x)_h = x_(h+1)`), so `u f u⁻¹ = f ∘ T⁻¹ = α(f)` (A§1.2).
  - The generic theorems take `τ j := ⇑(σ ^ (-j))`, matching `CrossedProduct.shift_apply`.
  - pc-ring-fg's σ-level form (70a27b8ae, "σ reads the next coordinate") matches `σ = T`.

## Truthfulness status (2026-09-13, tip d62ea043a)

- **Unconditional on main:**
  - (T) for `EL_n` over finitely generated rings;
  - its complex form and the quotient forms;
  - LEF ⇒ hyperlinear;
  - the centre calculus;
  - `EL₃/Z` infinite for infinite rings;
  - simplicity of free minimal crossed products, given `hconj`/`hspan`;
  - `SplitSimplicity`;
  - the assembly with binders;
  - the Palomar surface.
- **Conditional or unlanded:** every G1–G9 item. No binder-free endpoint exists yet. "PROBE GREEN" claims belong to
  the owning lanes' `.green.` records, not to this blueprint.
- **Not reviewed here:** the proofs inside landed modules. pc-review owns fidelity and closure checks.

## Arbitration log (newest last; date-time CDT, requester, decision, affected lanes)

- 2026-09-13 ~02:40, pc-architect, v1 drafted (base-point `BlockCode`, towers, `HasLocalFiniteRingModels`).
  - Not landed: exland refused four paths, where peers' WIP already existed.
  - Reading main showed the lanes had converged on other interfaces.
- 2026-09-13 ~03:05, pc-architect, v2.
  - Adopt the landed and WIP names (part 1 §2).
  - Pin G1–G9 and decide M1–M8.
  - Affected: all lanes. Critical path: pc-subshift, pc-crossed-product, pc-ring-simple, pc-el-center, pc-normal-a
    (G4 only), pc-ring-fg, pc-ring-lef, pc-assembly, pc-palomar.
