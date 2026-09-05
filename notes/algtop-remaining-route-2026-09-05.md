# `AlgTop/` — what is built, and the executable route for what is not

Lane `found-cohomology-ring`, 2026-09-05. Companion to
`notes/algtop-foundation-plan-2026-09-05.md` (the API contract). This file
records the two blockers found while building that API, and a step-by-step route
through each. Both blockers are **pure algebra**, not topology, and neither has an
alternative route.

## 0. Built

| Module | Contents |
|---|---|
| `AlgTop/CochainLeibniz.lean` | `sum_split_signed`, `aw_cochain_leibniz` over any `CommRing`, `cochainCup_cocycle`, the two coboundary corollaries, `cochainCast_zero/add/smul/cast/self` |
| `AlgTop/SingularCohomology.lean` | `cochainCx`, `cohomology`, `cohomologyℤ`, `IsCocycle`, `cocycleClass` (+ additive, `R`-linear, surjective, kills coboundaries), `classRepr`, `cohPullback` (+ functoriality, homotopy invariance, `cohIsoOfHomotopyEquiv`), `cohCast` |
| `AlgTop/CupProduct.lean` | `cup` / `⌣`, `cup_mk`, bilinearity, `one`, `cup_one`, `cohPullback_cup`, `cohPullback_one` |
| `AlgTop/CupAssoc.lean` | `cochainCup_assoc`, `cup_assoc`, `cochainCup_one_left`, `one_cup` |
| `AlgTop/CrossProduct.lean` | `prodMap`, `cross` / `×ᶜ`, bilinearity, `cross_natural`, `cross_one_right` |
| `AlgTop/FreeSubmodulePID.lean` | `free_of_submodule_of_pid`, `projective_of_submodule_of_pid` (arbitrary rank), `exists_retraction_of_projective_quotient`, `exists_extend_of_projective_quotient` — namespace `…AlgTop.PID` |
| `AlgTop/SingularChainFree.lean` | `chainCx`, `free_chainCx_X`, `free_range_d`, `projective_quot_ker_d`, `exists_extend_off_ker_d`, `cochainCoboundary_eq_comp`, `isCocycle_iff` |
| `AlgTop/Kronecker.lean` | `homologyOf`, `kronOfCocycle` (+ `homologyπ_kronOfCocycle`, additivity, linearity, vanishing on coboundaries), `kronecker`, `kronecker_cocycleClass` |

The whole stack sits on HamSandwich layers 0–7, which the first probe confirmed
green on v4.32. The only `ZMod 2`-specific step in that vendored stack was the
Leibniz rule, and the signed version replaces it.

## 1. Blocker A — no universal coefficient theorem

`Hⁿ(X;R)` is by construction the cohomology of `Hom(C_•(X), R)`. Computing it for
any concrete space needs either the UCT or cohomology Mayer–Vietoris, and:

* **UCT** needs `0 → Zₙ → Cₙ → Bₙ₋₁ → 0` to split, i.e. `Bₙ₋₁` projective.
  `Bₙ₋₁` is a submodule of the free module `Cₙ₋₁`, and Mathlib proves "a submodule
  of a free module over a PID is free" **only in finite rank**
  (`Submodule.basisOfPid`, `[Finite ι]`). Singular chains have uncountable rank.
  Mathlib has no UCT and no Künneth: grepping the pin for
  `universalCoefficient|Kunneth|Künneth` returns nothing.
* **Cohomology Mayer–Vietoris** dualizes the vendored MV sequence, and *that half
  is fine*: `MayerVietorisSES.lean` builds a degreewise **splitting**
  (`routeU`, `routeV`, `mvInclU_small_comp_routeU`, …), so `Hom(−,R)` preserves
  its exactness. The step that fails is identifying `H^*(X)` with the cohomology
  of `Hom(C_*^{U,V}(X), R)`: the vendored small-simplices theorem yields only a
  **quasi-isomorphism** (`smallChains_inclusion_quasiIso`), and a quasi-iso does
  not dualize. Hatcher escapes this because his Prop 2.21 produces a chain
  homotopy *equivalence*; the vendored port kept only the homology consequence and
  its "small" lemmas are existential per chain
  (`exists_iteratedSubdivision_homotopy_mem_smallChains`), not an operator.

`AlgTop/FreeSubmodulePID.lean` supplies the missing algebra. The route from there:

### A1. `AlgTop/UniversalCoefficients.lean` — **the two remaining theorems**

`Kronecker.lean` already builds the map and its computation rule, and
`SingularChainFree.lean` already supplies both splittings. What is left is
exactly two statements:

```lean
theorem kronecker_surjective (R) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (X) (n)
    (f : homologyOf R X n →ₗ[R] R) : ∃ a : cohomology R X n, (kronecker R X n).hom a = f
theorem kronecker_injective  -- when H_{n-1}(X;R) is projective
```

**Surjectivity is now proved** (`AlgTop/UniversalCoefficients.lean`,
`kronecker_surjective` and `exists_cocycle_pairing`): transport `f ∘ homologyπ`
across `ShortComplex.moduleCatCyclesIso` to a functional on `ker ∂ₙ`, extend it
with `exists_extend_off_ker_d`, and observe the extension is a cocycle because a
boundary is a cycle of zero class (`toCycles_comp_homologyπ`).

**Injectivity is the one theorem left.** Statement and proof, fully specified:

```lean
theorem kronecker_injective (m : ℕ) (hproj : Module.Projective R (homologyOf R X m))
    (a : cohomology R X (m + 1)) (ha : (kronecker R X (m + 1)).hom a = 0) : a = 0
```

Write `a = cocycleClass φ hφ`. From `ha` and `homologyπ_kronOfCocycle`, together
with `homologyπ` being epi, `iCycles (m+1) ≫ φ = 0`: `φ` kills `ker ∂ₘ₊₁`. Then

1. `φ̄ := Submodule.liftQ (ker ∂ₘ₊₁) φ.hom h : (Cₘ₊₁ ⧸ ker) →ₗ[R] R`, and
   `ḡ := φ̄ ∘ (LinearMap.quotKerEquivRange ∂ₘ₊₁).symm : ↥(range ∂ₘ₊₁) →ₗ[R] R`,
   with `ḡ ⟨∂c, _⟩ = φ c` by `LinearMap.quotKerEquivRange_symm_apply_image` then
   `Submodule.liftQ_mkQ`.
2. Extend `ḡ` from `Bₘ = range ∂ₘ₊₁` to `Zₘ = ker ∂ₘ`. The quotient
   `Zₘ ⧸ (range ∂ₘ₊₁).comap Zₘ.subtype` is `Hₘ` — because
   `ShortComplex.moduleCatToCycles` is `∂ₘ₊₁.codRestrict Zₘ _` and
   `LinearMap.range_codRestrict` says its range is exactly that `comap` — so it
   is projective by `hproj` transported along `moduleCatHomologyIso`. Apply
   `exists_extend_of_projective_quotient`.
3. Extend again from `Zₘ` to `Cₘ` with `exists_extend_off_ker_d`, giving `ψ`.
4. `d (m+1) m ≫ ψ = φ` by construction, i.e. `φ = cochainCoboundary R X m ψ`
   (`cochainCoboundary_eq_comp`), so `a = 0` by `cocycleClass_coboundary_zero`.

Extra Mathlib handles for this half, all checked at the pin:
`Submodule.liftQ`, `Submodule.liftQ_mkQ`, `LinearMap.quotKerEquivRange`,
`LinearMap.quotKerEquivRange_symm_apply_image`, `LinearMap.range_codRestrict`,
`ShortComplex.moduleCatHomologyIso`. The one arithmetic lemma to state first is
`(ComplexShape.down ℕ).next (m+1) = m`, the mirror of `down_prev` in
`Kronecker.lean`.

The original sketch, kept for context:

Work in `ModuleCat R` with Mathlib's concrete homology model
(`ShortComplex.moduleCatLeftHomologyData`, `moduleCatHomologyIso`,
`moduleCatCyclesIso`, all in `Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean`).

```lean
/-- The Kronecker map, on a cocycle. -/
def kroneckerOfCocycle (R) [CommRing R] (X) (n) (φ : singularCochainGroup R X n)
    (hφ : IsCocycle R X n φ) : (chainCx R X).homology n ⟶ ModuleCat.of R R
/-- The Kronecker map on classes. -/
def kronecker (R) [CommRing R] (X) (n) :
    cohomology R X n ⟶ ModuleCat.of R ((chainCx R X).homology n ⟶ ModuleCat.of R R)
theorem kronecker_surjective        -- always
theorem kronecker_injective         -- when H_{n-1}(X;R) is projective
```

* `kroneckerOfCocycle` is `homologyIsCokernel.desc` of `iCycles n ≫ φ`; the
  cokernel condition is `toCycles ≫ iCycles ≫ φ = d ≫ φ = 0`, which is exactly
  `hφ`.
* **Surjectivity.** Given `f : Hₙ ⟶ R`, put `f̃ := homologyπ ≫ f : Zₙ ⟶ R` and
  extend along the mono `iCycles n : Zₙ ⟶ Cₙ`. The extension exists because the
  cokernel of `iCycles n` is isomorphic to `Bₙ₋₁ ⊆ Cₙ₋₁`, free by
  `free_of_submodule_of_pid`, hence projective; use
  `Module.Projective.lift` on the split. The extension `φ` is a cocycle because
  `∂(Cₙ₊₁) = Bₙ ⊆ Zₙ` and `f̃` kills `Bₙ`.
* **Injectivity when `Hₙ₋₁` is projective.** If `κ(φ) = 0` then `φ|_{Zₙ} = 0`, so
  `φ` factors as `g ∘ ∂ₙ` with `g : Bₙ₋₁ ⟶ R`. Extend `g` over `Zₙ₋₁` (possible
  since `Zₙ₋₁/Bₙ₋₁ = Hₙ₋₁` is projective), then over `Cₙ₋₁` (same splitting as
  above). The result `ψ` has `δψ = ψ ∘ ∂ₙ = φ`, so `[φ] = 0`.

Nothing here needs `Ext`; both halves are the two splittings and no more. Do
**not** build the full six-term UCT — the campaign only needs these two.

**Every Mathlib handle this needs was checked at pin `81a5d257` and exists:**

| Need | Handle |
|---|---|
| lift along a surjection out of a projective | `Module.projective_lifting_property [Projective R P] (f : M →ₗ N) (g : P →ₗ N) (hf : Surjective f) : ∃ h, f.comp h = g` |
| the chain group is a direct sum | `ModuleCat.coprodIsoDirectSum Z : ∐ Z ≅ ModuleCat.of R (⨁ i, Z i)` (`Mathlib/Algebra/Category/ModuleCat/Products.lean`) — and `(chainCx R X).X n` is that coproduct **by `rfl`** |
| direct sums of free modules are free | `Module.Free.directSum` (`Mathlib/LinearAlgebra/DirectSum/Basis.lean`) |
| transport freeness | `Module.Free.of_equiv`, `ModuleCat.Iso.toLinearEquiv` |
| `M/ker ≅ range` | `LinearMap.quotKerEquivRange` |
| `ker mkQ = Q` | `Submodule.ker_mkQ`, `Submodule.mkQ_surjective` |
| concrete cycles/homology in `ModuleCat` | `ShortComplex.moduleCatLeftHomologyData`, `moduleCatCyclesIso`, `moduleCatHomologyIso`, `moduleCatLeftHomologyData_descH_hom` |

The two auxiliary lemmas to build first (they are short, and everything else is
plumbing on top of them):

```lean
theorem exists_retraction_of_projective_quotient {R M} [Ring R] [AddCommGroup M] [Module R M]
    (Q : Submodule R M) [Module.Projective R (M ⧸ Q)] :
    ∃ r : M →ₗ[R] Q, ∀ x : Q, r x = x
theorem exists_extend_of_projective_quotient (Q : Submodule R M)
    [Module.Projective R (M ⧸ Q)] (f : Q →ₗ[R] N) :
    ∃ F : M →ₗ[R] N, ∀ x : Q, F x = f x
```

The first is `Module.projective_lifting_property Q.mkQ LinearMap.id
Q.mkQ_surjective` followed by `(LinearMap.id - s.comp Q.mkQ).codRestrict Q`; the
second is `f.comp r`. The projectivity hypothesis is discharged for
`Q = ker (∂ₙ)` by `LinearMap.quotKerEquivRange` plus
`free_of_submodule_of_pid (LinearMap.range ∂ₙ)`, whose freeness hypothesis on
`Cₙ₋₁` is the `coprodIsoDirectSum` row above.

**Effort.** Roughly 400–700 lines. The mathematics is three short arguments; the
bulk is translating between `HomologicalComplex.cycles/iCycles/homologyπ` and the
concrete `ker`/`range` picture. Budget several build cycles.

### A2. `AlgTop/Spheres.lean`

The vendored `sphereTopHomology_step_MV` and `sphere0_singularHomologyℤ_isZero`
already give integral `H_*(Sⁿ;ℤ)`, and it is free in every degree. So A1 gives, with
no new topology at all:

```lean
def sphereTopCohomologyIso (n) (hn : 1 ≤ n) : cohomologyℤ (Sph n) n ≅ ModuleCat.of ℤ ℤ
def sphereGen (n) (hn) : cohomologyℤ (Sph n) n
theorem sphere_cohomology_isZero (n k) (hn : 1 ≤ n) (hk : k ≠ 0) (hkn : k ≠ n)
def spherePairing (n) (hn) : cohomologyℤ (Sph n) n →ₗ[ℤ] ℤ
def sphereSuspensionIso (n) (hn) : cohomologyℤ (Sph (n+1)) (n+1) ≅ cohomologyℤ (Sph n) n
```

Per design C2, the transport from `Metric.sphere` to the vendored `Sphere n` is
stated once, in `SphereOddDegree/SphereModelTransport.lean`, and reused.

## 2. Blocker B — no graded commutativity

`a ⌣ b = (-1)^{pq} (b ⌣ a)` is **not** available and is separately on the
critical path: it is what makes the cross product multiplicative,

```text
(a ×ᶜ b) ⌣ (a' ×ᶜ b') = (-1)^{q·p'} (a ⌣ a') ×ᶜ (b ⌣ b'),
```

which is what turns `H^*(S¹ × S⁵ × Y)` into a ring, and in particular what proves
`z² = 0` for `z = t·x` — used at every step of manuscript Lemma 3 ("because
`z² = 0` all products of positive components of `ch(δ)` vanish").

The Alexander–Whitney diagonal is not cocommutative on the nose; the identity
needs a natural chain homotopy between `Δ` and `T ∘ Δ`. Two routes:

**B1 (recommended) — Steenrod's `⌣₁`.** Elementary and self-contained: an explicit
formula, no acyclic models. For `φ ∈ Cᵖ`, `ψ ∈ C^q` and `σ` of degree `p+q-1`,

```text
(φ ⌣₁ ψ)(σ) = Σ_{i=0}^{p-1} ± φ(σ|[0..i] ∪ [i+q..p+q-1]) · ψ(σ|[i..i+q]),
```

and the coboundary formula `δ(φ ⌣₁ ψ) = ±(φ ⌣ ψ) ± (ψ ⌣ φ) ± (δφ ⌣₁ ψ)
± (φ ⌣₁ δψ)` gives commutativity on cocycles. Prerequisites, in order:

1. **Interval face maps.** Generalize the vendored `frontFace`/`backFace` to
   `intervalFace a b n : ⦋b-a⦌ ⟶ ⦋n⦌`, `k ↦ a+k`, and the "skip" map
   `outerFace i q p : ⦋p⦌ ⟶ ⦋p+q-1⦌`, `k ↦ k` for `k ≤ i` and `k ↦ k+q-1` for
   `k > i`. Both are `SimplexCategory.mkHom` of an explicit `OrderHom`, exactly
   like `frontFace`, and each needs its `_apply` vertex-value simp lemma.
2. **Composition identities with `SimplexCategory.δ k`,** split by the position of
   `k` relative to `i` and `i+q` — the analogue of
   `frontFace_comp_δ_of_le/_gt`, but with four cases instead of two.
3. **The telescoping,** with a four-block splitting lemma generalizing
   `sum_split_signed`.
4. **Pin the signs by boundary exactness, not by copying a reference.** Fix the
   convention by requiring the identity to hold with *equality* at the smallest
   index (`p = q = 1` on a 2-simplex), then verify the general case. Sign
   conventions for `⌣₁` differ between sources and a wrong one is only detectable
   this way.

**B2 — acyclic models.** Shorter to state, much longer to build: needs freeness of
the singular chain functor on the models `Δⁿ` and acyclicity of
`C(Δⁿ) ⊗ C(Δⁿ)`, the latter effectively requiring Eilenberg–Zilber first. Not
recommended.

## 3. Blocker C — Künneth

`kunnethIso` needs, in order: A1 (UCT machinery, for the same splittings),
Eilenberg–Zilber (`C_*(X × Y) ≃ C_*(X) ⊗ C_*(Y)`, a chain homotopy equivalence —
the Alexander–Whitney map is one direction and the shuffle map the other), and
the algebraic Künneth for complexes of free modules over a PID. The **ring**
statement additionally needs B.

Per the design's §B.3 the campaign needs Künneth only for `S¹ × S⁵ × Y`, and in
the shape `H^*(S¹ × M) = H^*(M) ⊕ t·H^*(M)`. That special case still goes through
Eilenberg–Zilber; there is no shortcut through `S¹` alone, because the splitting
is asserted as a ring decomposition.

## 4. Ordering

```text
FreeSubmodulePID  ──►  UniversalCoefficients  ──►  Spheres
                                │
                                └──►  (with Eilenberg–Zilber)  ──►  Kunneth
CupProduct ──►  CupOne (Steenrod ⌣₁)  ──►  graded commutativity  ──►  cross_cup
```

`FreeSubmodulePID` and `CupOne` are independent of each other and of the
HamSandwich port, so they parallelize cleanly across lanes. Everything else is
serial.
</content>
