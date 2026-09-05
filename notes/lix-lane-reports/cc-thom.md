# cc-thom — Thom class, relative Euler class, punctured-product recursion

Owns `GroupApproximation/CharClass/Thom*.lean` and
`GroupApproximation/CharClass/EulerLocal*.lean`, namespace
`GroupApproximation.CharClass`.

Notation: `H^n X := cohomologyZMod2 X n : ModuleCat.{0} (ZMod 2)` (vendored,
`…/AlgebraicTopology/CohomologyCupProduct.lean`; this is `cc-cohom-api`'s
`Hmod2 X n` reducibly), spaces are `TopCat.{0}`.

---

## 1. GREEN

Probe of all nine modules together: **`Build completed successfully (2911 jobs)`**,
`ERROR_LINES=0`, `LAKE_EXIT=0` (private clone `cc_clones/cc-thom`, 2026-09-05).
Every module below has a `Built …` line, not `Replayed`, for its current bytes.

| module | content |
|---|---|
| `CharClass/ThomFieldTwo.lean` | `injective_of_surjective_of_linearEquiv`, `ne_zero_of_surjective_of_linearEquiv`, `surjective_of_exact_of_subsingleton`, `ModuleCat` restatements |
| `CharClass/ThomPuncturedCover.lean` | the two-set open cover of a punctured product and its four homeomorphisms, as sets and as `Opens` |
| `CharClass/ThomPuncturedSphere.lean` | `spherePuncturedHomeo`, `ContractibleSpace ↥({v}ᶜ)` for the unit sphere of any real inner product space |
| `CharClass/ThomFreeModule.lean` | the Leray–Hirsch linear algebra: `thomGenerator`, `surjective_of_basis`, `ker_eq_span_thomGenerator`, `existsUnique_smul_thomGenerator`, `existsUnique_lift`, `existsUnique_smul_of_injective_of_range` |
| `CharClass/EulerLocalChart.lean` | `homeomorphCompl`, `compl_singleton_subtype`, `chartPairHomeo`, `openPartialHomeomorphChartPair` |
| `CharClass/ThomPuncturedRecursion.lean` | `isZero_of_linearEquiv`, `CohomologyToolkit`, `PuncturedAcyclic`, the two base-case constructors, `PuncturedAcyclic.prod`, `isZero_punctured_top` |
| `CharClass/EulerLocalNonvanishing.lean` | `ne_zero_of_map_ne_zero`, `rankOneOfIso`, `range_eq_ker_of_exact`, `surjective_of_punctured_acyclic`, `topChernClass_ne_zero` |
| `CharClass/ThomEulerNaturality.lean` | `hom_apply_comp`, `topClass_eq_of_naturality`, `topClass_eq_of_naturality'` |
| `CharClass/ThomPuncturedPi.lean` | `piFinSuccHomeo`, `PuncturedAcyclic.congr`, `puncturedAcyclic_pi` |

Job count: 2911.

## 2. AUTHORED, UNVERIFIED

Nothing outstanding; every cc-thom module is in §1.  What remains is
*instantiation*: `CohomologyToolkit` and the hypotheses of
`topChernClass_ne_zero` are `structure` fields / explicit hypotheses, never
`sorry` and never `axiom`, and §3 says exactly who owes each of them.

## 3. NEEDS

### From `cc-cohom-api`

**Already exported and usable** (no action): `Hmod2` (reducibly
`cohomologyZMod2`), `pullEquivOfHomeomorph`, `pullEquivOfHomotopyEquiv`.  These
give the `homeo` and `homotopy` fields of `CohomologyToolkit` through
`ThomPuncturedRecursion.isZero_of_linearEquiv`.

Still needed:

**(A1) Mayer–Vietoris, vanishing form.**  The single most important one; it is
all the recursion uses of MV.  Over subspaces, i.e. downstream of the
`SubChainSubspaceBridge` identification of `subChainComplex R X ↑U` with the
singular chains of `↥U`.  Note the vendored `AlgebraicTopology/MayerVietoris.lean`
is *homology*; the cohomological statement is the real work.

```lean
theorem isZero_cohomology_of_cover (Z : Type) [TopologicalSpace Z]
    (U V : TopologicalSpace.Opens Z) (hUV : U ⊔ V = ⊤) (m : ℕ)
    (hI : IsZero (cohomologyZMod2 (TopCat.of ↥(U ⊓ V)) m))
    (hU : IsZero (cohomologyZMod2 (TopCat.of ↥U) (m + 1)))
    (hV : IsZero (cohomologyZMod2 (TopCat.of ↥V) (m + 1))) :
    IsZero (cohomologyZMod2 (TopCat.of Z) (m + 1))
```

**(A2) Künneth, vanishing form.**  Far weaker than a cohomology cross product,
and *unconditional* over a field: `H^a(A;F₂) = 0 ↔ H_a(A;F₂) = 0` by the
universal coefficient theorem (`AlgTop/UniversalCoefficients.lean` has both
halves), and the homology Künneth theorem over a field has no finiteness
hypotheses.  Route it that way rather than through a cohomology cross product.

```lean
theorem isZero_cohomology_prod (A B : Type) [TopologicalSpace A] [TopologicalSpace B]
    (p q : ℕ)
    (hA : ∀ a, p < a → IsZero (cohomologyZMod2 (TopCat.of A) a))
    (hB : ∀ b, q < b → IsZero (cohomologyZMod2 (TopCat.of B) b))
    (k : ℕ) (hk : p + q < k) :
    IsZero (cohomologyZMod2 (TopCat.of (A × B)) k)
```

**(A5) Contractible spaces.**  *Authored* as
`CohomologyContractible.cohomology_isZero_of_contractible`; once it is green the
`contractible` field of `CohomologyToolkit` is filled by it directly.

**(A6) The empty space** (base case `CP(0) ∖ pt = ∅`), same shape with
`[IsEmpty A]` and no degree restriction.

**(A7) One-dimensionality of the top class** of the concrete
`N = S¹ × S⁵ × ∏_j CP(d_j)`, as a linear equivalence (that is the form
`ThomFieldTwo` consumes):

```lean
def topCohomologyEquiv (N : TopCat.{0}) (twoR : ℕ) :
    cohomologyZMod2 N twoR ≃ₗ[ZMod 2] ZMod 2
```

### From `cc-relative`

**Already planned and matching** (no action): `relCohomology R X A n`, `relToAbs`
(my `j`), `absToSub` (my `i`), `relLES_exact_abs` (exactness at `H^n(X)`).
`EulerLocalNonvanishing.topChernClass_ne_zero` takes those three as arguments,
in the form `LinearMap.range j.hom = LinearMap.ker i.hom`.  **No action is needed
if `relLES_exact_abs` is a `ShortComplex.Exact`**: Mathlib's
`ShortComplex.Exact.moduleCat_range_eq_ker` converts, and it is re-exported as
`EulerLocalNonvanishing.range_eq_ker_of_exact` so the call site needs no search.

Still needed:

**(B3) Excision to a chart.**  For `V` open with `z ∈ V`:

```lean
def excisionIso (X : TopCat.{0}) (z : X) (V : Set X) (hV : IsOpen V) (hz : z ∈ V) (n : ℕ) :
    relCohomology (ZMod 2) X ({z}ᶜ) n
      ≅ relCohomology (ZMod 2) (TopCat.of ↥V) ((Subtype.val ⁻¹' ({z}ᶜ)) : Set ↥V) n
```

`EulerLocalChart.compl_singleton_subtype` proves
`({⟨z, hz⟩}ᶜ : Set ↥V) = Subtype.val ⁻¹' ({z}ᶜ)`, so either spelling of the
second pair is fine.

**(B4) Homeomorphism invariance of pairs.**  This is what turns "the section is a
local homeomorphism at its zero" into "the class is the generator", with no
degree computation.  `EulerLocalChart.chartPairHomeo` supplies the topological
half (the chart is a homeomorphism *of pairs*).

```lean
def relCohomologyCongr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) (B : Set Y) (hAB : e '' A = B) (n : ℕ) :
    relCohomology (ZMod 2) (TopCat.of X) A n ≅ relCohomology (ZMod 2) (TopCat.of Y) B n
```

**(B5) Functoriality for maps of pairs**, with `j^*` natural.  Consumed by
`ThomEulerNaturality.topClass_eq_of_naturality'` as the square
`σ^*_{pair} ≫ j^*_X = j^*_E ≫ σ^*`.

**(B6) The local model, one dimensional with a named generator.**

```lean
def localGenerator (r : ℕ) :
    relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) ({(0 : Fin r → ℂ)}ᶜ) (2 * r)
theorem localGenerator_ne_zero (r : ℕ) : localGenerator r ≠ 0
def localEquiv (r : ℕ) :
    relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) ({(0 : Fin r → ℂ)}ᶜ) (2 * r)
      ≃ₗ[ZMod 2] ZMod 2
```

Shortcut: `AlgTop/PuncturedNormedSphere.lean` is **fleet-green (8664 jobs)** and
already contains
`complexPuncturedHomotopyEquivSphere d : {w : Fin (d+1) → ℂ // w ≠ 0} ≃ₕ ↥(sphere (0 : EuclideanSpace ℝ (Fin (2*(d+1)))) 1)`
together with the real-linear homeomorphism `ℂ^n ≃ ℝ^{2n}`.  The subtype
`{w // w ≠ 0}` is *definitionally* `↥({0}ᶜ)`, so this plugs straight into the
long exact sequence of `(ℂ^r, ℂ^r ∖ 0)`.  Do not reprove it.

### From `cc-bundle`

**(C1)** the pair `(P(p ⊕ 1), P(p ⊕ 1) ∖ Z)` with `Z` the zero section, the
homotopy equivalence `P(p ⊕ 1) ∖ Z ≃ P(p)`, and the open inclusion of pairs
`(E(p), E(p) ∖ 0) ⊆ (P(p ⊕ 1), P(p ⊕ 1) ∖ Z)` satisfying (B3)'s hypothesis.
**(C2)** the zero section `z₀`, the projection `π` with `π ∘ z₀ = id` and
`π ∘ s = id` for a section `s`, and pullback naturality of bundles.
**(C3)** a *trivializing chart* around a point: an open `U ∋ x` with a
homeomorphism of pairs `(E(p)|_U, E(p)|_U ∖ 0) ≅ (U × ℂ^r, U × (ℂ^r ∖ 0))`
commuting with the projection.
**(C4)** the rank-`r` trivial bundle over a point: `E = ℂ^r`, `E ∖ 0 = ℂ^r ∖ 0`.

### From `cc-projective`

**(D1)** Leray–Hirsch in the shape `ThomFreeModule` consumes: a
`Module.Basis (Fin (r+1)) (H^*(X)) (H^*(P(E⊕1)))` on `1, ξ, …, ξ^r`, a
`Module.Basis (Fin r) (H^*(X)) (H^*(P(E)))` on `1, …, ξ^{r−1}`, and the two
equations describing the restriction on the basis
(`ρ (b i.castSucc) = b' i` and `ρ (b (Fin.last r)) = -∑ i, γ_{r−i} • b' i`).
Any packaging of Leray–Hirsch producing those two bases will do; the `evenRing`
you are building is a fine base ring.
**(D2)** `H^k(CP d) = 0` for `k > 2d`, and `H^{2d}(CP d) ≃ₗ[ZMod 2] ZMod 2`.
**(D3)** `CP(d+1) ∖ pt ≃ₕ CP(d)` for the model of
`Analysis/LIXProjectiveSpaceModel.lean`.  A candidate is already authored (and
unverified) as `AlgTop/ComplexProjectivePunctureRetract.punctureHomotopyEquiv`;
its `punctured d = {x | x ≠ basePoint (d+1)}` is definitionally
`({basePoint (d+1)}ᶜ : Set (CP (d+1)))`, which is the shape
`puncturedAcyclic_of_homotopyEquiv` wants.
**(D4)** `H^k(S^n) = 0` for `k > n` and `H^n(S^n) ≃ₗ[ZMod 2] ZMod 2`.  The other
half of the sphere base case, `S^n ∖ pt` contractible, is **done and green** in
`CharClass/ThomPuncturedSphere.lean` for `Metric.sphere (0 : E) 1` in any real
inner product space; use it rather than reproving.

**Duplication to resolve (lead).**  `cc-cohom-api` has since authored
`CharClass/CohomologySphereComplement.lean` with the same stereographic argument
(`spherePunctureHomeo`, `contractibleSpace_sphere_compl`) for the vendored
`Sphere n`.  cc-thom's `ThomPuncturedSphere.lean` is green and general (any real
inner product space, `Metric.sphere (0 : E) 1`); theirs is specialised to the
vendored model.  Keeping both is harmless but one of them should be retired once
the concrete sphere model for `S¹`, `S⁴`, `S⁵` is fixed.  cc-thom will not touch
a peer's file.

### From `cc-lix-odd` / the lead

Instantiate `CohomologyToolkit` once (five fields, all listed above), then
`topChernClass_ne_zero` for the concrete `N` and the mapping-torus bundle `W_g`.
The dimension bookkeeping for `N = S¹ × S⁵ × ∏_j CP(d_j)` is
`puncturedAcyclic_pi` (for the `∀ j : Fin l, CP (d j)` factor, matching
`Analysis/LIXBlockProjections`'s `baseY`) followed by two `PuncturedAcyclic.prod`
steps, or one `puncturedAcyclic_pi` over the whole family.

## 4. TRAPS

* **The vendored Mayer–Vietoris is homology, not cohomology.**
  `AlgebraicTopology/MayerVietoris.lean` builds the long exact sequence of
  `subChainComplex R X ↑U` (chains of `X` supported in `U`), and carries
  `import Mathlib` at its head.  Everything in cc-thom's item 3 waits on the
  cohomological version, (A1).
* **`autoImplicit` is on in this project.**  A missing import shows up as
  "Function expected at `ContractibleSpace` but this term has type `?m`", not as
  "unknown identifier".  `CharClass/ThomPuncturedRecursion.lean` needed explicit
  `Mathlib.Topology.Homotopy.Equiv` and `Mathlib.Topology.Homotopy.Contractible`
  imports; the vendored cohomology modules do not pull them in.
* **`0 + 1` is not `1` for instance search.**  `Homeomorph.piUnique` over
  `Fin (0 + 1)` fails with "failed to synthesize `Unique (Fin (0 + 1))`" inside a
  `Nat.rec` zero branch; `haveI : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))`
  fixes it.
* **An inline `Finset.sum_congr rfl (fun i _ => by rw [...])` inside a `rw` list
  leaves the sum's target a metavariable** and the inner `rw` then fails on a
  goal `… = ?m i`.  Always `have hsum : ∑ … = ∑ … := Finset.sum_congr rfl …`
  first, then `rw [hsum]`.
* **`rw [← h]` where `h`'s subject occurs in the *type* of a bound variable** is
  a motive error: in `homeomorphCompl`, `y : ↥({e a}ᶜ)` mentions `a`, so
  `rw [← h, e.apply_symm_apply]` is impossible.  Chain the equalities by hand
  (`(e.apply_symm_apply ↑y).symm.trans (congrArg e h)`).
* **Warnings are errors**: unused section variables (`omit [Finite R] in` before
  the docstring), unused simp arguments, and named-but-unreferenced binders in
  structure instance fields (`left_inv _ :=`, not `left_inv x :=`).
* **The first probe of a fresh clone dies with `Argument list too long`**: the
  initial rsync reports the whole tree as changed and the script builds one
  `rm -f` argument per changed module.  Re-run once; the second probe syncs only
  what actually changed.
* `AlgTop/ComplexProjective*` and `AlgTop/BundleCalculus*` are **authored but
  never verified**.  `AlgTop/PuncturedNormedSphere.lean` and
  `AlgTop/UniversalCoefficients.lean` are worth reading before reproving
  anything about punctured normed spaces or the universal coefficient theorem.

## 5. Probe log

| date | targets | result |
|---|---|---|
| 2026-09-05 | 5 Mathlib-only modules | 3 green, 2 red (localized) |
| 2026-09-05 | 9 modules | 8 green, `ThomPuncturedPi` red on `Unique (Fin (0+1))` |
| 2026-09-05 | 9 modules | **green, 2910 jobs** |
| 2026-09-05 | 9 modules, after adding `rankOneOfIso` / `range_eq_ker_of_exact` | **green, 2911 jobs** |
| 2026-09-05 | 9 modules, after adding `openPartialHomeomorphChartPair` | **green, 2911 jobs** |
