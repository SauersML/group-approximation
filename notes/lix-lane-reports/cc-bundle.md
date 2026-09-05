# Lane `cc-bundle`

Owns `GroupApproximation/CharClass/Bundle*.lean`, namespace
`GroupApproximation.CharClass`.  Deliverable: the geometry of complex vector
bundles in the projection model (§2 roster row `cc-bundle` of
`notes/LIX_FULL_PROGRAM_2026-09-05.md`).

## The model, fixed once (peers: this is the interface)

A bundle is a **bundled structure** over an arbitrary finite index type, not
over `Fin K`.  The campaign's own bundles are indexed by
`EIdx i = Fin 2 ⊕ HIdx i` (`Analysis/LIXBlockProjections.lean`), and block sums
are `ι ⊕ κ` with no `Fin` arithmetic and no casts.

```lean
structure Bundle (X : Type) [TopologicalSpace X] (ι : Type) [Fintype ι] where
  toFun : X → Matrix ι ι ℂ
  continuous_toFun : Continuous toFun
  isStarProjection_toFun : ∀ x, IsStarProjection (toFun x)
```

with a `FunLike` coercion, so `p x : Matrix ι ι ℂ`.  `CP d` is **always**
`STW59.CP d` from `Analysis/LIXProjectiveSpaceModel.lean`; no second model is
created anywhere in this lane.

Spaces are subtypes of a product, so `TopCat.of` applies directly:

```lean
def totalSet (p : Bundle X ι) : Set (X × (ι → ℂ)) := {v | p v.1 *ᵥ v.2 = v.2}
def sphereSet (p : Bundle X ι) : Set (X × (ι → ℂ))            -- ‖v‖ = 1 inside totalSet
def puncturedSet (p : Bundle X ι) : Set (X × (ι → ℂ))          -- totalSet minus the zero section
def projSet (p : Bundle X ι) : Set (X × Matrix ι ι ℂ) :=
  {z | IsStarProjection z.2 ∧ z.2.trace = 1 ∧ p z.1 * z.2 = z.2}
abbrev Total p := ↥(totalSet p)   abbrev Sphere p := ↥(sphereSet p)
abbrev Punctured p := ↥(puncturedSet p)   abbrev Proj p := ↥(projSet p)
```

The rank-one calculus that everything runs on (`BundleRankOne.lean`):

```lean
def eucNormSq (u : ι → ℂ) : ℝ := ∑ i, ‖u i‖ ^ 2
noncomputable def lineOf (u : ι → ℂ) : Matrix ι ι ℂ := ((eucNormSq u : ℂ))⁻¹ • rankOneProj u
theorem lineOf_smul (c ≠ 0) : lineOf (c • u) = lineOf u
theorem lineOf_of_mem_unitVectors : u ∈ unitVectors ι → lineOf u = rankOneProj u
theorem isStarProjection_lineOf / trace_lineOf (u ≠ 0)
theorem conj_rankOneProj (a) (u) : a * rankOneProj u * aᴴ = rankOneProj (a *ᵥ u)
```

## Module plan

| module | content |
|---|---|
| `BundleBasic.lean` | the structure, `FunLike`, `triv`, `comap` (pullback), `blockSum`, the bridge `Matrix ι ι C(X,ℂ) ↔ Bundle X ι`, `Bundle.Iso` (rectangular continuous MvN) and its equivalence with the repo's `MurrayVonNeumannEquiv` in the square case, `rank` |
| `BundleRankOne.lean` | `eucNormSq`, `lineOf`, `conjNormalize`, the rank-one calculus above |
| `BundleSpace.lean` | `totalSet`/`sphereSet`/`puncturedSet`/`projSet`, topology, compactness of `Sphere`/`Proj`, `TopCat.of` objects and morphisms, zero section, `π`, the tautological line `taut p : Bundle (Proj p) ι`, and `Proj p ≃ₜ ↥{z : X × CP d | p z.1 * z.2 = z.2}` for `ι = Fin (d+1)` |
| `BundleHomotopy.lean` | `Total p ≃ₕ X`, `Punctured p ≃ₕ Sphere p`, `Proj (p.plusOne) ∖ Z ≃ₕ Proj p`, `Total p ≃ₜ (open subset) Proj (p.plusOne) ∖ Proj p`, `Proj p` closed in `Proj p.plusOne` |
| `BundleLocal.lean` | the intertwiner `z(x) = p x₀ · p x + (1 − p x₀)(1 − p x)`, invertibility on an open neighbourhood, local trivializations of `Total`/`Sphere`/`Proj`, the finite cover of a compact base, `rank` locally constant, the standard fibre (`W` with `Wᴴ W = 1`, `W Wᴴ = p x₀`) and `Proj p |_U ≃ₜ U × CP (r−1)`, `Total p |_U ≃ₜ U × (Fin r → ℂ)` |
| `BundleInvariance.lean` | `Iso p q → Total p ≃ₜ Total q` and `Proj p ≃ₜ Proj q` over `X`, taut compatibility, and the homotopy of classifying maps of isomorphic line bundles |

**No `‖·‖` on `Matrix` anywhere.**  There is no norm instance on `Matrix` at the
pin, and `unitaryConj_of_norm_sub_lt_one`
(`AlgTop/BundleCalculusProjection.lean`) needs a `CStarAlgebra` structure that
`Matrix ι ι ℂ` does not have.  Local triviality is obtained instead from the
**invertible intertwiner** `z(x) = p x₀ · p x + (1 − p x₀)(1 − p x)`, which
satisfies `z(x) · p x = p x₀ · z(x)` and `z(x₀) = 1`, so
`{x | IsUnit (z x)} = {x | det (z x) ≠ 0}` is an open neighbourhood of `x₀` on
which `z` and `z⁻¹` are continuous (`Continuous.matrix_det`,
`Continuous.matrix_adjugate`, `Matrix.inv_def`).  This needs **no square root,
no CFC, and no norm**, and it is strictly more general than the
`‖p x − p x₀‖ < 1` criterion.  For the *projective* bundle a non-unitary
intertwiner is enough because the line it produces is renormalized:
`conjNormalize a q := (trace (a q aᴴ))⁻¹ • (a q aᴴ)`, which for `q = rankOneProj u`
is `lineOf (a *ᵥ u)`.

## GREEN

*(nothing yet — first probe in flight)*

## AUTHORED, UNVERIFIED

*(see the module plan; updated as files land)*

## NEEDS

Nothing from a peer: this lane is a leaf over `Analysis/LIXProjectiveSpaceModel`
(GREEN) and `Analysis/FiniteCStarMurrayVonNeumann` (in the root, green).
`Analysis/LIXBlockProjections.lean` is deliberately **not** imported (it is red
and owned by `cs-stages`); the campaign spaces are re-stated over
`STW59.unitVectors (Fin 3)` and `STW59.CP`, which are the definitions
`sphereFive`/`baseY` unfold to.

## TRAPS

*(none recorded yet)*
