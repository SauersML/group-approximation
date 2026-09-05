# cc-thom — Thom class, relative Euler class, punctured-product recursion

Owns `GroupApproximation/CharClass/Thom*.lean` and
`GroupApproximation/CharClass/EulerLocal*.lean`, namespace
`GroupApproximation.CharClass`.

Notation throughout: `H^n X := cohomologyZMod2 X n : ModuleCat.{0} (ZMod 2)`
(vendored, `…/AlgebraicTopology/CohomologyCupProduct.lean`), spaces are
`TopCat.{0}`.

---

## 1. GREEN

*(job counts appear here as probes come back; a claim without a count is not a
claim)*

| module | jobs |
|---|---|
| — | — |

## 2. AUTHORED, UNVERIFIED

| module | content |
|---|---|
| `CharClass/ThomFieldTwo.lean` | `injective_of_surjective_of_linearEquiv`, `ne_zero_of_surjective_of_linearEquiv`, `surjective_of_exact_of_subsingleton`, `ModuleCat` restatements. The last step of Step C: a surjection between one-dimensional `F₂`-modules kills nothing. |
| `CharClass/ThomPuncturedCover.lean` | the two-set open cover of a punctured product: `leftPunctured`/`rightPunctured`, openness, `∪ = {(x₀,y₀)}ᶜ`, `∩ = (X∖x₀) × (Y∖y₀)`, the four homeomorphisms, and the cover as `Opens (puncturedProd x₀ y₀)` with `leftOpens ⊔ rightOpens = ⊤`. |

## 3. NEEDS

These are the exact signatures cc-thom builds against.  Until they exist they
are fields of `CohomologyToolkit` / `RelativeToolkit` (see
`CharClass/ThomPuncturedRecursion.lean`, `CharClass/EulerLocalNonvanishing.lean`):
local `structure`s, never `sorry`, never `axiom`.  Names may change; the
*shapes* are what cc-thom's proofs consume, and a lane that lands an
equivalent-or-stronger statement should say so here.

### From `cc-cohom-api`

**(A1) Mayer–Vietoris, vanishing form.**  This is the single most important one;
it is all the recursion uses of MV.  Stated over subspaces (`TopCat.of ↥U`),
i.e. downstream of the `SubChainSubspaceBridge` identification of
`subChainComplex R X ↑U` with the singular chains of `↥U`.

```lean
theorem isZero_cohomology_of_cover {Z : TopCat.{0}} (U V : TopologicalSpace.Opens Z)
    (hUV : U ⊔ V = ⊤) (m : ℕ)
    (hI : IsZero (cohomologyZMod2 (TopCat.of ↥(U ⊓ V)) m))
    (hU : IsZero (cohomologyZMod2 (TopCat.of ↥U) (m + 1)))
    (hV : IsZero (cohomologyZMod2 (TopCat.of ↥V) (m + 1))) :
    IsZero (cohomologyZMod2 Z (m + 1))
```

**(A2) Künneth, vanishing form.**  Again far weaker than full Künneth, and all
the recursion needs.

```lean
theorem isZero_cohomology_prod {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (p q : ℕ)
    (hA : ∀ a, p < a → IsZero (cohomologyZMod2 (TopCat.of A) a))
    (hB : ∀ b, q < b → IsZero (cohomologyZMod2 (TopCat.of B) b))
    (k : ℕ) (hk : p + q < k) :
    IsZero (cohomologyZMod2 (TopCat.of (A × B)) k)
```

**(A3) Homeomorphism invariance.**

```lean
def cohomologyCongr {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (n : ℕ) :
    cohomologyZMod2 (TopCat.of A) n ≅ cohomologyZMod2 (TopCat.of B) n
```

**(A4) Homotopy-equivalence invariance** (used for `S^n ∖ pt ≃ pt` and
`CP(d+1) ∖ pt ≃ CP(d)`; the second is already built in
`AlgTop/ComplexProjectivePunctureRetract.lean` as `punctureHomotopyEquiv`,
unverified).

```lean
def cohomologyCongrOfHomotopyEquiv {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : ContinuousMap.HomotopyEquiv A B) (n : ℕ) :
    cohomologyZMod2 (TopCat.of A) n ≅ cohomologyZMod2 (TopCat.of B) n
```

**(A5) Contractible spaces.**

```lean
theorem isZero_cohomology_of_contractible (A : Type) [TopologicalSpace A]
    [ContractibleSpace A] (n : ℕ) (hn : 0 < n) :
    IsZero (cohomologyZMod2 (TopCat.of A) n)
```

**(A6) The empty space** (base case `CP(0) ∖ pt = ∅`).

```lean
theorem isZero_cohomology_of_isEmpty (A : Type) [TopologicalSpace A] [IsEmpty A] (n : ℕ) :
    IsZero (cohomologyZMod2 (TopCat.of A) n)
```

**(A7) One-dimensionality of the top class** of the specific `N`, as a linear
equivalence (this is the form `ThomFieldTwo` consumes; an `IsIso`/`≅` with
`ModuleCat.of (ZMod 2) (ZMod 2)` is equally good):

```lean
def topCohomologyEquiv (N : TopCat.{0}) (twoR : ℕ) : cohomologyZMod2 N twoR ≃ₗ[ZMod 2] ZMod 2
```

### From `cc-relative`

**(B1) Relative cohomology and the restriction `j^*`.**

```lean
def relCohomologyZMod2 (X : TopCat.{0}) (A : Set X) (n : ℕ) : ModuleCat.{0} (ZMod 2)
def relRestrict (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    relCohomologyZMod2 X A n ⟶ cohomologyZMod2 X n
```

**(B2) Surjectivity of `j^*` from vanishing on the subspace** — the only piece
of the long exact sequence cc-thom uses.  (If you prefer, give me exactness at
`H^n X` as `LinearMap.range (relRestrict …).hom = LinearMap.ker (…).hom`; I have
`surjective_of_exact_of_subsingleton` to finish.)

```lean
theorem surjective_relRestrict_of_isZero (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (hA : IsZero (cohomologyZMod2 (TopCat.of ↥A) n)) :
    Function.Surjective (relRestrict X A n).hom
```

**(B3) Excision to a chart.**  For `V` open with `z ∈ V`:

```lean
def excisionIso (X : TopCat.{0}) (z : X) (V : Set X) (hV : IsOpen V) (hz : z ∈ V) (n : ℕ) :
    relCohomologyZMod2 X ({z}ᶜ) n
      ≅ relCohomologyZMod2 (TopCat.of ↥V) ((Subtype.val ⁻¹' ({z}ᶜ)) : Set ↥V) n
```

**(B4) Homeomorphism invariance of pairs** (this is what turns "the section is a
local homeomorphism at its zero" into "the class is the generator", with no
degree computation).

```lean
def relCohomologyCongr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) (B : Set Y) (hAB : e '' A = B) (n : ℕ) :
    relCohomologyZMod2 (TopCat.of X) A n ≅ relCohomologyZMod2 (TopCat.of Y) B n
```

**(B5) Functoriality for maps of pairs**, with `j^*` natural:

```lean
def relPullback {X Y : TopCat.{0}} (f : X ⟶ Y) (A : Set X) (B : Set Y)
    (hf : ∀ x, x ∈ A → f x ∈ B) (n : ℕ) :
    relCohomologyZMod2 Y B n ⟶ relCohomologyZMod2 X A n
theorem relRestrict_naturality … :
    relPullback f A B hf n ≫ relRestrict X A n
      = relRestrict Y B n ≫ (cohomologyZMod2 … ).map f  -- the two squares commute
```

**(B6) The local model, one dimensional with a named generator.**

```lean
def localGenerator (r : ℕ) :
    relCohomologyZMod2 (TopCat.of (Fin r → ℂ)) ({(0 : Fin r → ℂ)}ᶜ) (2 * r)
theorem localGenerator_ne_zero (r : ℕ) : localGenerator r ≠ 0
def localEquiv (r : ℕ) :
    relCohomologyZMod2 (TopCat.of (Fin r → ℂ)) ({(0 : Fin r → ℂ)}ᶜ) (2 * r) ≃ₗ[ZMod 2] ZMod 2
```

and the same for an open ball `D ⊆ ℂ^r` around `0` (or derive it from `B3`).

### From `cc-bundle`

**(C1)** the pair `(P(p ⊕ 1), P(p ⊕ 1) ∖ Z)` with `Z` the zero section, the
homotopy equivalence `P(p ⊕ 1) ∖ Z ≃ P(p)`, and the open inclusion of pairs
`(E(p), E(p) ∖ 0) ⊆ (P(p ⊕ 1), P(p ⊕ 1) ∖ Z)` satisfying the excision hypothesis
of `B3`.
**(C2)** the zero section `z₀ : X → E(p)` and pullback naturality of bundles.
**(C3)** a *trivializing chart* around a point: an open `U ∋ x` with a
homeomorphism of pairs `(E(p)|_U, E(p)|_U ∖ 0) ≅ (U × ℂ^r, U × (ℂ^r ∖ 0))`
commuting with the projection.
**(C4)** the rank-`r` trivial bundle over a point: `E = ℂ^r`, `E ∖ 0 = ℂ^r ∖ 0`.

### From `cc-projective`

**(D1)** `γ_i (E) : cohomologyZMod2 X (2 * i)` and the Leray–Hirsch freeness of
`H^*(P(E ⊕ 1))` over `H^*(X)` on `1, ξ, …, ξ^r`, of `H^*(P(E))` on
`1, …, ξ^{r-1}`, with the restriction sending `ξ ↦ ξ`.  cc-thom's
`ThomFreeModule.lean` turns exactly this into the Thom class; the interface it
consumes is *free module with a listed basis + a surjection matching the basis*,
so any concrete packaging of Leray–Hirsch that yields
`Module.Basis (Fin (r+1)) (H^*(X)) (H^*(P(E⊕1)))` will do.
**(D2)** `H^k(CP d) = 0` for `k > 2 d`, and `H^{2d}(CP d) ≃ₗ[ZMod 2] ZMod 2`.
**(D3)** `CP(d+1) ∖ pt ≃ CP(d)` as a homotopy equivalence *of the model
`Analysis/LIXProjectiveSpaceModel.lean`* (candidate already authored:
`AlgTop/ComplexProjectivePunctureRetract.punctureHomotopyEquiv`, unverified).
**(D4)** `H^k(S^n) = 0` for `k > n`, `H^n(S^n) ≃ₗ[ZMod 2] ZMod 2`, and
`S^n ∖ pt` contractible for `n ≥ 1` (stereographic projection; Mathlib's
`stereographic'` has source `{v}ᶜ`, target `univ`, so
`PartialHomeomorph.toHomeomorphSourceTarget` plus `Homeomorph.Set.univ` gives
`↥({v}ᶜ) ≃ₜ EuclideanSpace ℝ (Fin n)`, which is contractible).

### From `cc-lix-odd` / the lead

The instantiation of `EulerLocalNonvanishing`'s hypothesis structure for the
concrete `N = S¹ × S⁵ × ∏_j CP(d_j)` and the mapping-torus bundle `W_g`.

## 4. TRAPS

* The vendored Mayer–Vietoris (`AlgebraicTopology/MayerVietoris.lean`) is
  **homology** of `subChainComplex R X ↑U` (chains of `X` supported in `U`), not
  the singular chains of the subspace `↥U`, and `import Mathlib` sits at its
  head.  Cohomological MV over subspaces is a real piece of work; it is
  `cc-cohom-api`'s (A1) and everything of cc-thom's item 3 waits on it.
* `AlgTop/ComplexProjective*` and `AlgTop/BundleCalculus*` are **authored but
  never verified** (program note §3.7).  `AlgTop/PuncturedNormedSphere.lean` is
  fleet-green (8664 jobs) and already has
  `puncturedHomotopyEquivSphere : (E ∖ 0) ≃ S(E)` for a real normed space plus
  the real-linear homeomorphism `ℂ^n ≃ ℝ^{2n}`; reuse it rather than reproving.
