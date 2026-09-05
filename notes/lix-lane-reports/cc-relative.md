# cc-relative — relative mod-2 singular cohomology of a pair

Owner: lane `cc-relative`.  Files: `GroupApproximation/CharClass/Relative*.lean`,
namespace `GroupApproximation.CharClass`.  Everything is built over the vendored
`SphereOddDegree` singular (co)chain machinery (`cochainCxZMod2`, `cochainEval`,
`IsSubordinate`, `subChainSubmodule`, `subChainCorestrict`, `smallChainsInclusion`).

## 0. Module list (planned; stable interface for `cc-thom`)

| module | contents |
|---|---|
| `CharClass/RelativeCochains.lean` | `relCochainSubmodule`, `relCochainComplex`, `relCohomology`, `relInclusion`, `pairRestriction`, `pairShortComplex`, `pairShortExact` |
| `CharClass/RelativeLES.lean` | `relDelta`, exactness at the three spots, `relCohomology`-level names, `H^n(X, ∅) ≅ H^n(X)` |
| `CharClass/RelativeFunctorial.lean` | maps of pairs, functoriality, naturality of the LES, homeomorphism invariance of pairs, homotopy invariance of pairs |
| `CharClass/RelativeDual.lean` | dualization of a chain-level quasi-isomorphism over `ZMod 2` (`ZMod 2` is injective as a module over itself) |
| `CharClass/RelativeExcision.lean` | excision for an open cover, `H^*(X, U) ≅ H^*(V, U ∩ V)`; the `Z ⊆ interior A` form |
| `CharClass/RelativeLocal.lean` | `H^n(V, V ∖ {0}) ≅ F₂` for open `0 ∈ V ⊆ ℝⁿ`, independence of `V` |

## 1. Exported signatures (as authored)

All of these live in `GroupApproximation.CharClass`, with
`variable {R : Type} [CommRing R] {X : TopCat.{0}}`.  Take `R = ZMod 2`
downstream; then `cochainCx (ZMod 2) X = cochainCxZMod2 X` and
`(cochainCx (ZMod 2) X).homology n = cohomologyZMod2 X n`, both by `rfl`.

```lean
abbrev cochainCx (R : Type) [CommRing R] (X : TopCat.{0}) :
    CochainComplex (ModuleCat.{0} R) ℕ

def relCochainSubmodule (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    Submodule R (singularCochainGroup R X n)
-- carrier: {φ | ∀ σ, IsSubordinate A σ → cochainEval n φ σ = 0}

def relCochainComplex (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) :
    CochainComplex (ModuleCat.{0} R) ℕ

abbrev relCohomology (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    ModuleCat.{0} R                      -- H^n(X, A; R)

def relInclusion (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) :
    relCochainComplex R X A ⟶ cochainCx R X
def pairRestriction (R : Type) [CommRing R] {X : TopCat.{0}} (A : Set X) :
    cochainCx R X ⟶ cochainCx R (TopCat.of A)

def pairShortComplex (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) :
    ShortComplex (CochainComplex (ModuleCat.{0} R) ℕ)
theorem pairShortExact (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) :
    (pairShortComplex R X A).ShortExact
```

Long exact sequence (`RelativeLES.lean`), in element form; `j^*` is
`relToAbs`, `i^*` is `absToSub`, `δ` is `relDelta`:

```lean
def relToAbs  (R) (X) (A) (n) : relCohomology R X A n ⟶ (cochainCx R X).homology n
def absToSub  (R) (A) (n) : (cochainCx R X).homology n ⟶ (cochainCx R (TopCat.of A)).homology n
def relDelta  (R) (X) (A) (n) : (cochainCx R (TopCat.of A)).homology n ⟶ relCohomology R X A (n+1)

theorem relLES_exact_rel (n) :   -- at H^{n+1}(X, A):  δ then j^*
theorem relLES_exact_abs (n) :   -- at H^n(X):        j^* then i^*
theorem relLES_exact_sub (n) :   -- at H^n(A):        i^* then δ
```

## 2. GREEN (job counts)

*(nothing yet — first probe of `CharClass.RelativeCochains` in flight)*

## 3. AUTHORED, UNVERIFIED

* `GroupApproximation/CharClass/RelativeCochains.lean`.

## 4. NEEDS (from peers)

* `cc-cohom-api`: `H^k(S^n; F₂)` in element form (rank one for `k = 0, n`,
  vanishing otherwise) and homotopy invariance of `cohomologyZMod2` as an
  isomorphism for a homotopy equivalence.  If not available in time I prove the
  sphere facts from the vendored `SphereTopCohomologyRankOne` /
  `SphereModTwoTopClass` myself.

## 5. TRAPS

* The vendored cohomology is the *dual* of the singular chain complex, built
  categorically (`singularCochainComplexFunctor = op ⋙ opFunctor ⋙ linearYoneda`).
  Cochains are literally `ModuleCat` morphisms `C_n(X) ⟶ R`, so cochain-level
  constructions are best done as `Sigma.desc` out of the free chain group rather
  than elementwise.
* Surjectivity of `C^*(X) → C^*(A)` must not be proved by choosing a preimage
  simplex-by-simplex: use the vendored isomorphism `subChainCorestrict` (chains of
  the subspace `A` ≅ chains of `X` supported in `A`) together with the coordinate
  projection `subKeep` onto the `A`-supported chains, giving a chain-level
  *retraction* `relRetract` with `singularChainMap (sInclusion A) ≫ relRetract = 𝟙`.
  Then the cochain retraction is `ψ ↦ relRetract ≫ ψ` and surjectivity is one
  associativity rewrite.
