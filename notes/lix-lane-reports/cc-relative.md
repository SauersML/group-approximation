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
| `CharClass/RelativeSmallChains.lean` | cochains vanishing on all `𝒰`-small chains form an acyclic subcomplex (`smallAnnComplex_acyclic`) — the geometric input excision needs |
| `CharClass/RelativeExcision.lean` | excision for an open cover, `H^*(X, U) ≅ H^*(V, U ∩ V)` (`excisionIso`); the `Z ⊆ interior A` form |
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

All six planned modules are green, including built together in one probe
(8734 jobs, matching the largest individual count — nothing regressed
cross-module):

* `RelativeCochains.lean` — 8728 jobs
* `RelativeLES.lean` — 8729 jobs
* `RelativeFunctorial.lean` — 8730 jobs
* `RelativeDual.lean` — 8730 jobs
* `RelativeSmallChains.lean` — 8731 jobs
* `RelativeExcision.lean` — 8734 jobs

The two systematic issues the predecessor (Opus) session flagged before
hitting its limit — "a nested type-ascription that Lean won't accept, and an
implicit-argument mismatch blocking instance search" — are both fixed; see §5
for the exact mechanism and the general recipe used throughout.

## 3. AUTHORED, UNVERIFIED

* `GroupApproximation/CharClass/RelativeLocal.lean` — not yet started
  (`H^n(V, V ∖ {0}) ≅ F₂` for open `0 ∈ V ⊆ ℝⁿ`). Everything it needs
  (excision, the LES, homeomorphism invariance) is now green and available.

## 4. NEEDS (from peers)

* For `RelativeLocal.lean`: `H^k(S^n; F₂)` in element form (rank one at
  `k = 0, n`, vanishing otherwise) from `cc-cohom-api`/`cc-projective`, plus
  homotopy invariance of `cohomologyZMod2` for a homotopy equivalence (needed
  to reduce a general open `V` to a ball). If not available in time, prove the
  sphere facts from the vendored `SphereTopCohomologyRankOne` /
  `SphereModTwoTopClass` directly.

## 5. TRAPS

* **The dominant failure mode this session, by far**: `ModuleCat` objects
  built via `ChainComplex.of`/`HomologicalComplex.Hom` fields (e.g.
  `(subChainComplex R X A).X n`, `(relCochainComplex R X A).X n`) are `rfl`-equal
  to a "nice" label (`ModuleCat.of R (subChainSubmodule R X A n)`, a bare
  submodule) but **not syntactically equal**, and the equality requires
  unfolding a regular (non-reducible) `def`. `rw`/`simp`'s motive-abstraction
  and **instance search** both operate at `instances` transparency and cannot
  see through this unfold, so:
  - `rw`-ing through a `≫`-composite whose middle object was "baked in" from
    one side's native type (elaboration order: the first morphism in a `≫`
    fixes the middle object from *its* codomain) fails with "did not find
    occurrence" or a downstream "application type mismatch", even though the
    composite type-checked fine when originally *defined*.
  - A **nested type ascription** `((e : T1) : T2)` used in a *statement*
    (not a tactic) can silently drop the inner `T1` and try to coerce `e`
    directly to `T2`, failing exactly when `e`'s native type is merely
    `rfl`-equal (not syntactically equal) to `T1` — this is *not* about
    parenthesization; it reproduces even with correct nesting.
  - Instance search for a class like `IsIso`/`Mono`/`Epi` fails to find a
    `have`d instance stated for a differently-labeled but `rfl`-equal
    expression (e.g. `Mono (HomologicalComplex.homologyMap g n)` vs the goal's
    `Mono (relPullback R f hf n)`, `g` and `relCochainMap R f hf`
    interchangeable only by unfolding `excisionCochainMap`/`excisionShortComplex`).
  - A `section`-level `variable` that is *only used in a proof body*, never
    mentioned in a declaration's stated *type*, is **not** auto-bound — the
    body then sees "unknown identifier". Grep every `variable` line's names
    against each subsequent declaration's own signature, not just its proof.
  **The fix that actually works, uniformly**: never let `rw`/`simp`/instance
  search reconstruct or search across the "clunky ↔ nice" gap. Options, in
  order of preference:
  1. **Relabel one endpoint of the exact composition that needs to be clean**
     with a thin wrapper `def` whose *stated* domain/codomain is the other
     side's native type (see `subChainSubtypeAt`, `subKeepAt`,
     `subChainCorestrictInv` in `RelativeCochains.lean` — the latter's
     domain is deliberately kept "clunky" because `IsIso` instance search
     needs it at the exact shape `subChainCorestrict_f_isIso` was stated at;
     wrap the *other* morphism in the composition instead).
  2. Prove the needed fact via a **universally quantified `key : ∀ ψ : <nice
     type>, P ψ`**, then apply it with **ordinary Pi-application** (`key φ`
     with `φ : <clunky type>`) — ordinary application uses full defeq and
     accepts the clunky-typed argument; only `rw`/ascription fail. This is
     the `relCochainMap_id`/`smallAnn_comp`/`smallAnnToRel_comp` pattern.
  3. `show` (full defeq, not ascription/rw) to restate a *goal* — including
     to unfold a *transparent wrapper `def`* (e.g. `subKeepAt` → `subKeep`)
     before invoking a lemma stated for the unwrapped name — but never to
     bridge a genuine clunky/submodule gap (that still needs (1) or (2)).
  4. Building `have h := congrArg f hyp` **without** an explicit ascribed
     type works fine (Lean infers `h`'s type naturally); the failure mode is
     specifically adding your *own* mismatched ascription on top.
  5. `congrArg`/`Subtype.ext` composed directly inside a call whose *outer*
     expected type can propagate backward into unifying `congrArg`'s implicit
     endpoints (e.g. `Subtype.ext (congrArg Subtype.val hab)` when `hab`'s own
     type isn't literally `a = b`) — split into two `have`s instead so the
     first is computed forward with no imposed expected type.
* Surjectivity of `C^*(X) → C^*(A)` must not be proved by choosing a preimage
  simplex-by-simplex: use the vendored isomorphism `subChainCorestrict` (chains of
  the subspace `A` ≅ chains of `X` supported in `A`) together with the coordinate
  projection `subKeep` onto the `A`-supported chains, giving a chain-level
  *retraction* `relRetract` with `singularChainMap (sInclusion A) ≫ relRetract = 𝟙`.
  Then the cochain retraction is `ψ ↦ relRetract ≫ ψ` and surjectivity is one
  associativity rewrite.
* `CategoryTheory.Functor.map_id` is shadowed by the ambient (non-category)
  `Functor` typeclass's own `map_id` when `open CategoryTheory` is active;
  qualify it fully.
* `(ConcreteCategory.hom (𝟙 X)) x = x` is **not** `rfl` in general (it goes
  through `CategoryTheory.id_apply`, `@[simp]`); don't assume identity
  morphisms reduce definitionally on points.
