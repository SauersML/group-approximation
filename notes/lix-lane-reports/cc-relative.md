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
| `CharClass/RelativeLocal.lean` | (B3) `excisionIsoPoint`, (B4) `relCohomologyCongr` — both **green**, delivered per `cc-thom`'s exact request (see §6). (B6) the local generator is **not yet attempted**; route verified, see §6. |

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

## 6. `RelativeLocal.lean`: what's delivered and the verified route for (B6)

Delivered (green, 8735 jobs), reading `cc-thom`'s exact request
(`notes/lix-lane-reports/cc-thom.md` §"From `cc-relative`"):

* **(B3)** `excisionIsoPoint X z V hV hz n` — `pointComplementOpen X z : Opens X`
  is `{z}ᶜ` (needs `[T1Space X]` for `IsOpen`), `pointComplement_sup` shows it
  covers `X` with any open `V ∋ z`, and the whole thing is a one-line
  application of `RelativeExcision.excisionIso`.
* **(B4)** `relCohomologyCongr e A B hAB n` — apply `RelativeFunctorial.relPairIso`
  to `TopCat.isoOfHomeo e.symm` (note the `.symm`: `relPairIso`'s conclusion is
  `H^*(target) ≅ H^*(source)` for `e : source ≅ target`, so to land
  `H^*(X,A) ≅ H^*(Y,B)` the iso must go `Y ≅ X`); the two membership
  hypotheses are one-liners from `hAB : e '' A = B`.
* (B5) functoriality was already `relToAbs_naturality` — no action needed.

**(B6) — not attempted, but the route is fully verified and every piece it
needs is confirmed to exist and line up:**

```lean
def localGenerator (r : ℕ) :
    relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) ({(0 : Fin r → ℂ)}ᶜ) (2 * r)
theorem localGenerator_ne_zero (r : ℕ) : localGenerator r ≠ 0
def localEquiv (r : ℕ) : … ≃ₗ[ZMod 2] ZMod 2
```

For `r ≥ 1` (write `r = d + 1`):

1. `↥({(0:Fin r→ℂ)}ᶜ)` is definitionally `{w : Fin r → ℂ // w ≠ 0}` (both
   unfold `Set.mem_compl_iff`/`Set.mem_singleton_iff`, `Iff.rfl` all the way).
2. `AlgTop/PuncturedNormedSphere.lean`'s `complexPuncturedHomotopyEquivSphere d`
   (fleet-green, 8664 jobs, **do not reprove**) is a `ContinuousMap.HomotopyEquiv`
   from that subtype to `↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2*(d+1)))) 1)`,
   which **is** `SphereOddDegree.Basic.Sphere (2*d+1)` up to the `Nat` identity
   `2*(d+1) = (2*d+1)+1` (true by `rfl`: `Nat.add` recurses on the second
   argument, so `a+2 = Nat.succ (a+1) = (a+1)+1`). So this is homotopy
   equivalent to `Sphere (2*r - 1)`.
3. `cc-cohom-api`'s `CohomologySphere.lean` (green) has exactly the needed
   facts on `Sphere (2*r-1)` in its **top** degree `2*r-1`:
   `sphere_coh_top_finrank`, `sphereTopClass`, `sphereTopClass_ne_zero`,
   `sphereTopEquiv : Hmod2 (Sphere (2r-1)) (2r-1) ≃ₗ[ZMod 2] ZMod 2`. `Hmod2`
   is reducibly `cohomologyZMod2`, itself `rfl`-equal to
   `(cochainCx (ZMod 2) X).homology n` (this file's `cochainCx`) — so a
   homotopy-equivalence-induced isomorphism on `Hmod2` transports directly to
   `(cochainCx (ZMod 2) _).homology (2r-1)`, the absolute term the LES needs.
   (Homotopy invariance itself: check `cc-cohom-api`'s `CohomologyBridge.lean`
   for the exact induced-isomorphism statement to cite, rather than reproving.)
4. `Fin r → ℂ` is contractible (it's a vector space), so
   `(cochainCx (ZMod 2) (TopCat.of (Fin r → ℂ))).homology k` is zero for
   `k = 2r-1` **and** `k = 2r` — cite `cc-cohom-api`'s `CohomologyContractible.lean`.
5. With both those vanishing, `RelativeLES.isIso_relDelta`/`relDeltaIso` (this
   file, green) gives `relDelta _ _ _ (2r-1) : (cochainCx _ (TopCat.of ↥({0}ᶜ))).homology (2r-1)
     ≅ relCohomology (ZMod 2) (Fin r→ℂ) ({0}ᶜ) (2r)` — exactly the target type,
   with degree `(2r-1)+1 = 2r` matching by `rfl` for the same `Nat.add` reason
   as step 2.
6. Chase the nonzero class `sphereTopClass (2*r-1) (by omega)` backward through
   steps 3→2→1 (transport along the homotopy-equivalence iso, defeq-identify
   the subtype, then apply) to land in `(cochainCx _ (TopCat.of ↥({0}ᶜ))).homology (2r-1)`,
   then push forward through `relDeltaIso.hom` from step 5 to define
   `localGenerator r`. `localGenerator_ne_zero` and `localEquiv` follow since
   every step in the chain is an isomorphism (or, for step 6's forward push,
   `relDeltaIso` itself).

The `r = 0` edge case (not excluded by `cc-thom`'s signature) is a **different,
easier** argument: `({(0:Fin 0→ℂ)}ᶜ) = ∅` (the only element of `Fin 0 → ℂ` is
`0`), so `relEmptyIso` (`RelativeLES.lean`, green) gives
`relCohomology (ZMod 2) (Fin 0→ℂ) ∅ 0 ≅ (cochainCx (ZMod 2) (Fin 0→ℂ)).homology 0`,
nonzero since `Fin 0 → ℂ` is a nonempty (one-point) path-connected space
(`cc-cohom-api`'s `cohZero_finrank`/`cohZeroEquiv`). Whoever picks this up:
handle `r = 0` and `r ≥ 1` as two separate cases from the start rather than
trying to unify them.

None of steps 1–6 were executed or probed; this is a plan, not a claim of
partial progress.
