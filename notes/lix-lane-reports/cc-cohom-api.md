# cc-cohom-api

Lane of `notes/LIX_FULL_PROGRAM_2026-09-05.md`.  Owns
`GroupApproximation/CharClass/Cohomology*.lean`, namespace
`GroupApproximation.CharClass`.

Everything is the **vendored** mod-2 singular cohomology
(`GroupApproximation/ThirdParty/HamSandwich/SphereOddDegree/AlgebraicTopology/`),
repackaged element-wise.  Spaces are `TopCat.{0}`; `Hmod2 X n` is a
`ModuleCat (ZMod 2)` and is *reducibly* the vendored `cohomologyZMod2 X n`, so a
peer may mix the two vocabularies freely.

## Module map

| module | contents |
|---|---|
| `CohomologyBasic.lean` | `Hmod2`, `cohCast`, `cup` (`⌣`), `one`, `pull`, bilinearity, right unitality, naturality, functoriality |
| `CohomologyAssoc.lean` | degree relabelling of simplices, `cochainCup_assoc`, `cup_assoc`, `one_cup`, the cast calculus |
| `CohomologyBridge.lean` | `TopCat.of` plumbing for concrete `Type`s, subspace restriction, products, homotopy invariance, `H^*(X × [0,1])`, `H^*(X × ℝ^k)` |
| `CohomologySphere.lean` | `H^k(S^n; F₂)`: vanishing range, top-degree generator, `H^0` of a path-connected space |
| `CohomologyContractible.lean` | `H^k(pt) = 0` for `k ≥ 1`, hence `H^k(Y) = 0` for contractible `Y`, and `H^0(Y) ≃ₗ F₂` |
| `CohomologySphereComplement.lean` | `S^n ∖ {p}` is contractible (stereographic projection) and its cohomology |
| `CohomologyMayerVietoris.lean` | the cochain-level Mayer–Vietoris short exact sequence, `δ`, exactness, the connecting isomorphism |
| `CohomologyProductCover.lean` | `isZero_mvAmbient`, opens of a product, the empty space |
| `CohomologyKunnethSphere.lean` | the Künneth vanishing step and the cohomology suspension isomorphism |
| `CohomologySphereZero.lean` | the two-point structure of `S⁰` and Künneth with a sphere factor |

## 1. GREEN

Each line is a `ccprobe.sh` run ending in `Build completed successfully (N jobs)`
with a `Built …` line for the module (never `Replayed`).

| module | jobs |
|---|---|
| `CharClass/CohomologyBasic.lean` | 8767 |
| `CharClass/CohomologyBridge.lean` | 8767 |
| `CharClass/CohomologySphere.lean` | 8769 |
| `CharClass/CohomologyAssoc.lean` | 8769, re-green at 2055 after the cast-shape change |
| `CharClass/CohomologyContractible.lean` | 8769 |
| `CharClass/CohomologySphereComplement.lean` | 8768 |
| `CharClass/CohomologyMayerVietoris.lean` | 8768 |
| `CharClass/CohomologyProductCover.lean` | 8769 |

No `sorry`, `admit`, `axiom`, `opaque` or `native_decide` has ever appeared in
any of these files.

## 2. AUTHORED, UNVERIFIED

* `CharClass/CohomologyKunnethSphere.lean` — first probe hit a `maxHeartbeats`
  timeout in one `isDefEq`; restructured with `refine` and re-probing.
* `CharClass/CohomologySphereZero.lean` — first probe in flight.

## 3. NEEDS

* **`cc-steenrod`: `cup_comm`.**  Not built here and deliberately not
  placeholdered.  The consumer is `cc-projective`'s `ChernEvenRingComm.lean`; the
  shape it imports is

  ```lean
  theorem cup_comm {X : TopCat.{0}} {p q : ℕ} (a : Hmod2 X p) (b : Hmod2 X q) :
      cohCast (Nat.add_comm p q) (cup a b) = cup b a
  ```

  Nothing in this lane will need renaming when it lands.

* **Not delivered by this lane, and now owned elsewhere**: the element-level
  Mayer–Vietoris layer with the `H^*(X)`-linearity of the connecting map is
  `cc-thom`'s, built on `CohomologyMayerVietoris.lean`; the even total ring is
  `cc-projective`'s `ChernEvenRing.lean`, built on `CohomologyBasic.lean`.

* **Künneth with spheres in full (isomorphism) form**, `H^k(X × S^n) ≅ H^k(X) ⊕
  H^{k-n}(X)` via `pr₁^*` and `(-) ⌣ pr₂^* σ_n`, natural in `X`, is *not* done:
  only the vanishing form is.  The vanishing form is what `cc-thom`'s recursion
  consumes; the isomorphism form additionally needs the splitting of the
  Mayer–Vietoris sequence by the retraction `X × S^n → X`.

* **Künneth for an arbitrary pair of factors** is out of reach here and should not
  be promised to anyone: it needs Eilenberg–Zilber, a chain equivalence
  `C_*(A × B) ≃ C_*(A) ⊗ C_*(B)`, which neither Mathlib nor the vendored tree
  has.  The universal-coefficient route does **not** avoid it.  What is available
  is one sphere factor at a time (here) and one `CP` factor at a time
  (`cc-projective`).

## 4. TRAPS

* The `⦋n⦌` simplex notation is **scoped in the `Simplicial` locale**.  Without
  `open Simplicial` the parse error is a bare `expected token`, and every
  subsequent tactic in the file is reported as `'…' tactic does nothing` by the
  unused-tactic linter — which, under `-DwarningAsError=true`, buries the real
  error under forty spurious ones, and Lean's error recovery adds
  `declaration uses 'sorry'` on every downstream declaration.  Read the *first*
  error, not the loudest, and never conclude from `declaration uses 'sorry'` that
  the file contains the token.
* `ccprobe.sh` prints only `grep '^error' | head -60` plus `tail -n CC_TAIL`.
  With many errors the first (real) one falls off the end of both; raise
  `CC_TAIL` rather than guessing.
* `CategoryTheory.FunctorToTypes.map_id_apply` and `…map_comp_apply` are
  **deprecated** at this pin in favour of `CategoryTheory.Functor.map_id_apply`
  and `…Functor.map_comp_apply`; a deprecation is an error here.
* `TopCat.of ((U : Set X) ∩ (V : Set X))` fails with `failed to synthesize Inter
  Type`: the argument of `TopCat.of` is elaborated with expected type `Type`, so
  the `↥` coercion is attempted around the whole intersection and `∩` is looked
  up at `Type`.  Write `TopCat.of ↥(… ∩ …)`.
* A `ShortComplex` built as `F.mapShortComplex.obj S` does **not** reduce: its
  `.X₁` will not unfold to what you think, and every downstream `exact` fails a
  defeq check.  Build the short complex as an explicit structure.  Likewise
  `ShortComplex.Splitting.ofIso` through an identity iso is worse than copying the
  five fields directly, because `ShortComplex.isoMk`'s square goals are not closed
  by `simp` (it normalizes one side into `Linear.leftComp`).
* `Functor.mapShortComplex` needs `[F.PreservesZeroMorphisms]`, and instance
  search will not find it for `F.mapHomologicalComplex _` while the shape argument
  is still a metavariable.  Write the shape out: `(ComplexShape.down ℕ).symm`.
* Passing a hand-written `have` to a lemma whose expected type mentions
  `TopCat.of ↥(…)` can blow the 200000-heartbeat `isDefEq` budget.  Use `refine`
  with `?_` so Lean elaborates the goal itself, instead of checking your
  statement against it.
* The vendored `CohomologyCupProduct.lean` **already** carries the
  cohomology-level product `cupZMod2`, the unit `oneZMod2`, `cupZMod2_mk`,
  `cohPullback` and `cohPullback_cupZMod2`.  Do not re-derive the descent; only
  bilinearity, associativity and unitality were missing.
* The vendored **Mayer–Vietoris is homological**.  The cohomology version here is
  its `Hom(-, F₂)`-dual; that dualization is exact because `F₂` is injective over
  itself (the vendored `moduleInjective_ZMod2`), and it is *cheap* because the
  vendored `mvSplitting` gives an explicit **degreewise splitting** — a split
  short exact sequence survives any additive functor.  Without the splitting one
  would have to prove exactness of the dual by hand.
* `H^0(X; F₂)` for a path-connected `X` goes through the *general-coefficient*
  augmentation `H0Gen.H0aug`, in the sub-namespace `H0Gen` of
  `SingularH0General.lean`.  The unqualified `H0aug` in scope is the **integral**
  one from `SingularH0PathConnected.lean` and takes a `TopCat` where you expect a
  ring.
* `p + 0` reduces to `p` but `0 + p` does not, and `p + q + r` is not
  definitionally `p + (q + r)`.  Right unitality is therefore free; left
  unitality and associativity need `cohCast`.
* `Subspace.dual_finrank_eq` plus the vendored `kroneckerEquiv` is the cheap
  route to "this cohomology group is one dimensional": compute the *homology*
  rank and dualize, exactly as `SphereTopCohomologyRankOne.lean` does.

## 5. Overlaps for the lead to arbitrate

* `CohomologySphereComplement.lean` is subsumed by `cc-thom`'s green
  `ThomPuncturedSphere` (theirs is for any real inner product space, mine only for
  the vendored `Sphere n`).  I will delete mine on request.
* `CohomologyMayerVietoris.lean`'s `cohDualFunctor` block duplicates
  `cc-relative`'s `RelativeDual.lean`.  I wrote my own because
  `RelativeCochains.lean` was red and a red module cannot be imported at all.
