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
| `CohomologyMayerVietoris.lean` | the canonical `Hom(-, F₂)` dualization, and the cochain-level Mayer–Vietoris short exact sequence with `δ`, exactness and the connecting isomorphism |
| `CohomologyProductCover.lean` | `isZero_mvAmbient`, opens of a product, the empty space |
| `CohomologyKunnethSphere.lean` | the Künneth vanishing step and the cohomology suspension isomorphism |
| `CohomologySphereZero.lean` | the two-point structure of `S⁰` and Künneth with a sphere factor |
| `CohomologyShapes.lean` | `cc-projective`'s `HasPointCohomology` / `HasSphereCohomology` discharged |
| `CohomologyDegreeZero.lean` | `cocycleClass` is injective in degree 0; `one X ≠ 0` |
| `CohomologyKunnethSplit.lean` | the Künneth map for a sphere factor; the slice half of its injectivity |
| `CohomologyKunnethNatural.lean` | naturality of the Künneth map in the base |
| `CohomologyKunnethMap.lean` | the Künneth map named, and the one missing statement isolated as `KunnethSecondInjective` |
| `CohomologyDeltaLift.lean` | the connecting map computed from an arbitrary lift; entry point for δ-linearity |
| `CohomologyClassOf.lean` | the class of a cocycle for an arbitrary `F₂` cochain complex, with surjectivity and naturality |
| `CohomologyDeltaChain.lean` | the two maps of `mvCoSC` identified on the chain level, including the `V` twins and the mod-2 sign lemmas |

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
| `CharClass/CohomologyMayerVietoris.lean` | 8768 |
| `CharClass/CohomologyProductCover.lean` | 8769 |
| `CharClass/CohomologyKunnethSphere.lean` | 8771 |
| `CharClass/CohomologySphereZero.lean` | 8771 |
| `CharClass/CohomologyShapes.lean` | 8773 |
| `CharClass/CohomologyDegreeZero.lean` | 8730 |
| `CharClass/CohomologyKunnethSplit.lean` | 8768 |
| `CharClass/CohomologyKunnethNatural.lean` | 8769 |
| `CharClass/CohomologyKunnethMap.lean` | 8770 |
| `CharClass/CohomologyBasic.lean` re-green with the cast calculus, 8 modules together | 8771 |
| `CharClass/CohomologyDeltaLift.lean` | 8769 |
| `CharClass/CohomologyClassOf.lean` | 8770 |
| `CharClass/CohomologyDeltaChain.lean` | 8776 |

No `sorry`, `admit`, `axiom`, `opaque` or `native_decide` has ever appeared in
any of these files.

## 2. AUTHORED, UNVERIFIED

*(nothing — every module this lane owns is green)*

`CharClass/CohomologySphereComplement.lean` was **deleted** on the lead's ruling:
`grep -rn CohomologySphereComplement GroupApproximation notes` showed no importer,
and `cc-thom`'s `ThomPuncturedSphere` proves the same thing for any real inner
product space rather than only for the vendored `Sphere n`.

## 2b. EXPORTS (frozen; other lanes build against these)

The dualization layer, canonical per the lead's ruling and consumed by cc-thom's
`MayerVietorisBiproduct`/`MayerVietorisElement`, in `CohomologyMayerVietoris.lean`:
`cohDualFunctor` with `cohDualFunctor_preservesLimits`,
`cohDualFunctor_preservesEpimorphisms`, `cohDualFunctor_preservesHomology`;
`dualCxFunctor` with `dualCxFunctor_additive`; `dualCx2`; `dualMap2`;
`dualMap2_quasiIso`; `cochainCxZMod2_eq_dualCx2`; `upRel`.

The Mayer–Vietoris layer, same module: `mvCoSC`, `mvCoSplittingAux`,
`mvCoSplitting`, `mvCoSC_degreewise_shortExact`, `mvCoSC_shortExact`,
`subCxDualIso`, `subCxDualHomologyIso`, `mvInterIso`, `mvAmbientIso`, `mvDelta`,
`mvExact_inter`, `mvExact_sum`, `mvExact_ambient`, `isZero_mvCoX2`,
`mvConnectingIso`.

The cup layer, in `CohomologyBasic.lean` and `CohomologyAssoc.lean`: `Hmod2`,
`cohCast` with its calculus, `cup` (`⌣`), `one`, `pull`, `pullLinear`, `cupBilin`,
`cup_mk`, the bilinearity lemmas, `cup_one` (strict), `one_cup` and `cup_assoc`
(cast on the left, cc-projective's shape), `one_cup'` and `cup_assoc'` (cast on
the right), `cohCast_symm_cohCast`, `cohCast_cohCast_symm`, `pull_id`,
`pull_comp`, `pull_cup`, `pull_one`, `pull_mk`.

Künneth with a sphere factor, in `CohomologyKunnethSplit.lean` and
`CohomologySphereZero.lean`:

```lean
abbrev knPrY (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    TopCat.of (Y × Sphere n) ⟶ TopCat.of Y
abbrev knPrS (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    TopCat.of (Y × Sphere n) ⟶ TopCat.of (Sphere n)
def knSlice (Y) (n) (p : Sphere n) : TopCat.of Y ⟶ TopCat.of (Y × Sphere n)
def knSigma (Y) (n) (hn : 1 ≤ n) : Hmod2 (TopCat.of (Y × Sphere n)) n
theorem pull_knSlice_knPrY / pull_knPrY_injective / pull_knSlice_knSigma
theorem kunneth_fst_eq_zero (Y) (n) (hn : 1 ≤ n) (p : Sphere n) (m : ℕ)
    (u : Hmod2 (TopCat.of Y) (n + m)) (v : Hmod2 (TopCat.of Y) m)
    (h : pull (knPrY Y n) (n + m) u + cup (knSigma Y n hn) (pull (knPrY Y n) m v) = 0) :
    u = 0
def prodSwapEquiv (A B) (k) : Hmod2 (TopCat.of (B × A)) k ≃ₗ[ZMod 2] Hmod2 (TopCat.of (A × B)) k
theorem isZero_cohomology_prod_sphere (A) (p n) (hA) (k) (hk : p + n < k) :
    IsZero (Hmod2 (TopCat.of (A × Sphere n)) k)
```

Degree zero, in `CohomologyDegreeZero.lean`: `cocycleClass_zero_injective`,
`one_ne_zero_cohZero`.

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

The headline results, all green: `cup`/`one`/`pull` with associativity, unitality,
bilinearity and naturality; homotopy invariance as a `LinearEquiv`; `H^*(S^n)`,
`H^*(pt)` and `H^*(contractible)`; the cochain-level Mayer–Vietoris sequence with
its connecting map, exactness and connecting isomorphism; and Künneth with a
sphere factor in vanishing form,

```lean
theorem isZero_cohomology_prod_sphere (A : Type) [TopologicalSpace A] (p n : ℕ)
    (hA : ∀ a, p < a → IsZero (Hmod2 (TopCat.of A) a))
    (k : ℕ) (hk : p + n < k) :
    IsZero (Hmod2 (TopCat.of (A × Sphere n)) k)
```

### The plan for δ-linearity (assigned to this lane, in progress)

1. **DONE, green at 8769 jobs.**  `MVDelta.delta_apply` in `CohomologyDeltaLift.lean` — Mathlib's
   `ShortComplex.ShortExact.δ_apply` specialised to `mvCoSC`: for a cocycle `x₃`,
   **any** lift `x₂` along `g` and **any** descent `x₁` of `d x₂` along `f` give
   `δ [x₃] = [x₁]`.  The freedom of both choices is the point.
1b. **DONE, green at 8770 jobs.**  `CohClass.clsOf` in `CohomologyClassOf.lean` —
   the class of a cocycle for an **arbitrary** `F₂` cochain complex, which is what
   the terms of `mvCoSC` are (duals of subordinate-chain complexes and of the
   small-chain complex, none of them cochain complexes of a space), with
   `clsOf_eq_cocycleClass`, `clsOf_surjective`, `homologyMap_clsOf` and
   `d_map_eq_zero`.
1c. **DONE, green at 8776 jobs.**  `CohomologyDeltaChain.lean` — the two maps of
   `mvCoSC` on the chain level: `MVDelta.mvCxInclV_comp_g` (the `V` twin of
   cc-thom's `mvCxInclU_comp_g`, where the sign in `mvLeftChainMap` disappears by
   `MVDelta.neg_eq_self_hom` and `MVDelta.mvDualMap_neg`), `MVDelta.f_comp_projU`
   and `MVDelta.f_comp_projV`, and `MVDelta.subToAllU`/`subToAllV` with
   `MVDelta.corestrict_comp_subToAllU`/`V`.  So `g` is the sum of the two
   restrictions and `f` is the pair of restrictions from the ambient space.
2. `mvDelta_spec` — the cochain characterisation: given a cocycle `α` on `U ∩ V`,
   cochains `α_U` and `α_V` restricting to it, and a cochain `γ` on `X` restricting
   to `d α_U` on `U` and `d α_V` on `V`, `mvDelta [α] = [γ]`.
3. δ-linearity then costs four lines: use `α_U ⌣ b|_U`, `α_V ⌣ b|_V` and `γ ⌣ b`,
   and the mod-2 Leibniz rule `d (φ ⌣ b) = d φ ⌣ b` for a cocycle `b`.

The subproject this avoids: one never has to define a cup product on the dual of
the small-chain complex, which has no space behind it.  Choose `x₁` to be the
restriction of a global cochain from the start, and `x₁ ⌣ b` is literally the
restriction of `γ ⌣ b`.  What step 2 does need is the identification of `mvCoSC`'s
`f` and `g` with honest restriction maps of cochains — the same chain-level square
`cc-thom` is building for `mvResWU_one`.  It is now **green on their side** and is
to be imported, not rebuilt: `MayerVietorisPull.mvCxInclU_comp_g`,
`MayerVietorisPull.dualMap2_subChainCorestrict_naturality`,
`MayerVietorisRestriction.subChainCorestrict_naturality`, and
`MayerVietorisBiproduct.mvDualMap_comp/_id/_add/_zero`.

* **`δ`-linearity of the Mayer–Vietoris connecting map**, `δ (a ⌣ b|_{U ⊓ V}) =
  δ a ⌣ b` for a globally defined `b`.  This is the ONE thing between the fleet
  and the Künneth **isomorphism** with a sphere factor, hence between the fleet
  and `cc-wu`'s `tx_inj`.  The lead's split gave it to `cc-thom` with the
  element-form Mayer–Vietoris layer; I have asked them and offered to take it.
  It is isolated in this lane as `KunnethSecondInjective Y n`
  (`CohomologyKunnethMap.lean`), so a consumer can take it as an explicit
  hypothesis today and become unconditional later with no restructuring.
  The route is written out in that module's footer: Mathlib's
  `ShortComplex.ShortExact.δ_eq` gives `δ` the "lift along `g`, differentiate,
  descend along `f`" description, the lift exists because `mvCoSC` is degreewise
  split, and mod 2 the Leibniz rule gives `d (x₂ ⌣ b) = d x₂ ⌣ b` for a cocycle
  `b`; the work is transporting cup products across `subCxDualIso`.

* **Künneth with spheres in full (isomorphism) form** is therefore not finished.
  What IS finished: the map (`kunnethMap`), its naturality in the base
  (`kunnethMap_natural`), the split injection `pr_Y^*` with its slice retraction,
  the vanishing of the sphere class on a slice, the first-component injectivity
  (`kunneth_fst_eq_zero`), the reduction of full injectivity to the one missing
  statement (`kunnethInjective_of_second`), and the vanishing form
  (`isZero_cohomology_prod_sphere`).

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
* `p ∈ (U : Set X)` for `U : Opens X` is **not** defeq-visible as the defining
  inequality to `lt_trans`, `abs_of_pos` or dot notation: state the membership as
  an `Iff.rfl` lemma and rewrite with it.  Relatedly, `a ≠ b` unfolds to a
  function type, so `h.lt_or_lt` on a `Ne` resolves to `Function.lt_or_lt` and
  fails; write `Ne.lt_or_lt h`.
* `EuclideanSpace ℝ (Fin (n+1))` elements go through `WithLp.ofLp` at this pin,
  and the index type in `Sphere n` is `Fin (0 + 1)`, not `Fin 1`, so
  `Subsingleton (Fin 1)` does not fire.  Use `fin_cases`.
* `set_option … in` must come **before** the docstring, not between it and the
  declaration; otherwise the parse error is `unexpected token 'set_option'`.
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

## δ-linearity: state as of probe 34/35

**GREEN and pushed (4bf855412):**

| module | jobs | content |
|---|---|---|
| `CohomologyDeltaSpec` | 8777 | `eltSub`/`eltU`/`eltV`/`eltAmb`, `g_eltU`, `g_eltV`, `projU_f_eltAmb`, `projV_f_eltAmb`, `mvX2_ext`, `d_eltSub` |
| `CohomologyDeltaValue` | 8778 | `mvDelta_spec`, `mvDelta_data`, `exists_d_of_clsOf_eq`, `eltAmb_surjective`, `mvSectG`/`mvRetrF`, `mvGmid`/`mvFmid` |

`CohomologyDeltaCup` (`mvDelta_cup`, `mvDelta_cup_inclSubtype`) is authored and
under probe.

### Two traps that cost four probes

1. **`ModuleCat.comp_apply` produces `ConcreteCategory.hom`.** A goal written
   with `φ.hom x` carries `ModuleCat.Hom.hom`; after
   `simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h`, `h`
   carries `ConcreteCategory.hom`. `rw [h]` then fails. Finish with `exact` or
   `congrArg … |>.trans`, never `rw`, on a simp-normalised hypothesis.

2. **`(mvCoSC U V hUV).X₂` is semireducible.** It is definitionally
   `dualCx2 (mvCx U ⊞ mvCx V)`, but instance search (`HAdd`) and `rw`'s
   `kabstract` work at `instances` transparency and do not unfold it. Symptoms:
   `failed to synthesize HAdd ↑((mvCoSC …).X₂.X p) ↑((dualCx2 …).X p) ?m`, and
   `rw` reporting "did not find an occurrence" of a pattern that is visibly
   present. Cure: type every element and every map at the explicit biproduct
   dual — `mvGmid`, `mvFmid` and the restatements `mvGmid_eltU`, `mvGmid_eltV`,
   `projU_mvFmid_eltAmb`, `projV_mvFmid_eltAmb` do exactly that.

Two smaller ones: `TopCat.of ((U : Set X) ∩ (V : Set X))` fails with
`failed to synthesize Inter Type` — write `TopCat.of ↥(…)`. And `rw [← g_eltU]`
leaves `hUV` a metavariable, because `hUV` occurs only on the rewritten side;
pass all arguments explicitly to a backwards rewrite.

### Why `mvDelta_data` needs a correction step

A class of the ambient term `X₁` (the dual of the small-chain complex) is **not**
the restriction of a global cocycle on the nose. `eltAmb` is surjective, but a
preimage of a cocycle need not be a cocycle: its coboundary vanishes only on
small chains. So `mvDelta_data` picks a global cocycle `γ` representing the value
of `mvDelta`, extracts a coboundary `d w` with `eltAmb γ = x₁ + d w`
(`exists_d_of_clsOf_eq`), and replaces the lift `x₂` by `x₂ + f w`. That leaves
`g x₂` unchanged, so `α` is untouched, while `f (eltAmb γ) = d (x₂ + f w)`
holds exactly — which is what the cup computation needs.
