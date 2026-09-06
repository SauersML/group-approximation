# cc-thom — Thom class, relative Euler class, punctured product, Mayer–Vietoris

Owns `GroupApproximation/CharClass/Thom*.lean`,
`GroupApproximation/CharClass/EulerLocal*.lean` and, from the lead's reassignment
of 2026-09-05, `GroupApproximation/CharClass/MayerVietoris*.lean`; namespace
`GroupApproximation.CharClass`.

## 0. Mayer–Vietoris: published signatures (build against these)

Cohomological Mayer–Vietoris moved from `cc-cohom-api` to cc-thom.  `cc-cohom-api`
keeps the cup product, casts, bridges, spheres, homotopy invariance and
Künneth-with-spheres.

**Split, per the lead's ruling.**  `cc-cohom-api` owns the categorical dualized
short exact sequence (`CharClass/CohomologyMayerVietoris.lean`, green at 8768
jobs, `1b9601b02`): `dualCx2`, `dualMap2`, `mvCoSC`, `mvCoSC_shortExact`,
`subCxDualHomologyIso`, `mvInterIso`, `mvAmbientIso`, `mvDelta`, `upRel`, the
three `ShortComplex.Exact`s.  cc-thom owns the element-form bridge on top of it.
An earlier cc-thom port of the dualization (`MayerVietorisDual.lean`, namespace
`CharClass.MV`) was written while their file was red and has been **deleted** on
the lead's ruling that their copy went green first.  cc-thom's four `dualMap2`
algebra lemmas are kept locally and prefixed `mvDualMap_` so they cannot collide.

| module | contents |
|---|---|
| `CharClass/MayerVietorisBiproduct.lean` | `mvDualMap_comp/_id/_add/_zero`, the four biproduct identities on the middle term, `mvH_decompose`, `mvH_eq_zero_iff`; the `F₂` sign lemmas |
| `CharClass/MayerVietorisElement.lean` | the four restrictions, `mvDelta`, and `mvExactX` / `mvExactSum` / `mvExactW` |
| `CharClass/MayerVietorisVanishing.lean` | `isZero_cohomology_of_cover`, and `isZero_cohomology_of_cover'` in the `CohomologyToolkit` shape: **need (A1) is discharged** |
| `CharClass/MayerVietorisRestriction.lean` | `subInclusion`, `subInclusion_comp_sInclusion`, `subChainCorestrict_naturality` — the chain-level half of `mvResWU_eq_pull` |
| `CharClass/MayerVietorisPull.lean` | `mvCxInclU_comp_g`, `dualMap2_subChainCorestrict_naturality`, **`mvResWU_eq_pull`**, **`mvResWV_eq_pull`**, **`mvResWU_one`**, `neg_eq_self_chainHom`, `mvCxInclV_comp_g` — the restrictions to the intersection are honest pullbacks, and the unit restricts to the unit |
| `CharClass/MayerVietorisPullAmbient.lean` | `subChainCorestrict_comp_toAll`, `f_comp_mvCxProjU`, **`mvResU_eq_pull`**, **`mvResV_eq_pull`** and their `V` twins — the restrictions from the ambient space are the pullbacks along `sInclusion`, through the small-chain end without inverting the quasi-isomorphism |
| `CharClass/MayerVietorisZero.lean` | `mono_homologyMap_zero`, **`mvExactZero`**, `mvResPair_injective` — the left end of the sequence: the pair of restrictions is injective on `H⁰` |
| `CharClass/MayerVietorisNaturality.lean` | `opensComap_sup_eq_top`, `opensRestrict`, `interRestrict`, **`mvResU_naturality`**, **`mvResV_naturality`**, **`mvResWU_naturality`**, **`mvResWV_naturality`** — the four restriction squares for a map of covered spaces |
| `CharClass/MayerVietorisDisjoint.lean` | `mvResPair_eq_zero_of_disjoint`, `mvResPair_surjective_of_disjoint`, **`mvPairEquiv`** — a cover by two *disjoint* opens splits `H^n`; the `S⁰` base of the top-degree Künneth, with no cross product |
| `CharClass/MayerVietorisSequence.lean` | `mvSequence`, cc-projective's `MVSequence` package |

```lean
namespace GroupApproximation.CharClass
variable {X : TopCat.{0}}

/-- `U ∩ V` as a space. -/
abbrev mvInter (U V : Opens X) : TopCat.{0}          -- TopCat.of (↑U ∩ ↑V : Set X)

def mvResU  (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    Hmod2 X n ⟶ Hmod2 (TopCat.of (U : Set X)) n
def mvResV  (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    Hmod2 X n ⟶ Hmod2 (TopCat.of (V : Set X)) n
def mvResWU (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    Hmod2 (TopCat.of (U : Set X)) n ⟶ Hmod2 (mvInter U V) n
def mvResWV (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    Hmod2 (TopCat.of (V : Set X)) n ⟶ Hmod2 (mvInter U V) n
-- δ is cc-cohom-api's `mvDelta U V hUV n : Hmod2 (mvInter U V) n ⟶ Hmod2 X (n + 1)`

theorem mvExact_X (U V) (hUV) (n : ℕ) (x : Hmod2 X (n + 1)) :
    ((mvResU U V hUV (n + 1)).hom x = 0 ∧ (mvResV U V hUV (n + 1)).hom x = 0)
      ↔ ∃ w, (mvDelta U V hUV n).hom w = x
theorem mvExact_sum (U V) (hUV) (n : ℕ) (a : Hmod2 (TopCat.of (U : Set X)) n)
    (b : Hmod2 (TopCat.of (V : Set X)) n) :
    (mvResWU U V hUV n).hom a = (mvResWV U V hUV n).hom b
      ↔ ∃ x, (mvResU U V hUV n).hom x = a ∧ (mvResV U V hUV n).hom x = b
theorem mvExact_W (U V) (hUV) (n : ℕ) (w : Hmod2 (mvInter U V) n) :
    (mvDelta U V hUV n).hom w = 0
      ↔ ∃ a b, (mvResWU U V hUV n).hom a + (mvResWV U V hUV n).hom b = w

/-- The package `cc-projective`'s `ProjectiveSpaceCohomology` consumes, verbatim. -/
def mvSequence (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    MVSequence X (TopCat.of (U : Set X)) (TopCat.of (V : Set X)) (mvInter U V)

/-- The restrictions are the honest pullbacks along the inclusions. -/
theorem mvResU_eq_pull  … ; mvResV_eq_pull  … ;
theorem mvResWU_eq_pull … ; mvResWV_eq_pull …

/-- `CohomologyToolkit`'s field (A1), a corollary. -/
theorem isZero_cohomology_of_cover (U V : Opens X) (hUV : U ⊔ V = ⊤) (m : ℕ)
    (hI : IsZero (Hmod2 (mvInter U V) m))
    (hU : IsZero (Hmod2 (TopCat.of (U : Set X)) (m + 1)))
    (hV : IsZero (Hmod2 (TopCat.of (V : Set X)) (m + 1))) :
    IsZero (Hmod2 X (m + 1))

/-- Naturality in a map of covered spaces (NOT YET WRITTEN).  For `f : X' ⟶ X` and
    `U' := (Opens.comap f) U`, `V' := (Opens.comap f) V`, the restriction squares and
    the δ-square commute. -/
theorem mvResU_naturality (f : X' ⟶ X) (U V : Opens X) (hUV : U ⊔ V = ⊤) (n) (x) :
    pull (f.restrict …) n ((mvResU U V hUV n).hom x)
      = (mvResU _ _ _ n).hom (pull f n x)
theorem mvDelta_naturality (f : X' ⟶ X) (U V : Opens X) (hUV : U ⊔ V = ⊤) (n) (w) :
    pull f (n + 1) ((mvDelta U V hUV n).hom w)
      = (mvDelta _ _ _ n).hom (pull (f.restrict …) n w)

/-- `H^*(X)`-linearity of the connecting map, for a global class `b`.  This is the
    δ-square of `LerayHirschAlgebra.bijective_of_ladder`, whose squares are
    `∀ a, φ (f a) = g (φ a)` with the verticals `cup · b`; the degree cast is
    `p + q + 1 = p + 1 + q`. -/
theorem mvDelta_cup (U V) (hUV) {p q : ℕ} (a : Hmod2 (mvInter U V) p) (b : Hmod2 X q) :
    (mvDelta U V hUV (p + q)).hom (cup a (pull (inclSubtype _) q b))
      = cohCast (by omega) (cup ((mvDelta U V hUV p).hom a) b)
end GroupApproximation.CharClass
```

**`mvResWU_eq_pull` — DONE, green in `CharClass/MayerVietorisPull.lean` (8773 jobs),
together with `mvResWU_one`.**  Postscript: `cc-projective` then found they did not
need it.  Their degree-zero hypothesis was only ever used as "every class of
`H^0(U ∩ V)` is a sum of restrictions", which follows from `mvExactSum` by counting
on lines with no identification of the maps at all; they weakened
`hasCPCohomology_succ` to that and `H^*(ℂP^n; F₂)` is unconditional at 8789 jobs.
The general statement is still wanted for Leray–Hirsch, so the work stands, but the
lesson is worth recording: **check what a hypothesis is used for before building the
strongest thing that would discharge it.**  `cc-cohom-api` does consume
`mvCxInclU_comp_g` from this file for δ-linearity step 2.  The record of how it
was assembled, kept because the same three steps recur for the other three
restrictions:
`cc-projective` reports that this, in its degree-zero form `mvResWU_one`, is the
*last* hypothesis of the projective-space induction, so it outranks δ-linearity in
what it unblocks.  Its mathematical content is the naturality of
`subChainCorestrict` for subspace inclusions, and that is **green** in
`CharClass/MayerVietorisRestriction.lean`.  What remains is bookkeeping, now
pinned precisely:

* `mvResWU` unfolds to `(subCxDualHomologyIso ↑U n).inv ≫ homologyMap (dualMap2 (subChainInclusion (↑U∩↑V) ↑U _)) n ≫ mvInterIso.hom`,
  because `mvHInclU ≫ homologyMap (mvCoSC).g = homologyMap (dualMap2 (mvInclUV_U))`
  by `mvDualMap_comp` and `biprod.lift_fst`;
* `cohPullback f n` is `(singularCohomologyZMod2 n).map f.op`, which unfolds to
  `homologyMap (dualMap2 (chainCxFun.map f)) n`;
* so the identification is `subChainCorestrict_naturality` dualized by
  `mvDualMap_comp` and pushed through `homologyMap`, then conjugated by
  `subCxDualHomologyIso`, whose `hom` is `dualCxFunctor.map` of the *op* of an
  `asIso` — getting that direction right is the one fiddly step left.

**Still open**, and each comparable in size to the element-level layer:

* **(3) `H^*(X)`-linearity of `δ` — OWNED BY `cc-cohom-api`**, by the lead's
  reassignment and at their request, since
  they need it for `tx_inj` and `ParityData` and it is on cc-projective's critical
  path twice over.  The full analysis went to them, including cc-projective's
  simplification that `b` is always pulled back from the ambient space, so the lift
  can be taken to be `c̃ ⌣ b` with the same `b` throughout.  Better framing than the
  one first recorded here:  This is precisely the δ-square of
  `LerayHirschAlgebra.bijective_of_ladder`, whose verticals are `cup · b`.  Route:
  Mathlib's `ShortComplex.ShortExact.δ_apply`
  (`Mathlib/Algebra/Homology/ConcreteCategory.lean`) describes `δ [c]` as `[d c̃]`
  for any lift `c̃`, and the vendored cochain Leibniz rule
  (`AlgebraicTopology/CochainCupLeibniz.lean`) then moves `d` across the cup.  The
  awkward step is the *ambient* end: `coAmbientIso` inverts the homology map of the
  dual small-chains inclusion, so identifying `δ` with a global cochain needs the
  compatibility of that quasi-isomorphism with `cochainCup`, which holds because it
  is induced by a chain map compatible with Alexander–Whitney, but is not written.
* **(2) Naturality — the four restriction squares are DONE**
  (`CharClass/MayerVietorisNaturality.lean`, green at 8775).  Historical note on why
  they were cheap:  With `mvResU_eq_pull` and `mvResWU_eq_pull`, every Mayer–Vietoris
  restriction is a `cohPullback`, so each restriction square of naturality is
  functoriality of `pull` and needs no chain-level map at all.  Only the **δ-square**
  still needs the missing `subChainComplex R X' (f⁻¹ S) ⟶ subChainComplex R X S`
  with compatibility of the splittings.  **All four restriction identifications are now green**: `mvResU_eq_pull`,
  `mvResV_eq_pull`, `mvResWU_eq_pull`, `mvResWV_eq_pull`.  Only the last needed the
  characteristic-two absorption, via `neg_eq_self_chainHom`, because the minus of the
  chain-level sequence lives in `g` and the two ambient restrictions go through `f`.
  So **every restriction square of naturality is functoriality of `pull`**, and the
  missing subordinate-chain map over different spaces is needed for the δ-square
  alone, which is `cc-cohom-api`'s side of the split.

**Note for `cc-projective`.**  `mvSumIso` turns out not to be needed: the
element-form `MVSequence` above is derived from the four biproduct identities
(`dualMap2 biprod.fst ≫ dualMap2 biprod.inl = 𝟙`, the two vanishing cross terms,
and `biprod.total` carried through the additive `dualCxFunctor`), never from an
identification of `X₂.homology` with a biproduct.  You get the structure itself,
which is strictly what you asked the iso for.

Notation: `H^n X := cohomologyZMod2 X n : ModuleCat.{0} (ZMod 2)` (vendored,
`…/AlgebraicTopology/CohomologyCupProduct.lean`; this is `cc-cohom-api`'s
`Hmod2 X n` reducibly), spaces are `TopCat.{0}`.

---

## 1. GREEN

Probe of **all fourteen modules together**:
**`Build completed successfully (8786 jobs)`**, `ERROR_LINES=0`, `LAKE_EXIT=0`,
`PROBE GREEN` (private clone `cc_clones/cc-thom`, 2026-09-05, fixed `ccprobe.sh`).
Every module below has a `Built …` line, not `Replayed`, for its current bytes.

The four `MayerVietoris*` modules are the lead's reassignment of cohomological
Mayer–Vietoris; the nine `Thom*`/`EulerLocal*` modules are the original lane.

| module | content |
|---|---|
| `CharClass/ThomFieldTwo.lean` | `injective_of_surjective_of_linearEquiv`, `ne_zero_of_surjective_of_linearEquiv`, `surjective_of_exact_of_subsingleton`, `ModuleCat` restatements |
| `CharClass/ThomPuncturedCover.lean` | the two-set open cover of a punctured product and its four homeomorphisms, as sets and as `Opens` |
| `CharClass/ThomPuncturedSphere.lean` | `spherePuncturedHomeo`, `ContractibleSpace ↥({v}ᶜ)` for the unit sphere of any real inner product space |
| `CharClass/ThomFreeModule.lean` | the Leray–Hirsch linear algebra: `thomGenerator`, `surjective_of_basis`, `ker_eq_span_thomGenerator`, `existsUnique_smul_thomGenerator`, `existsUnique_lift`, `existsUnique_smul_of_injective_of_range` |
| `CharClass/EulerLocalChart.lean` | `homeomorphCompl`, `compl_singleton_subtype`, `chartPairHomeo`, `openPartialHomeomorphChartPair` |
| `CharClass/ThomPuncturedRecursion.lean` | `isZero_of_linearEquiv`, `CohomologyToolkit`, `KunnethFactor`, `kunnethFactor_of_prodEquiv`, `PuncturedAcyclic`, the two base-case constructors, `PuncturedAcyclic.prod`, `isZero_punctured_top` |
| `CharClass/EulerLocalNonvanishing.lean` | `ne_zero_of_map_ne_zero`, `rankOneOfIso`, `range_eq_ker_of_exact`, `surjective_of_punctured_acyclic`, `topChernClass_ne_zero` |
| `CharClass/ThomKunnethSphere.lean` | `kunnethFactor_sphere`, `kunnethFactor_of_contractible`, `kunnethFactor_sphere_compl`, `puncturedAcyclic_sphere` — the Künneth input instantiated from `cc-cohom-api`'s green `isZero_cohomology_prod_sphere` |
| `CharClass/EulerLocalAssembly.lean` | `rankOneOfIsoChain`, `su_ne_zero_of_chain`, **`topChernClass_ne_zero_of_chain`** — Step C in a single application, chaining excision, the chart isomorphism and the local model |
| `CharClass/ThomToolkitInstance.lean` | **`cohomologyToolkit`** — the toolkit as a *term*; `puncturedAcyclic_prod` and `puncturedAcyclic_sphere'` with it discharged |
| `CharClass/ThomKunnethProjective.lean` | `prodOpen_inf`, `isZero_prodOpen_of_homotopyEquiv`, **`kunnethFactor_CP`** — `KunnethFactor (CP d) (2*d)` by Mayer–Vietoris induction on `d`; **no δ-linearity involved** |
| `CharClass/ThomClassChain.lean` | **`thomClass`**, `jm_thomClass`, `thomClass_unique`, `existsUnique_smul_thomClass` — the Thom class as a *term* over Leray–Hirsch as a hypothesis; §1.4 item 5's `H^{k+2r}(pair) ≅ H^k(X)` |
| `CharClass/ThomProjectivePunctured.lean` | `isZero_cohomology_CP`, `KunnethFactor.congrHomotopy`, **`puncturedAcyclic_CP`**, **`kunnethFactor_CP_punctured`** — the two projective hypotheses of `cc-lix-odd`'s `puncturedAcyclic_lixBase`, at an arbitrary point via `cc-projective`'s homogeneity |
| `CharClass/ThomEulerNaturality.lean` | `hom_apply_comp`, `topClass_eq_of_naturality`, `topClass_eq_of_naturality'` |
| `CharClass/ThomPuncturedPi.lean` | `piFinSuccHomeo`, `piFinOneHomeo`, `PuncturedAcyclic.congr`, `PuncturedAcyclic.congr'`; the `Fin`-indexed recursion is deliberately absent, see the file's last section |
| `CharClass/ThomTopLine.lean` | **`HasTopLine`**, `prodCoverConnecting`, `hasTopLine_sphere`, `hasTopLine_prod_sphere{,_succ}`, `hasTopLine_prod_CP{,_succ}` — the top-line induction for a left-nested product of spheres and projective spaces; **no cup and no cross product** |
| `CharClass/ThomTopLineCircle.lean` | `sphereZeroProdEquiv`, `ker_mvDelta_circle`, **`circleTopLineStep`** — the one case the connecting isomorphism cannot reach, computed by rank counting over `F₂` |
| `CharClass/ThomTopLineLIX.lean` | `hasTopLine_sphereOne`, `hasTopLine_circleTimesFive`, `hasTopLine_lixBase`, **`absEquiv_lixN`** — hypothesis 8 of Step C at the real `N`, modulo the one model homeomorphism `cc-lix-odd` owes |

Job count: 8786 (fourteen modules, one probe).

## 2. AUTHORED, UNVERIFIED

Nothing outstanding; every cc-thom module is in §1.  What remains is
*instantiation*: `CohomologyToolkit` and the hypotheses of
`topChernClass_ne_zero` are `structure` fields / explicit hypotheses, never
`sorry` and never `axiom`, and §3 says exactly who owes each of them.

## 3. NEEDS

### From `cc-cohom-api`

**ALL FOUR TOOLKIT FIELDS ARE DISCHARGED.**  `CohomologyToolkit` is now the term
`ThomToolkitInstance.cohomologyToolkit`, built from their `pullEquivOfHomeomorph`,
`pullEquivOfHomotopyEquiv` and `cohomology_isZero_of_contractible` together with
cc-thom's own `isZero_cohomology_of_cover'`.  Everything the punctured-product
recursion proves is unconditional in it.  The remaining ask of this lane is the
`CP`-factor Künneth from `cc-projective`, and δ-linearity, which is theirs.

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

**(A2) Künneth, vanishing form — CORRECTED, and now much smaller.**
`cc-cohom-api` established that the route through homology Künneth is **not**
available: it needs Eilenberg–Zilber, and neither the vendored tree nor Mathlib
has it.  cc-thom's recursion has been restructured accordingly and no longer asks
for general Künneth.  The `kunneth` field is gone from `CohomologyToolkit`;
`ThomPuncturedRecursion.KunnethFactor Y` takes its place, one factor at a time,
and `PuncturedAcyclic.prod` consumes two instances of it.  With `N` **left-nested**,
`(((S¹ × S⁵) × CP d₁) × CP d₂) × ⋯`, every second factor is a sphere, a `CP(d)`, a
punctured sphere (contractible, so `kunnethFactor_of_prodEquiv` applies with no
Künneth at all, fed by `cohProdContractible`) or a punctured `CP(d)` (homotopy
equivalent to `CP(d−1)`, so a `CP` again).  **Both cases are now done and nothing is owed here.**  The projective case is
`ThomKunnethProjective.kunnethFactor_CP`, built in cc-thom's own vocabulary by
Mayer–Vietoris induction on `d` over cc-projective's green cover; it needs only the
*vanishing* form of Mayer–Vietoris, so it did **not** wait on δ-linearity.  The
sphere case is: `cc-cohom-api`'s green `isZero_cohomology_prod_sphere`
gives `kunnethFactor_sphere (n) : KunnethFactor (Sphere n) n` in
`CharClass/ThomKunnethSphere.lean`, and punctured spheres need no Künneth at all
since they are contractible.  
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

Status: **(C1)** first half green (`BundleZeroSection.notZeroHomotopyEquivProj`);
second half and **(C2)** pullback naturality requested.  **(C3) and (C4) withdrawn** —
`cc-lix-odd` has a free explicit trivialisation of the fibre at Step C's zero (over the
southern half of the circle), so the trivializing chart is not consumed, and the trivial
bundle over a point needs no named lemma.

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
`Analysis/LIXProjectiveSpaceModel.lean`.  cc-projective is landing this as
`CharClass/ProjectiveSpaceRetract.punctureHomotopyEquiv (d) : ↥(punctured d) ≃ₕ CP d`;
`punctured d = {x | x ≠ basePoint (d+1)}` is definitionally
`({basePoint (d+1)}ᶜ : Set (CP (d+1)))`, which is the shape
`puncturedAcyclic_of_homotopyEquiv` wants.  **Do not** use
`AlgTop/ComplexProjectivePunctureRetract.punctureHomotopyEquiv`: cc-projective
reports the whole `AlgTop/ComplexProjective*` chain red at the pin, because
`AlgTop/ComplexProjectiveBasic.lean` has an unused simp argument
(`Pi.single_apply`), fatal under `-DwarningAsError=true`, and no lane owns it.

**(D5) Homogeneity of `CP d`.**  (D3) deletes the *base point*; Step C's zero is
an arbitrary point, so I need one symmetry:

```lean
theorem exists_homeomorph_mapsTo_basePoint (d : ℕ) (z : CP (d + 1)) :
    ∃ e : CP (d + 1) ≃ₜ CP (d + 1), e z = basePoint (d + 1)
```

(conjugation by a unitary carrying `z` to the base point, in the projection
model).  `ThomPuncturedPi.PuncturedAcyclic.congr'` turns that plus the base-point
case into the statement at every `z` in one application.  The sphere side needs
no analogue: `ThomPuncturedSphere` already punctures at an arbitrary point.
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

### Delegated to `cc-lix-odd` (lead's split of Step E, 2026-09-05)

`puncturedAcyclic_lixBase`, the punctured-product vanishing instantiated for
`sphereOne × baseM dd` at degree `2 * (∑ j, dd j) + 6`.  Chosen because it is the
first hypothesis of `topChernClass_ne_zero_of_chain` and is written entirely in
`cc-lix-odd`'s vocabulary (`baseM`, `baseSnocHomeo`, `baseNilHomeo`, `sphereOne`).
They build it against `puncturedAcyclic_prod`, `PuncturedAcyclic.congr'` and
`cohomologyToolkit`; the three projective hypotheses stay explicit until
`cc-projective` lands `KunnethFactor (CP d) (2*d)`.  cc-thom keeps the assembly.

### From `cc-lix-odd` / the lead

Instantiate `CohomologyToolkit` once (five fields, all listed above), then
`topChernClass_ne_zero` for the concrete `N` and the mapping-torus bundle `W_g`.
The dimension bookkeeping for `N = S¹ × S⁵ × ∏_j CP(d_j)` is
`puncturedAcyclic_pi` (for the `∀ j : Fin l, CP (d j)` factor, matching
`Analysis/LIXBlockProjections`'s `baseY`) followed by two `PuncturedAcyclic.prod`
steps, or one `puncturedAcyclic_pi` over the whole family.

## 3b. Signature check against the endpoint (2026-09-05)

`cs-endpoint`'s `CharClass.LemmaTwoInput` (`CharClass/LemmaTwoGlue.lean`) bundles a
coefficient object `K` with `[Zero K]`, a
`topClass : (↥sphereOne × baseM dd → Matrix (VIdx dd ⊕ VIdx dd) _ ℂ) → K`, and two
conjuncts; the first is cc-thom's Step C.  Checked against
`EulerLocalAssembly.topChernClass_ne_zero_of_chain`:

* **compatible.**  `K` is existential, so take `K := ↥(cohomologyZMod2 (TopCat.of (↥sphereOne × baseM dd)) (lixTopDegree dd))`;
  its module zero is the `0` of the `≠ 0`, matching my `gamma ≠ 0`.
* **degrees agree.**  `stepD_of_parity` reads `γ` at index `(∑ j, dd j) + 3`, which is
  the rank `r`; my `twoR` is `lixTopDegree dd = 2 * (∑ j, dd j) + 6 = 2 r`.  A class
  `γ_r` in degree `2r` is consistent on both sides.
* **one real seam, unclaimed.**  `topClass` is quantified over *all* matrix-valued maps,
  not just projection-valued ones, so its definition must be total (junk value off the
  projection locus).  And my conclusion is about a `gamma` supplied with
  `hgamma : gamma = j.hom su`, so the glue owes
  `topClass (mappingTorus …) = j.hom su` for each `G` — the identification of `topClass`
  with the top Chern class.  Nobody has claimed it; it is the last seam between Step C
  and the endpoint.

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
* **`Functor.map_id` resolves to the monadic `Functor` class**, not
  `CategoryTheory.Functor.map_id`, even with `open CategoryTheory` in scope; the
  rewrite then fails against the pattern `fun x => id <$> x`.  This is what red
  `cc-cohom-api`'s `CohomologyMayerVietoris.lean`.  Write `CategoryTheory.` on
  `map_id`, `map_comp`, `map_add`, and on `op_id`/`op_comp`/`op_add`.
* **Morphism-level `rw [Category.assoc]` fails once a type ascription has
  rewritten an object.**  In `mvPhi`/`mvPsi` the middle term is ascribed from
  `(coSC U V hUV).X₂` to `coCx (mvCx U ⊞ mvCx V)`; the two are definitionally
  equal but not equal at `instances` transparency, so reassociating a composite
  through them fails with an application type mismatch.  Prove the identity
  pointwise instead (`hom_apply_of_comp_eq` plus a `show`), which checks at full
  transparency.
* **`simp` will not evaluate `(1 : ZMod 2) + 1` to `0`** while simplifying a
  scalar action; supply `((1 : ZMod 2) + 1) = 0 := by decide` and `rw` it.
* **`singularChainMap R f n` takes the degree.**  Writing it without `n` in an
  equality of chain-*complex* maps does not fail with an arity error: `autoImplicit`
  binds the whole application and it surfaces as "Function expected at
  `singularChainMap` … this term has type `x✝`", which reads like a missing import.
  Use `chainCxFun.map f` for the complex-level map.  Relatedly,
  `singularChainComplexFunctor` needs its `AlgebraicTopology.` prefix even with the
  vendored namespace open.
* **A probe syncs the shared working tree, so it tests a *stopped* agent's
  uncommitted edits as if they were the owner's.**  The eight errors I saw in
  `CohomologyMayerVietoris` were a stopped Sonnet lane's bytes; the owner's
  committed file was green throughout.  Check `git status` on a peer's file before
  concluding it is red.
* **Writing a new file against cc-thom's names needs two `open`s that cc-thom's own
  files already carry**, so the lane never sees the failure: `IsZero` needs
  `CategoryTheory.Limits` and `cohomologyZMod2` needs the vendored
  `…SphereOddDegree` namespace.  With `autoImplicit` on, each missing `open` reads as
  "Function expected at `IsZero`, but this term has type `?m`".  Reported by
  `cc-lix-odd` after hitting both in consecutive probes.
* **A theorem inside a `variable` block whose *statement* does not mention those
  variables does not get them bound**, even though the proof body uses them; the
  failure is a cluster of "unknown identifier" errors naming hypotheses three lines
  above.  Also `cc-lix-odd`.  Use explicit binders when the statement quantifies
  internally.
* **Duplicate top-level declarations across `CharClass/` modules are an import
  error, not a type error.**  `isZero_of_linearEquiv` existed in both
  `ThomPuncturedRecursion` and `cc-cohom-api`'s `CohomologyProductCover`, and Lean
  refused the import outright.  Mine is renamed `thomIsZero_of_linearEquiv`.  A
  sweep of every top-level name in `CharClass/` found twelve further candidate
  pairs, all between peers; they are listed in the message to the lead, and any
  pair sharing a namespace will break the root the same way.
* **`git add GroupApproximation/CharClass/` sweeps peers' in-flight files onto
  main.**  cc-thom's commits `05a5fd71a`, `574d4aafe`, `10120c0cc`, `6603e2a7d`,
  `690767b1f` and `fb2d5b958` each carried other lanes' uncommitted work in the
  shared tree along with cc-thom's own modules (the same effect `sweep.sh` has,
  and non-destructive since only current worktree bytes are recorded, but not
  what §3.5 of the program note asks for).  Fixed forward by naming the nine
  `Thom*`/`EulerLocal*` files explicitly; nothing was reverted.
* `AlgTop/ComplexProjective*` and `AlgTop/BundleCalculus*` are **authored but
  never verified**.  `AlgTop/PuncturedNormedSphere.lean` and
  `AlgTop/UniversalCoefficients.lean` are worth reading before reproving
  anything about punctured normed spaces or the universal coefficient theorem.

### The top-line induction bottoms out at the circle, not at the zero sphere

Two separate facts, and I reported the first one wrongly before checking.

* `H^n(Sⁿ; F₂) ≃ F₂` is **not** a gap.  The vendored tree proves it through the
  mod-2 universal coefficient isomorphism, and `CharClass/CohomologySphere.lean`
  restates it as `sphereTopEquiv n hn`.  Grep before declaring a gap: I nearly
  built a Mayer–Vietoris computation for something already green.
* What is genuinely not formal is `H^{p+1}(A × S¹; F₂)`, and **every** step of
  both inductions descends to it.  The sphere step at `n = 0` would need
  `H^p(A; F₂) = 0`, which is the line it is producing; the projective step at
  `d = 1` lands on the same place.  It is one named case, not a family.

The cure is not another connecting isomorphism, because the two arcs covering
`S¹` meet in a disconnected set.  It is a rank count: the connecting map out of
`H^p(A × S⁰)` is surjective, its kernel is exactly the image of `pr_A^*`, the
source is two dimensional and the kernel one.  `ThomTopLineCircle.lean`.

### `cc-cohom-api`'s Künneth-injectivity layer is the naturality this lane needed

`CohomologyKunnethHemi/Band/Zero/Step` and `CohomologyDeltaNatural` are landed.
`KnHemi.exists_pull_prSub_hemiU` (every class on a hemispherical piece is pulled
back from the base) and `KnHemi.mvResWU_pull_prSub` (restriction to the band *is*
the projection) are precisely what the circle rank count needs, and
`pull_knPrY_injective` (a slice retracts the projection) is the injectivity.  The
lead's fallback instruction was to duplicate the cover definitions; that turned
out unnecessary, and duplicating them would have missed the naturality, which is
the hard part.

### `rw` on the degree of a `HasTopLine` hypothesis is a motive error

`HasTopLine Z d` carries an instance argument `[TopologicalSpace Z]`, and
rewriting the *numeric* index in a hypothesis re-abstracts the whole application:

```text
Tactic `rewrite` failed: motive is not type correct:
  fun _a => HasTopLine (↑sphereOne × Sphere 5) _a
Error: Application type mismatch: The argument instTopologicalSpaceSubtype …
```

The motive that is printed abstracts only the `ℕ`, so the message is misleading:
what actually fails is the synthesized `TopologicalSpace` instance in the space
argument, not the degree.  The cure is not to rewrite at all.  Numeric indices
like `1 + 5` and `6` are definitionally equal, so state the result in term mode
and let the final defeq check do the arithmetic.  The same `rw` **succeeds** in
the goal (`hasTopLine_lixBase` rewrites `2 * (∑ …) + 6` there without complaint);
it is only `rw … at h` that breaks.

## 5. Probe log

| date | targets | result |
|---|---|---|
| 2026-09-05 | 5 Mathlib-only modules | 3 green, 2 red (localized) |
| 2026-09-05 | 9 modules | 8 green, `ThomPuncturedPi` red on `Unique (Fin (0+1))` |
| 2026-09-05 | 9 modules | **green, 2910 jobs** |
| 2026-09-05 | 9 modules, after adding `rankOneOfIso` / `range_eq_ker_of_exact` | **green, 2911 jobs** |
| 2026-09-05 | 9 modules, after adding `openPartialHomeomorphChartPair` | **green, 2911 jobs** |
| 2026-09-05 | 9 modules, fixed `ccprobe.sh`, after adding `PuncturedAcyclic.congr'` | **green, 2911 jobs, `PROBE GREEN`** |
| 2026-09-05 | `CohomologyMayerVietoris` alone (cc-cohom-api's) | red: 1 error, then 8 errors on the next probe |
| 2026-09-05 | 5 `MayerVietoris*` modules | green after three rounds |
| 2026-09-05 | all 14 cc-thom modules (with the ported dual) | green, 8744 jobs |
| 2026-09-05 | MV bridge retargeted onto cc-cohom-api's green file | green, 8776 jobs |
| 2026-09-05 | all 13 cc-thom modules, per-factor Künneth | green, 8782 jobs |
| 2026-09-05 | all 14, with the sphere Künneth instances | green, 8786 jobs |
| 2026-09-05 | **`MayerVietorisRestriction`** | **green, 8772 jobs, `PROBE GREEN`** |
| 2026-09-05 | **`ThomTopLine`** | **green, 8791 jobs, `PROBE GREEN`, first probe** |
| 2026-09-05 | **`ThomTopLineCircle`** | **green, 8811 jobs, `PROBE GREEN`, first probe** |
| 2026-09-05 | `ThomTopLineLIX` | red: one `rw … at h` motive error, localized |
| 2026-09-05 | **`ThomTopLineLIX`**, term-mode fix | **green, 8859 jobs, `PROBE GREEN`** |
