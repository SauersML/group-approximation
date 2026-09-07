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
| `CharClass/ThomChernBasis.lean` | `ThomChern.genPow_dim_eq_neg_sum/_finSum/_basisSum`, `totalMap_comp`, `totalMap_id` — the Chern relation solved for the top power and written in the Leray–Hirsch basis, which is `ThomClassChain`'s `hlast`; pure `PowerBasis` algebra, no topology |
| `CharClass/ThomFreeDegreewise.lean` | `ThomDeg.restrictMap`, `thomLift`, **`ker_restrictMap`**, `kerEquiv`, **`thomEquiv`** — the Thom-class linear algebra in Leray–Hirsch *coordinates*, over a product of different groups rather than a `Module.Basis`; §1.4 item 5 at `k = 0` |
| `CharClass/ThomStepCLocal.lean` | `topChernClass_ne_zero_of_local`, `..._of_local_naturality`, `..._of_local_line`, `..._of_chain_line` — `locEquiv`, `hg` and `hgamma` discharged, leaving `hsu` alone on the odd side; plus the `Nonempty` forms that spare a consumer the use of choice |
| `CharClass/ThomStepCEuler.lean` | `eq_localGenerator_of_ne_zero`, **`hsu_of_ne_zero`**, `ne_zero_of_hsu`, `topChernClass_ne_zero_of_su_ne_zero{,_line}` — `hsu` **is** `su ≠ 0`, because the local model is a line and excision-then-chart is an iso onto it |
| `CharClass/ThomStepCSection.lean` | `thomClass_ne_zero` (free, no topology), **`SectionDetectsThom`**, `su_ne_zero_of_section`, `topChernClass_ne_zero_of_section` — `su ≠ 0` split into the Thom class being nonzero and one named predicate about the *section* |
| `CharClass/ThomBundlePair.lean` | `bundlePairTrivIso` — the bundle pair over a trivialising neighbourhood **is** the product pair, `cc-bundle`'s image equation fed to `cc-relative`'s pair transport; `relPullback_injective_of_retraction` — a retracted map of pairs is injective, which is what makes the trivial-bundle Thom class computable with no Künneth of pairs |
| `CharClass/ThomKunnethNatural.lean` | `knBaseMap`, `knSigma_natural`, `pull_knBaseMap_knPrY`, **`kunneth_decomposition_natural`** — the absolute Künneth decomposition is natural in the base, the one input `cc-bundle`'s hypothesis-free route still needed |
| `CharClass/ThomRelativeCokernel.lean` | `relDelta_surjective_of_injective`, `ker_relDelta_eq_range_absToSub`, **`relQuotEquiv`** — if the restriction is injective in every degree, the relative group **is** the cokernel of the restriction; the homological core of the hypothesis-free route, with no bundle, sphere or product in it |
| `CharClass/ThomSphereSubspace.lean` | `absToSub_injective_of_sphere`, `relQuotEquiv_of_sphere` — when the ambient contracts onto a base and the subspace is that base crossed with a sphere, the restriction is split injective, so the relative group is the cokernel |
| `CharClass/ThomSectionDetect.lean` | `sectionDetectsThom_of_detect`, **`sectionDetectsThom_of_injective`**, **`topChernClass_ne_zero_of_chartInjective`** — the section predicate **is** injectivity of the chart composite; Step C's odd side over that one geometric input |
| `CharClass/ThomBridgeChart.lean` | `chartExcisedImage`, `bridgeChart` — bridge steps one and two, excision to the affine chart and the chart identified with the total space |
| `CharClass/ThomBridgeHyperplane.lean` | `range_projIncl_subset_notZero`, `bridgeHyperplane`, `incl_comp_eq_invFun`, `hyperplane_hsub` — bridge step three, with its named input discharged |
| `CharClass/LIXLerayHirschInstance.lean` | `lixLerayHirschGraded` — `cc-projective`'s compact-base instance at the projectivised mapping-torus bundle, index `lixRank dd + 1` |
| `CharClass/ThomChernDegreewise.lean` | `cohCast_sum`, `cup_pull_lhTerm{,'}`, `chernCoeff`, `sum_lhTerm_chernCoeff`, `chernMul`, **`lhTerm_top_eq_sum`** — the Chern relation degreewise; no `TotalH` transport is needed, `gammaCoeff` already is the relation |
| `CharClass/ThomRestrictSquare.lean` | **`absToSub_sum_lhTerm`** — the restriction of the pair at degree `2r` **is** `ThomDeg.restrictMap` in coordinates; produces the `g` that `ThomFreeDegreewise` assumes |
| `CharClass/ThomHabs.lean` | `range_relToAbs_eq_ker_absToSub`, `range_comp_eq_ker_of_square`, **`range_thomJm_eq_ker_restrictMap`** — **`habs`** discharged |
| `CharClass/ThomDataFromLH.lean` | `relToAbs_injective_of_graded` (**`hinj0`**), **`thomData_of_lerayHirsch`** — the whole degreewise Thom datum from the two Leray–Hirsch instances plus `1 ≤ r` |
| `CharClass/ThomBridgeTotal.lean` | **`bridgeTotal`**, `thomData_transport`, **`thomData_total_of_lerayHirsch`** — the three bridge steps as one linear equivalence, and the Thom datum moved onto the vector-bundle pair |
| `CharClass/LerayHirschGradedIso.lean` | **`LH.lerayHirschGraded_of_iso`** — `cc-projective`'s `bijective_lhSum_of_iso` wrapped by `LerayHirschBridge`'s transfer, at the published `LerayHirschGraded` interface |
| `CharClass/ThomHyperplaneLH.lean` | `hyperIso`, `hyperProj`, `hyperIso_hom_comp`, **`hyperLH`**, **`thomData_total_of_taut`** — Leray–Hirsch on the hyperplane presented as a subset; the Thom datum over the single input `htaut` |
| `CharClass/LIXThomClassOfTaut.lean` | `cohCast_ne_zero`, `lixTopCoeff{,_ne_zero}`, **`exists_lixThomClass_ne_zero`** — the `u` and the `hu` of `lix_topClass_ne_zero_of_named`, over `htaut` |
| `CharClass/ThomStepCOddLocal.lean` | `injective_comp_of_square`, **`topChernClass_ne_zero_odd_local`**, `topChernClass_ne_zero_odd_local_of_iso` — Step C's odd side over an **injective** local restriction plus one square, strictly weaker than the isomorphism form, which it recovers |
| `CharClass/ThomChainHne.lean` | `injective_of_comp_injective`, **`ne_zero_of_injective_comp`**, `ne_zero_of_local` — `ThomChainThom.hne` (`sRel.hom u ≠ 0`) from the same `hinj` the odd side already needs; closes `cc-projective`'s seam finding C5 with no new obligation |
| `CharClass/LIXThomClassTerm.lean` | `range_comp_linearEquiv`, `injective_thomJm`, `hyperLH_range`, `thomJmTotal{,_apply}`, `injective_thomJmTotal`, `range_thomJmTotal`, `one_le_lixRank_dd`, `lixLHplus`, `lixLHhyper`, **`lixThomClassTerm`**, **`lixThomClassTerm_ne_zero`** — the Thom class as an **unconditional term**, `htaut` discharged by `cc-projective`'s `pull_sInclusion_tautEulerOf` |
| `CharClass/LIXBaseConnected.lean` | `pathConnectedSpace_sphereOne`, `pathConnectedSpace_unitVectorsThree`, **`pathConnectedSpace_lixN`**, `nonempty_lixN`, **`lixCohZeroEquiv`** — the base is path-connected and its `H^0` is a line, which is the whole content of `hres` once the two Thom isomorphisms are in place |
| `CharClass/LIXThomResReduction.lean` | `cohCastEquiv`, `injective_of_line`, **`lixRelLine`**, **`injective_lixRes_of_ne_zero`**, `ne_zero_of_injective_lixRes` — `hres` **is** one nonvanishing statement, because the source of `lixRes` is a line |
| `CharClass/LerayHirschGammaIso.lean` | `LH.lhMap_eq_sum_lhDomain`, `LH.lhMap_of_iso`, **`LH.gammaCoeff_of_iso`**, **`LH.gamma_of_iso`** — the mod-2 Chern classes survive a transport of the total space; the half of `hclass` that mentions no free binder |
| `CharClass/LerayHirschContractible.lean` | `LH.lhTerm_eq_zero_of_contractible`, **`LH.sum_lhTerm_eq_top_of_contractible`** — over a contractible base only the top column survives at degree `2r`; needs no Leray–Hirsch instance over the neighbourhood |
| `CharClass/ThomFibreRestriction.lean` | `Bundle.totalInclOnComp{,_apply,_mem_puncturedSet_iff}`, **`relPullback_totalInclOn_comp`** — restricting a bundle pair twice needs no `restrictTo` transitivity; the direct restriction never appears, so no subtype is identified |
| `CharClass/LIXChernTopGamma.lean` | **`lixChern_top_eq_gamma`** — the endgame's `gamma` is `lixLHhyper`'s top Chern class; the half of `hclass` that mentions no free binder, finished |
| `CharClass/ThomBridgeNatural.lean` | **`chartOpensHomeoTotal_natural`**, `bridgeChartIncl{,_apply}`, **`bridgeChartIncl_natural`** — the naturality layer's space-level content; `bridgeChart` is one `relPullback` along the chart inclusion, so its naturality is one square, not two |
| `CharClass/ThomBridgeNaturalHyper.lean` | **`relPullback_id_comm`** — shrinking a subspace commutes with pulling back; the hyperplane step's square, no geometry |
| `CharClass/ThomBridgeNaturalSquare.lean` | **`relPullback_comm_of_map_eq`** — a commuting square of SPACES gives one of relative pullbacks; the tool the whole naturality layer runs on |
| `CharClass/ThomBridgeChartHom.lean` | `bridgeChartIncl_map_eq`, **`bridgeChart_hom_eq`** (the first two bridge steps are ONE `relPullback`, along the chart inclusion), **`bridgeChart_natural`** (their square, one application of the general tool) |
| `CharClass/ThomBridgeTotalNatural.lean` | `inv_natural_of_hom_natural`, `bridgeTotal_apply`, **`bridgeTotal_natural`** — the bridge is natural in the base; docstring records that `bridgeTotal` needs a COMPACT Hausdorff base, so it does not exist over a ball, which is why the route restricts to a point |
| `CharClass/ThomCoordinates.lean` | **`ThomDeg.jm_thomEquiv_symm`**, **`thomJmTotal_lixThomClassTerm`** — the Thom class's coordinates: top is the unit, the rest are the Chern coefficients acting on it |

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

### The two sphere models are not definitionally equal; only the index is

I nearly committed a docstring saying the model homeomorphism
`↥(unitVectors (Fin 3)) ≃ₜ S⁵` had never been a real obligation.  `cc-lix-odd`
stopped it, and they were right.  Two different things:

* **Free.**  `Sphere 5` against the `EuclideanSpace ℝ (Fin 6)` form.  `Sphere` is
  a reducible abbreviation and `5 + 1` and `6` are the same literal, so
  `unitVectorsThreeHomeoSphere` is `unitVectorsThreeHomeo` with no transport.
* **Not free.**  The models.  `STW59.unitVectors n` is
  `{x : n → ℂ | ∑ᵢ ‖xᵢ‖² = 1}`, a subset of the plain function type;
  `EuclideanSpace ℝ (Fin 6)` is `WithLp 2 (Fin 6 → ℝ)`, and at the pin `WithLp`
  is `structure WithLp (p) (V) where toLp :: ofLp : V`, a one-field wrapper.
  Three complex coordinates in a bare Pi type against six real ones behind a
  structure.  `LIXStepESphereModel.lean` is 153 lines paying the norm identity,
  the round trips and continuity across that seam.

The wording that matters is **discharged by name**, never *never owed*: a reader
told the models are defeq will try `rfl`, which fails as an unrelated instance or
elaboration error rather than as a type mismatch.

### The `Nonempty` variant is hygiene, not foundations

I told three parties that taking the top line as a `Nonempty` "removes the use of
choice".  `cc-lix-odd` ran `#print axioms` and both Step C theorems still report
`[propext, Classical.choice, Quot.sound]`, because the mod-2 cohomology
development and the Mathlib beneath it use choice throughout.  No arrangement of
this interface changes that.

The true claim is narrower: the *consumer* no longer performs a `Nonempty.some`
of its own, which is the consumer's responsibility in a way that Mathlib's use is
not.  Four permanent `#print axioms` lines now sit in `ThomStepCLocal.lean` and
`ThomStepCEuler.lean` so the build states the answer rather than a docstring.
Syntax gotcha from `cc-lix-odd`: a `/-- -/` docstring cannot precede
`#print axioms`; the error says "expected 'lemma'".  Use `/-! -/`.

### Four wrong absence claims in one session

Four times today I wrote that something was not in the tree when the true
statement was that my grep did not match: the sphere base (`sphereTopEquiv`), the
total cohomology ring (`TotalH`), the surjective half of Künneth
(`CohomologyKunnethDecomp`), and the chart trivialisation wired to the relative
pair (`BundlePairs`, `BundleLocal`, `Bundle.totalTrivStd`).  Three were caught by
a peer, one by my own second look.  Every one cost a message or a retraction.

The rule already in this repo's memory is "grep before declaring a gap".  What
that rule does not say, and what cost the time, is that **a failed grep is
evidence about the search, not about the tree.**  So: search by concept and not
by a guessed name, check the recent commit log of the lane that would own it, ask
the owner — and when claiming absence, show the search that was run, so the claim
is falsifiable by the reader rather than taken on trust.

### A claim true in the case at hand, written as though general

`cc-lix-odd`'s observation, recorded with attribution.  `eq_localGenerator_of_ne_zero`
rests on `∀ c : ZMod 2, c ≠ 0 → c = 1` by `decide`.  So "the equality half of
`hsu` is free" is true **because the coefficients are mod 2**.  Over any other
field a nonzero class is only some multiple of the generator, the multiple
survives into the statement, and the equality carries content the nonvanishing
does not.

This is the same failure as the four absence claims, at a different scale: a
statement true in the case at hand, phrased so that it reads as holding
generally.  A second instance of mine the same day: I wrote "only `hsu` remains
open", which was true of one theorem and false as a claim about Step C, and
`cc-lix-odd` caught the undercount.  The naturality square does not remove the
content of `hgamma`; it trades it for `hu`, which mentions a Thom class that is
not green.

What worked, all three times: put the narrow claim in the **source**, where the
next reader hits it, not in a report that has to be remembered.

### The ball route hides local contractibility of the base

`cc-bundle` caught this and I verified it.  Computing the Thom class of a trivial
bundle over a "small enough" trivialising neighbourhood needs that neighbourhood
to be contractible, or at least path-connected.  That is a property of the
**base**, not of the bundle, and it is false in general: `trivSet p x₀` is open
and contains `x₀` and nothing more follows, while in a Cantor set every nonempty
open subset is totally disconnected with more than one point, hence not
path-connected, hence not contractible.  Solenoids are worse.

For the LIX base it happens to hold — a product of spheres and projective spaces
is a closed manifold, so locally contractible — which is exactly why it would
have gone unnoticed until someone instantiated at a general `Bundle X ι`.

The hypothesis-free route: replace the punctured fibre by the sphere bundle,
run the LES of the pair against the **absolute** sphere Künneth, and read two
consecutive degrees.  The restriction is injective in every degree, so the map
out of the relative group vanishes, the connecting map is onto with kernel that
image, and the relative group is the cokernel.  It also gives the fibre-generator
statement at **every** point rather than at one chosen point.

### Reporting failures, which were the day's worst

Two after midnight, both worse than the mathematical ones because neither has a
natural check.

* **A fabricated identifier.**  I wrote a commit hash into a message while saying
  in the same sentence that I had not yet verified it.  A wrong hash does not
  break a build; it sends whoever trusts it to the wrong commit.  **Rule, now
  fleet-wide: an identifier goes into a message only after being read out of
  command output.**  If it has not been read, write "hash to follow".
* **A green probe left unread for an hour.**  I set a long blocking wait, the
  notification arrived, and I did not look.  Nothing needed fixing — only
  reading — and the lead was blocked the whole time.  Do not set long blocking
  waits; read the probe log directly when it returns, and send the one-liner at
  a red rather than waiting for the retry.

`cc-lix-odd`'s framing that the build is the signal and the text is not has a
second half: the signal is worth nothing if nobody looks at it.

### The ambient of a pair must be a `TopCat`, not a type

`absToSub` takes the ambient implicitly, and Lean cannot recover it from a
`Set` of a plain type with a topology.  The symptom is an application type
mismatch naming the *set*, followed by an unrelated `isDefEq` timeout further
down the file — so the second error points nowhere near the cause.  State the
ambient as `{Z : TopCat.{0}}` and take `A : Set Z`.  Same inference failure
`cc-cohom-api` flagged for `mvResU`/`mvPairEquiv` earlier in the day.

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
| 2026-09-05 | `ThomChernBasis` | red twice: `eq_neg_of_add_eq_zero_left` orients `a + b = 0 → a = -b`, and `simp only` applied the second index rewrite first |
| 2026-09-05 | **`ThomChernBasis`** | **green, 2467 jobs, `PROBE GREEN`** |
| 2026-09-05 | `ThomFreeDegreewise` | red: `abel` not imported, two `Fin.snoc` lemmas needing a `show`, one unused binder |
| 2026-09-05 | **`ThomFreeDegreewise`** | **green, 1170 jobs, `PROBE GREEN`** |
| 2026-09-05 | `ThomStepCLocal` | red: missing `open …SphereOddDegree`, so `cohomologyZMod2` was unresolved and autoImplicit reported it as fourteen `Function expected at` |
| 2026-09-05 | **`ThomStepCLocal` + `ThomTopLineLIX`** | **green, 8871 jobs, `PROBE GREEN`** |
| 2026-09-05 | **`ThomStepCEuler`** | **green, 8795 jobs, `PROBE GREEN`** |
| 2026-09-05 | **`ThomStepCEuler` + `ThomStepCLocal`**, axiom prints | **green, 8795 jobs, `PROBE GREEN`** |
| 2026-09-05 | **`ThomStepCSection`** | **green, 8798 jobs, `PROBE GREEN`, first probe** |
| 2026-09-05 | **`ThomBundlePair`** | **green, 8746 jobs, `PROBE GREEN`, first probe** |
| 2026-09-05 | **`ThomBundlePair` + `ThomStepCEuler` + `ThomStepCLocal`** | **green, 8806 jobs, `PROBE GREEN`** |
| 2026-09-05 | **`ThomKunnethNatural`** | **green, 8803 jobs, `PROBE GREEN`, first probe** |
| 2026-09-05 | **`ThomRelativeCokernel`** | **green, 8730 jobs, `PROBE GREEN`, first probe** |
| 2026-09-06 | `ThomSphereSubspace` | red: ambient stated as a type, not a `TopCat` |
| 2026-09-06 | **`ThomSphereSubspace`** | **green, 8807 jobs, `bf27d703`** |
| 2026-09-06 | **`ThomSectionDetect`** | **green, 8830 jobs, `1b542ffc`, first probe** |
| 2026-09-06 | `LIXLerayHirschInstance` | red: I redeclared `rank_lixBundle_plusOne`, already landed in `LIXBundleModel`; and `projMapOf`/`tautEulerOf`/`lerayHirschGraded_compact` are in `LH`, not `Bundle` |
| 2026-09-06 | **`LIXLerayHirschInstance`** | **green, 8999 jobs, `685ddf9a4`** |
| 2026-09-06 | **`ThomChernDegreewise`** | **green, 8925 jobs, `676d54018`** |
| 2026-09-06 | **`ThomRestrictSquare`** | **green, 8931 jobs, `4ad0c528e`** |
| 2026-09-06 | **`ThomHabs`** | **green, 8997 jobs, `a546099e0`** |
| 2026-09-06 | **`ThomDataFromLH`** | **green, 8998 jobs, `cb38b0268`, first probe** |
| 2026-09-06 | **`ThomBridgeTotal`** | **green, 9038 jobs, `28ad165df`** |
| 2026-09-06 | **`LerayHirschGradedIso`** | **green, 2458 jobs, `8d5c0f110`** |
| 2026-09-06 | **`ThomHyperplaneLH`** | **green, 9040 jobs, `4088f7d7b`** |
| 2026-09-06 | **`LIXThomClassOfTaut`** | **green, 9042 jobs, `7760be635`** |
| 2026-09-06 | **`ThomStepCOddLocal`** | **green, 8833 jobs, `e6d7eb609`, first probe** |
| 2026-09-06 | **`ThomChainHne`** | **green, 8834 jobs, `fdfd2dae3`, first probe** |
| 2026-09-06 | `LIXThomClassTerm` | red x3: `isDefEq`/`whnf` timeouts from unpinned `TopCat` implicits and restated types; then `g` elaborated to a metavariable because `M` comes later |
| 2026-09-06 | **`LIXThomClassTerm`** | **green, 9183 jobs, `ee784cb87`** |
| 2026-09-06 | **`LIXBaseConnected`** | **green, 8887 jobs, `73bc9b919`, first probe** |
| 2026-09-06 | `LIXThomResReduction` | red: `omega` cannot see through `↑(Fin.last r)`; needs `rw [Fin.val_last]` first |
| 2026-09-06 | **`LIXThomResReduction`** | **green, 9206 jobs, `71b55c4d3`** |
| 2026-09-06 | `LerayHirschGammaIso` | red: `LHCast.pull_lhTerm` unknown, `CohomologyLHRestrict` not in the import chain |
| 2026-09-06 | **`LerayHirschGammaIso`** | **green, 8929 jobs, `1da909618`** |
| 2026-09-06 | `LerayHirschContractible` | red x2: `omega` blind to `↑(i.castSucc)`; then `Fin.coe_castSucc` deprecated, and a deprecation is an error under the probe's flags |
| 2026-09-06 | **`LerayHirschContractible`** | **green, 8925 jobs, `ecd83acb3`** |
| 2026-09-06 | **`ThomFibreRestriction`** | **green, 8742 jobs, `6b64c1b88`, first probe** |
| 2026-09-06 | **`LIXChernTopGamma`** | **green, 9189 jobs, `8c65148ed`, first probe** |
| 2026-09-06 | `ThomBridgeNatural` | red: stray `open CategoryTheory` with no import, and an unused `DecidableEq` section variable |
| 2026-09-06 | **`ThomBridgeNatural`** | **green, 2981 jobs, `0f3b21b72`** |
| 2026-09-06 | **`ThomBridgeNatural`** (chart inclusion) | **green, 2981 jobs, `696c51b97`** |
| 2026-09-06 | **`ThomBridgeNaturalHyper`** | **green, 8748 jobs, `298a03787`, first probe** |
| 2026-09-06 | **`ThomBridgeNaturalSquare`** | **green, 8749 jobs, `bb8836643`, first probe** |
| 2026-09-06 | `ThomBridgeChartHom` | red x3: missing import for `cmap` and `open` for `sInclusion`; unused `DecidableEq`; `omit` placed AFTER the docstring (a trap already in my own notes) |
| 2026-09-06 | **`ThomBridgeChartHom`** | **green, 8760 jobs, `02c9e0494`** |
| 2026-09-06 | **`ThomBridgeChartHom`** (square) | **green, 8760 jobs, `c79141c57`, first probe** |
| 2026-09-06 | **`ThomBridgeTotalNatural`** (inversion) | **green, 9045 jobs, `1b84115ad`, first probe** |
| 2026-09-06 | `ThomBridgeTotalNatural` (composite) | red x3: `bridgeTotal` needs `open ThomChernDeg`; `congrArg (fun g : _ ⟶ _ => g.hom …)` cannot project; `rw` left a proof-irrelevant `X = X` |
| 2026-09-06 | **`ThomBridgeTotalNatural`** (composite) | **green, 9045 jobs, `66bc6eeb6`** |
| 2026-09-06 | **`ThomCoordinates`** | **green, 9184 jobs, `fd3da3cc1` then `e3cd62615`** |

## 2026-09-07 — lane `lix-hres`: `hres` closed, by the fibre and not by the ball

`hres` is the injectivity of `cc-lix-odd`'s `lixRes`, one of the three residues of
`lix_topClass_ne_zero_of_three`.  `LIXThomResReduction` had already reduced it to
one nonvanishing, because the source of `lixRes` is a line:

```text
(lixRes hGc hGu (2 * lixRank dd)).hom (lixThomClassTerm hGc hGu) ≠ 0.
```

That nonvanishing is now `LIXResFibre.lixRes_lixThomClassTerm_ne_zero`, and `hres`
itself is `LIXResFibre.injective_lixRes`, over `hGc` and `hGu` and **nothing
else** — no `hdd`, no `hGe`, no property of the particular `G`, and no positivity
of the index family.

### The finding: "the whole of its content" was wrong, and the signatures say so

`LIXBaseConnected`'s docstring said injectivity becomes, "under the Thom
isomorphism on each side", the restriction of `H^0` from the base to the ball, so
that connectedness of `N` is "the whole of `hres`'s content"; `lix-wire`'s
model-test cited that as its strongest evidence and graded `hres` "bookkeeping,
not open mathematics".  **There is no Thom isomorphism over the ball.**  The Thom
isomorphism here is `thomJmTotal`, which is built from `bridgeTotal`, and both
carry `[CompactSpace X] [T2Space X]` — `ThomBridgeTotal.lean:74` and
`LIXThomClassTerm.lean:89`.  A ball is not compact, so the ball side of that
sentence does not exist in Lean at all.

Connectedness is a genuine prerequisite — it is what makes the source of `lixRes`
rank one, through `lixRelLine` — but it does not give the nonvanishing.  The lead
corrected the docstring on main at `e341f09e3`.

The honest statement was already in the tree, in `LerayHirschContractible`'s own
postscript: over a contractible neighbourhood only the top column survives, but
applying that to a *restricted class* needs a Leray–Hirsch presentation over the
neighbourhood, and a ball has none.  That postscript is what turned the route.

This is the repository's recorded failure mode "correct declaration, wrong
justification": three separate sources — a docstring, a peer's audit and the
lane brief — agreed that the obligation was bookkeeping, and no gate could see
otherwise, because every declaration involved is true.

### The route

The class is followed one step further, to the **fibre over `lixZero dd`**.
`{lixZero dd}` is a singleton subset of the base, hence compact
(`isCompact_singleton`), Hausdorff (the subtype instance) and nonempty by hand;
over a one-point base `lerayHirschGraded_compact` applies with nothing added and
the coordinates are computable.

The point lies in the ball, so restricting to the point **factors through**
restricting to the ball.  The direction is used one way only and is easy to state
backwards: a class killed by `lixRes` is killed over the point, therefore
**surviving over the point suffices**.  It is *not* claimed that the two
restrictions have the same kernel, that the point restriction is injective, or
that it detects every class.

Over the point the top Leray–Hirsch coordinate of the Thom class is
`lixTopCoeff dd`, the unit of `H^0` of the base, and the unit restricts to the
unit, which is nonzero because a point is nonempty.  Only linearity of
`thomJmTotal` is used — its injectivity over the point is never needed, so
`pull_sInclusion_tautEulerOf` does not have to be re-established there.

### Stage 0 (the empty index family) is not a special case

`lixDD j : Fin j → ℕ`, so at `j = 0` the family is empty, the base is `S¹ × S⁵`,
and `lixRank (lixDD 0) = 3`.  `LIX.lixDD_pos` and any `hdd` binder are vacuous
there.  Checked rather than assumed: this lane's proof uses **no** positivity, no
CP computation, peels no projective factor, and inducts over nothing, so ℓ = 0 is
uniform with the rest.  `lixRank dd = (∑ j, dd j) + 3` is `3` there, which is all
that the two landed general-`dd` facts `one_le_lixRank_dd` and
`two_le_two_mul_lixRank` need; and `LIXBaseConnected.pathConnectedSpace_lixN` is a
single `inferInstanceAs`, so the `Pi` instance over `Fin 0` applies unchanged.

### The modules

| module | content |
|---|---|
| `CharClass/ThomChartSquare.lean` | `totalInclOn_mapsTo`, `bridgeChartIncl_mapsTo`, **`chartSquare`** (the six map-of-pairs conditions of `bridgeChart_natural`, discharged at the bundle's own objects), **`bridgeTotalRestrict`** (the Thom bridge is natural in the base, with nothing left to supply) |
| `CharClass/ThomJmNatural.lean` | **`LH.pull_lhTerm_base`** (a Leray–Hirsch column term under a BASE CHANGE, one `pull_comp` on top of `LHCast.pull_lhTerm`), `projInclOn_eq_projComap`, `projInclOn_proj_square`, `pull_projInclOn_tautEulerOf`, **`thomJm_natural`**, **`thomJmTotal_restrict`** |
| `CharClass/LIXResFibre.lean` | `Bundle.totalInclSub{,_mem,_mem_puncturedSet_iff}`, `totalInclOn_comp_totalInclSub`, `totalInclSub_mapsTo`, `cmap_totalInclSub_comp`, **`relPullback_totalInclOn_sub`**, `pull_lixTopCoeff_ne_zero`, **`lixRes_lixThomClassTerm_ne_zero`**, **`injective_lixRes`** |

`ThomHyperSquare.hyperSquare` was already landed and is the *second* of
`bridgeTotal_natural`'s two squares; the first, the chart square, was the missing
half and had never been written because it had no consumer.
`thomJmTotal_restrict` is exactly what `ThomBridgeTotal`'s docstring predicted:
"a consumer who needs to push a class across this isomorphism and then compare it
with something on the other side will find no lemma to do it with, and will have
to build the naturality layer first."  That prediction was right, and the
naturality layer is now built.

The useful surprise is that cc-projective's two inputs, `projComap_square` and
`LH.tautEulerOf_comap`, are **already general base change** rather than
restriction: `projInclOn p U` *is* `projComap ⟨Subtype.val, _⟩ p` on the nose, by
`rfl`.  So no new geometry was needed for either the projection square or the
tautological class.

### What none of it does

* Nothing here excises anything.  The refutation stands: the excised set would be
  the part of the total space over the complement of the ball, its closure
  contains zero-section points, and those are exactly what the punctured set
  omits.
* Nothing is computed over the ball, and no Thom isomorphism over the ball is
  used or claimed.
* `thomJmTotal_restrict` computes coordinates only; that a restricted class is
  nonzero is the consumer's business.
* Nothing here bears on `hsq` or `hclass`.

### Traps

* **The session scratchpad is shared by every lane**, not per-lane.  A peer
  writing a generic log filename (`probe2.log`) overwrote mine mid-run, and I
  watched its contents change from my own `== lake build` header to another
  lane's.  This is a *different* failure from the shared remote `.cc-last.log`
  and strictly worse: the existing rule — check that the build line names your
  targets — catches the remote case, but a clobbered local log is entirely
  self-consistent, header included, so the rule gives false comfort exactly where
  the danger is highest.  A lane can read a peer's `PROBE GREEN` and land red
  code.  Use a per-lane subdirectory.
* **Killing a probe locally does not kill it remotely.**  The `flock`/`lake` pair
  keeps running and keeps the clone's lock, so a lane that relaunches after a
  local kill ends up queued behind itself.  I had four runs stacked on one clone
  before the lead spotted it from the node.  Kill the remote PIDs, and probe the
  full target list once rather than launching a narrow probe and then a wider one.
* `omit` precedes the docstring; `totalInclOn_mapsTo` needs no `DecidableEq` but
  `bridgeChartIncl_mapsTo` does, through `chartOpensHomeoTotal`.
* Unused section variables: `pull_lixTopCoeff_ne_zero` is fenced inside its own
  `section` so that the `{X} [TopologicalSpace X] {ι} [Fintype ι]` line of the
  bundle-plumbing section cannot follow it and leave unresolvable binders.

### Probe rows

| date | targets | result |
|---|---|---|
| 2026-09-07 | `ThomChartSquare` + `ThomJmNatural` | **contaminated** — local log clobbered by a peer, remote `.cc-last.log` shared; result discarded |
| 2026-09-07 | same, three targets | never ran: queued behind three of my own stale remote builds on `.cc.lock` |
| 2026-09-07 | three targets | red: `ThomJmNatural` — `(i : ℕ)` ascription solved the binder as `ℕ`; cascade at the `simpa` |
| 2026-09-07 | three targets | red: `Unknown identifier ThomChernDeg.thomJmTotal` ×3 — `LIXThomClassTerm` not imported |
| 2026-09-07 | three targets | red: `rw` motive ill-typed at `instances` transparency, `(p.restrictTo U).plusOne` vs `(p.plusOne).restrictTo U` |
| 2026-09-07 | three targets | red: `linter.unusedTactic` on the unexecuted branch of a `first`; `sorryAx: none` |
| 2026-09-07 | **three targets** | **green, 9217 jobs, `sorryAx: none`, 39 axiom lines, `59796080e`** |

Axiom lines checked by name at the green, all exactly
`[propext, Classical.choice, Quot.sound]`: `bridgeTotalRestrict`,
`thomJmTotal_restrict`, `injective_lixRes`.

## 2026-09-07 — lane `lix-hclass`: `hclass` discharged

`lix_topClass_ne_zero_of_thom`'s `hclass` is now a theorem.  Three new modules,
all **PROBE GREEN on cs-endpoint (acn116)**; the third at 9203 jobs, `sorryAx`
absent from the whole log.

| module | contents |
|---|---|
| `CharClass/ThomChartTautZero.lean` | `eulerOfBundle_comap_const_eq_zero`, `eulerOfBundle_pushforward_eq_zero_of_trivIso`, `LH.pull_zeroSectionProj_tautEulerOf`, `chartInclMap`, `chartSymmMap`, `bridgeChartIncl_eq`, `LH.pull_chartInclMap_tautEulerOf`, **`LH.pull_bridgeChartIncl_tautEulerOf`**, `bridgeChartIncl_comp_projMapOf` — **`ξ` restricts to zero on the affine chart** |
| `CharClass/ThomBridgeRelToAbs.lean` | `pull_eq_absPull`, **`relToAbs_bridgeTotal`** — the bridge commutes with `relToAbs`; the naturality `ThomBridgeTotal`'s own docstring flagged as missing |
| `CharClass/LIXHclass.lean` | `gammaCoeff_eq_of_val`, `gamma_top_eq_chernCoeff`, `chernMul_top_unit`, `lhTerm_zero_class`, `lhTerm_at_index_zero`, `pull_bridgeChartIncl_lhSum`, **`lixHclass`** |

### The proof, and where the geometry actually is

`jE(u) = π^*(γ_r)` comes out of four steps and only the first is topology.

1. **`ξ` dies on the affine chart.**  Classically this is the nowhere-zero
   section `v ↦ (v,1)` of the tautological line over `E ⊆ P(E⊕1)`.  No section is
   built here: `cc-bundle` had already proved that the chart's homotopy inverse
   **is** the zero section (`chartOpensHomotopyEquivBase_invFun_apply`) and that
   on the zero section the tautological line is the *constant* line `infPoint`
   (`tautLineZeroSectionIso`).  A constant line is pulled back from a point and a
   point has no `H^2`, so the whole statement is homotopy invariance plus
   `cohomology_unit_isZero`.  Two lemmas of cc-bundle's that had no consumer
   until now turned the one piece of real geometry into bookkeeping.
2. **The bridge commutes with `relToAbs`.**  `bridgeChart_hom_eq` says the first
   two bridge steps are one `relPullback`, and the third is a `relPullback` along
   the **identity**; `relToAbs_naturality` applies to both, and the second
   square's ambient pullback is `absPull (𝟙 _) = 𝟙`.  So `jE(u)` is the
   restriction to the chart of `relToAbs` of `u`'s partner upstairs.
3. **The coordinates.**  `thomJmTotal` is by definition `lhTopEquiv⁻¹ ∘ relToAbs`
   across the bridge, so `relToAbs (bridgeTotal u)` **is** the Leray–Hirsch
   combination of `u`'s coordinates, and `thomJmTotal_lixThomClassTerm` says
   those are `thomLift` of the unit.  Restricting to the chart sends column `i`
   to `lhTerm π' 0 (2r) i`, which vanishes for `i ≥ 1` because `cupPowE 0 (j+1) = 0`,
   and the `i = 0` column is `π^*` of the coefficient.
4. **The coefficient is `γ_r`.**  `thomLift`'s zeroth entry is `-γ_r ⌣ 1`; the
   sign is invisible over `F₂` (`neg_eq_self_two`) and the cup with the unit is
   three degree transports collapsing.  `lixChern_top_eq_gamma` then closes.

### What these files do NOT do

* Nothing about `hsq`, and nothing about the **section**: the class compared here
  is the one the *projection* pulls back.  `gamma ≠ 0` is still the consumer's
  conclusion from `hres` **and** this equation, not from this equation alone.
* `pull_bridgeChartIncl_tautEulerOf` says nothing about `ξ` off the zero section,
  where it does not vanish and where the Gysin sequence lives.  And it is about
  the **class**, not the line: the tautological line is not trivial over the
  chart on the nose, only up to the homotopy that contracts the chart.
* `relToAbs_bridgeTotal` relates the two `relToAbs` and nothing else — not
  `absToSub`, not `δ`, not naturality in the base (that is `bridgeTotal_natural`,
  a different square).

### The join with the consumer, checked before probing

`CharClass/LemmaTwoOfHsqHresHclass.lean` (already on origin/main) states `hclass`
as its second hypothesis.  `lixHclass hGc hGu (continuous_mappingTorus_lix hGc)
(isStarProjection_mappingTorus_lix hGu)` is that statement character for
character.  `hcont`/`hproj` are arguments here exactly as in
`lixChern_top_eq_gamma`, so a caller with different proofs of them still fits.
**`hdd` is not needed**, and no input was added.

### Traps

* **`absPull` lives in `RelativeSupport`, not `CharClass`.**  Without
  `open RelativeSupport` the error is `Function expected at absPull … this term
  has type ?m.1`, i.e. autoImplicit reports a missing `open` as a type error at
  the *use* site.  Same shape as the `cohomologyZMod2` trap already in this file.
* **Rewrite the hypothesis, not the goal, when a `relPullback` proof is in the
  way.**  `rw [← hnat2]` in the goal failed with *"the target expression is not
  type-correct under the `instances` transparency level"*, with a nested
  *"function expected: `range_projIncl_subset_notZero p`"*.  The abstraction has
  to pass through `relPullback`'s map-of-pairs argument.  `rw [hnat2] at hnat1`
  and then `exact hnat1.symm` touches no dependent argument and works.
* **`calc` cannot cross two spellings of one object; `Eq.trans` can.**  The chain
  starts in `↥(lixHE …)` and ends in `↥(Hmod2 (TopCat.of (Bundle.Total …)) …)`.
  These are defeq, but `calc` needs `Trans Eq Eq ?r` and instance search runs at
  reducible transparency, where `lixTotalPair` (a plain `def`) does not unfold.
  The error is the unhelpful `failed to synthesize Trans Eq Eq ?m`, reported at
  the *last* step.  `refine h.trans ?_` unifies instead of searching, and works.
* **`congrArg (fun f : _ ⟶ _ => f.hom u) h` does not elaborate**; the ascription
  leaves the category a metavariable and the field projection then fails.  Bind
  the equation to a `have` first and write `congrArg (fun t => t.hom u) h`, which
  is the spelling already green in `RelativeProdContractible`.
* **`rw`'s closing `rfl` is weaker than the `rfl` tactic.**  Three goals of the
  form `cohCast ⋯ a = a` and one `lhTopEquiv⁻¹ (…) = thomJmTotal …` survived a
  `rw` chain and needed an explicit `exact cohCast_self _ _` / an explicit
  `thomJmTotal_apply, thomJm_apply` step.  `GysinFromGraded.lhTerm_index_zero`
  already ends in `exact cohCast_self _ _` for exactly this reason.
* **Name the coefficient family before feeding it to `lhTerm`.**  Writing
  `ThomDeg.thomLift (fun i => chernMul …) x i` inline inside a `lhTerm` argument
  makes `M` a metavariable — the trap `LIXThomClassTerm` records — and the error
  is an application type mismatch naming `?m.192 i`.  `set a := thomJmTotal … u`
  once and use `a i` everywhere; it also spares the `(M := …)` pin.
* **`warningAsError=true` is on for the `GroupApproximation` lib** (`lakefile.toml`),
  so the `unusedSectionVars` linter is a hard build failure, not a warning.

### Duplicate-name coordination

Lane `lix-hres`'s in-flight `CharClass/ThomChartSquare.lean` declares
`bridgeChartIncl_mapsTo` with the identical statement.  My copy was deleted and
is now a `have` inside `relToAbs_bridgeTotal`, so the duplicate baseline stays 0
whichever of the two lands first.  `lhTerm_index_zero` was likewise renamed to
`lhTerm_at_index_zero`: `LH.lhTerm_index_zero` already exists in
`GysinFromGraded.lean`, at the degrees `n + 2` only, and with `open LH` the bare
name would have been ambiguous.

### Probe log

| date | targets | result |
|---|---|---|
| 2026-09-07 | `ThomChartTautZero` | red: `rw [← eulerOfBundle_comap]` cannot see through the `tautEulerOf` def; two `unusedSectionVars` errors |
| 2026-09-07 | **`ThomChartTautZero`** | **green** (built 9186/9203, 41s) |
| 2026-09-07 | `ThomBridgeRelToAbs` + `LIXHclass` | red: `absPull` unknown (namespace `RelativeSupport`), and the `_ ⟶ _` ascription in `congrArg` |
| 2026-09-07 | `ThomBridgeRelToAbs` + `LIXHclass` | red: `rw [← hnat2]` motive not type-correct at `instances` transparency |
| 2026-09-07 | **`ThomBridgeRelToAbs`** green; `LIXHclass` red | `chernMul_top_unit` left `cohCast ⋯ a = a`; `thomLift` inline left `M` a metavariable |
| 2026-09-07 | `LIXHclass` | red: `Trans Eq Eq ?m` at the last `calc` step |
| 2026-09-07 | **`LIXHclass`** | **green, 9203 jobs, `PROBE GREEN`, no `sorryAx` in the log** |
| 2026-09-07 | all three, `lixprobe6.sh` | **green, 9203 jobs, `axiom lines seen: 38`, `sorryAx: none`** |

### Axiom lines, by name

Read out of `lixprobe6.sh cs-endpoint` (the older `lixprobe.sh` filters whole
`info:` lines, so it printed none of these):

```text
'GroupApproximation.CharClass.LH.pull_bridgeChartIncl_tautEulerOf' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'GroupApproximation.CharClass.relToAbs_bridgeTotal' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'GroupApproximation.CharClass.lixHclass' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

**A `grep` for `sorryAx` over a filtered probe log is not evidence about a given
theorem.**  The filter drops whole `info:` lines but keeps their continuations,
so an axiom list that WRAPS leaks ` Classical.choice,` / ` Quot.sound]` while one
that fits on a single line vanishes entirely.  `lixHclass`'s list is short and
left no trace; `pull_bridgeChartIncl_tautEulerOf`'s wraps and did.  A clean grep
across such a log therefore says nothing about the short ones — and unsolved
goals close a proof with `sorryAx` while leaving **no literal token** for
`ccland.sh`'s lexical gate to catch.  `relToAbs_bridgeTotal` was in exactly that
state for one probe round.  Read the axiom line by name, or read nothing.

## 2026-09-07 — lane `lix-hsq`: `hsq` closed, by cutting a homotopy over a line

`lixHsq` (`CharClass/LIXHsq.lean`) is the `hsq` binder of
`lix_topClass_ne_zero_of_thom`, character for character, over `hGc`, `hGu`, `hGe`
and nothing else.  `#print axioms lixHsq` reports
`[propext, Classical.choice, Quot.sound]`.

### The obstruction, and why the two obvious routes are both closed

`hsq` compares two composites of relative pullbacks into the local model.  Both
outer legs are pullbacks, but `lixRelModelIso` contains an **inverse** excision,
so the square is not an equation between induced maps and cannot be checked
pointwise end to end.  Composing that excision's forward map onto both sides
removes the inverse and leaves an equation between two honest pullbacks — along
two maps of pairs out of a neighbourhood of the origin:

* left, `v ↦ the section at the chart point of v`;
* right, `v ↦ the point of the fibre over the section's zero with frame
  coordinate v`.

**These agree nowhere.**  The base coordinate varies on the left and is constant
on the right, so no amount of unfolding makes them equal, and the pointwise route
`RelativeProdContractible`'s docstring recommends stops here.

The other obvious route also fails, and it fails for a reason worth keeping.
Both sides of `hsq` are maps between `F₂`-**lines** — the source by
`ThomChernDeg.lixRelLine`, the target by `localEquiv` — and two maps between
lines are equal as soon as both are nonzero.  But "right leg nonzero" **is**
`hres`, and "left leg nonzero" is the conclusion Step C is trying to reach.  That
is the circle the 08:42–08:45 reductions fell into, and it is why this lane never
proves either leg nonzero: it proves them **equal**.

### The route: cut a homotopy at either end

Relative cohomology in this tree has no prism operator.
`RelativeHomotopyInvariance` gives **bijectivity** through the five lemma and
never an **equality** of two pullbacks, which is what the comparison needs.

Over `F₂` the equality is free once the source pair is one dimensional.
`Hom(L, L')` between two `F₂`-lines has exactly two elements, so two injective
maps into a line are the same map; and the two endpoint slices `x ↦ (b, x)` and
`x ↦ (b', x)` of a contractible parameter space both induce bijections by
`cc-relative`'s `relPullback_slice_bijective`.  So they induce the *same* map, and
any homotopy through maps of pairs may be **cut at either end**.  That is
`RelativeSupport.relPullback_eq_of_homotopy_of_line`, stated at no LIX object and
in no fixed degree.

The homotopy contracts the chart-coordinate point `q` to the origin along `s · q`
while **holding fixed the chart's reading of the section**, moving only the point
at which the reconstruction's coefficients are evaluated.  At `s = 1` the value is
the section; at `s = 0` the base point is the zero and the fibre vector is an
`ℝ`-linear automorphism of `ℂ^r` read through the standard frame.  A linear
automorphism is a homeomorphism of the punctured pair, so its own pullback is an
isomorphism of the local model — and the local model is a line, so that
isomorphism is the identity.

Three facts make the homotopy exist, and none of them is a degree computation.

### 1. `lixTrivBall` is a metric ball in chart coordinates, and that is load-bearing

`lixBaseBall` is **defined** as the base chart's image of `Metric.ball 0 ε`, so it
is star-shaped about the origin in chart coordinates.  That is the only property
of it the contraction uses.  A neighbourhood produced by an abstract "small
enough" argument would not do, and the ball is not an implementation detail of
`LIXBaseBall`; anyone rewriting that file must keep it.

### 2. The section's blocks are **linear** in the chart's coordinates

The trivial block of the section, read in the charts, *is* `eulerLocalHomeo`.  The
transverse block is `cVec`, the `(i+1)`-st column of the `j`-th projection, and in
the affine chart that column is `chartVec (wⱼ)` **times** the chart coordinate
`cpChartSection (wⱼ)ᵢ` (`tautColSection_chartAt`).  So the section is recovered
from its chart coordinates by a map linear in them whose coefficients depend only
continuously on the point: `lixEtaLin`.  The path's weight `χ(τ) = sin(πτ)` rides
in the coefficient and is strictly positive on the ball, which keeps the
reconstruction injective.

**The nondegeneracy of the zero is paid for exactly once**, when `lixProductChart`
was built from the inverse function theorem, and never again.  What `lixEtaLin`
adds is that the nondegeneracy is then usable at *every* point of the
contraction rather than at the zero alone.

### 3. TRAP — the chart is a **clamped** map, so "the chart reads the section" is FALSE off a small ball

Both chart factors are total maps made total by clamping: the sphere chart
rescales through `sphereClamp`, the circle chart through `circClamp`.  Off the
clamp's fixed region the chart reads the section **of a rescaled point**, so the
identity "the chart is the section's blocks" is not merely unproved there, it is
false.  `LIXHsqNeighbourhood` caps the comparison radius at `1/2`, which makes
both clamps inactive (the product norm bounds every coordinate, so `sphereQ ≤ 1`
and the circle coordinate lies in the open interval).  The cap costs nothing,
because the excision shrink says any smaller neighbourhood carries the same
relative group.  **Anyone building on `lixProductChart` or `lixFullChart` against
the section needs the same cap.**

### TRAP — `lixFullChart` was never connected to `lixSection` anywhere in the tree

`grep -rn trivialBlockChart GroupApproximation/` returns hits only inside the
three files that define it (`LIXSectionChart`, `LIXSectionDeriv`,
`LIXSectionLocalHomeo`).  So the sentence "`lixFullChart` charts the section",
true of the intent since 2026-09-05, was **unproved in Lean** until
`lixEtaLin_eq_blockSouth`.  A docstring is not a lemma; grep for the identity, not
for the noun.

### TRAPS met while building

* **`Homeomorph.toContinuousMap` does not exist at the pin.**  Use
  `TopCat.isoOfHomeo`, and name the iso as a `def` so its `TopCat` implicits are
  pinned: `relPairIso` cannot infer them from a `ConcreteCategory.hom`
  application and reports an application type mismatch full of metavariables.
* **A `have`-bound iso is opaque.**  `have hiso := relPairIso …` and then
  `hiso.hom.hom a = …` will not reduce to the pullback `hiso` is *defined* as; the
  error is a type mismatch between two visibly identical `relPullback`s.  Write
  the iso out at the use site, or make it a `def`.
* **`mtSection_south_form'` has no `ξ` parameter** even though `ξ` is a section
  variable of `MappingTorusSection`: a section variable the *statement* does not
  mention is not a parameter, and `(ξ := …)` is an "invalid argument name" error
  that names `n`, `M`, `Z`, `hmem` as the near misses.
* **`subInclusion` and `sInclusion` take their ambient implicitly** and cannot
  recover a `TopCat` from a `Set` of a plain type.  Pin it: `subInclusion
  (X := TopCat.of (Fin r → ℂ)) h`.  Same failure `cc-thom` recorded for `absToSub`.
* **`Matrix.dotProduct` is `dotProduct`** (root namespace), and `simp only
  [Matrix.mulVec, dotProduct]` unfolds `mulVec` into `⬝ᵥ` without unfolding
  `⬝ᵥ`; a following `rw` then fails to find its sum.  State the sum with `show`
  instead.
* **One `rfl` too many is a build that never returns.**  `LIXHsq` in its first
  form discharged all seven "this iso's `hom` is that pullback" identifications
  inside the theorems that used them.  Elaboration went past the heartbeat limit
  in `whnf` with errors naming the whole theorem, and one earlier form ran for
  half an hour in the kernel with no output at all.  Stated one at a time as
  their own `rfl` lemmas (`LIXHsqLegs` §4) each is a small delta-reduction, every
  one compiles in seconds, and a failure names the factor that moved.
* **An import can cost more than the module.**  `LIXHsq`'s first version imported
  `LIXStepCOddThom` for a corollary it did not contain; that import alone pulls in
  the whole Leray–Hirsch and Thom closure and turned a 20-second module into a
  build of several hundred.  The corollary lives in its own module,
  `LIXStepCOddHsq`, so the square itself stays cheap.

### The check that no probe of this lane could make

A lane can prove a theorem whose statement has drifted from the binder it was
written for, and no probe of the lane's own modules will see it, because the lane
never mentions the consumer.  `CharClass/LIXStepCOddHsq.lean` applies
`lix_topClass_ne_zero_of_thom` **at the binder** with `lixHsq` supplied.  That is
the only thing that catches the drift, and it is why the corollary exists at all.

### Probe log

| date | targets | result |
|---|---|---|
| 2026-09-07 | `RelativeLineHomotopy` | **green, 8785 jobs, `PROBE GREEN`, first probe**, `0f79b48cf` |
| 2026-09-07 | `LIXHsqNeighbourhood` | red: `congrArg (fun t : _ ⟶ _ => t.hom a)` cannot project; `subInclusion` ambient not pinned |
| 2026-09-07 | **`LIXHsqNeighbourhood`** | **green, 8878 jobs**, `56fd504b9`; radius capped at `1/2` at `3de02c2c3` |
| 2026-09-07 | `LIXHsqEta` | red: one `ring` after a `simp` that had already closed the goal |
| 2026-09-07 | **`LIXHsqEta`** | **green, 8879 jobs**, `91e737744` |
| 2026-09-07 | `LIXHsqLinear` | red x3: `(ξ := …)`, `Matrix.dotProduct`, `Homeomorph.toContinuousMap`, then the opaque `have`-bound iso |
| 2026-09-07 | **`LIXHsqLinear` + `LIXHsqHomotopy`** | **green, 8887 jobs**, `e6ea9a93c` |
| 2026-09-07 | `LIXHsq` (one file, seven inline `rfl`s) | 28 minutes with no output, then heartbeat timeouts in `whnf` naming whole theorems |
| 2026-09-07 | **`LIXHsqLegs`** (identifications split out) | **green, 8890 jobs** |
| 2026-09-07 | **all seven** | **green, 8891 jobs, `sorryAx: none`**, `lixHsq` on `[propext, Classical.choice, Quot.sound]`, `ef0b678cb` |
