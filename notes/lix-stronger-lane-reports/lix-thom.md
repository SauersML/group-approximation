# Lane `lix-thom` — the coefficient parameter `K` in Thom / Gysin / Bundle / Slice (successor of sp-thom)

Program: `notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5.  Lead: nonsofic-existence-41.  Shared clone `lix-b`
(rule 20).  The lane owns `CharClass/Thom*`, `Gysin*`, `Bundle*`, `Slice*`, `RelativeSupport*`, `ThomStepCEuler*`, and
`LIXThomAssembly` (lead ruling 21:55).

## Design rule of this lane: K-forms go in NEW `…Of` modules

The F₂ files feed the verified mod-2 answer to LIX, and every import added to one of them reaches every root build.
So the K-forms live in new modules named `<F₂ module>Of`, which import the F₂ module plus the K-generic layers.  The
F₂ files change only additively, and only where no import is needed (ThomBridgeChart, ThomBundlePair,
ThomBridgeChartHom, GysinFromGraded).  The one exception is GysinFromGraded, which was made generic in place with K
implicit; its two F₂ importers are byte-unchanged.

## STEP 0 (2026-09-11 ~21:25)

- sp-thom's 16 locally modified files were byte-identical to origin, landed by rescue-lix in gate B (dd28464fc), and
  the 13 Batch-A modules have compiled evidence in rescue-lix.green.0911-194230-57555.  Nothing was lost.
- Measured on origin: 111 files carry the four prefixes, and 48 still name `ZMod 2`/`Hmod2`/`cohomologyZMod2` in code.

## GREEN (compiled, landed normally)

| sha | probe | modules |
|---|---|---|
| a82df617e | 0911-215659-72612 | ThomStepCEulerOf, ThomToolkitInstanceOf, GysinFromGraded (over K), ThomBridgeChart (+`bridgeChartOf`), ThomBundlePair (+`bundlePairTrivIsoOf`) |
| 343a27cd7 | 0911-220621-37569 | ThomBridgeChartHom (+`bridgeChartOf_hom_eq`, `bridgeChartOf_natural`); GysinRetractOf, GysinSphereOf, ThomStepCLocalOf (already byte-identical on main) |

Mathematical content over a field K:
- **Step C over K** (`ThomStepCEulerOf`, `ThomStepCLocalOf`).  γ_r ≠ 0 from su ≠ 0, with no generator
  identification.  The F₂ step "a nonzero class of the local model is the generator" (`decide`) is false over K; over K
  it becomes `hsu_isUnit_of_ne_zeroOf`, a unit multiple, and no consumer needs it.  The odd-side forms
  `topChernClass_ne_zero_oddOf` / `_odd_isoOf` / `_odd_localOf` / `_odd_localModelOf` are the K-forms of what LIXKStepC,
  LIXThomDatum and LIXStepCOddLocal consume.
- **Punctured acyclicity over K** (`ThomToolkitInstanceOf`).  `cohomologyToolkitOf K`, `puncturedAcyclic_prodOf`,
  `puncturedAcyclic_sphereOf`.
- **Gysin readings over K** (`GysinRetractOf`): `rChartOf K` / `rNotZeroOf K` are sections of the projection and are
  multiplicative.  **Unit vectors over K** (`GysinSphereOf`): the K-cohomology of S^{2d+1}.
- **Thom bridge steps 1–2 over K** (`bridgeChartOf K [Field K]`), a single relative pullback, natural in the base.

| 902250273 | 0911-221742-20681 | ThomChernDegreewiseOf, GysinPairTautOf, ThomDataOf |
| (identical) | 0911-225755-70521 | ThomTopLineOf, ThomKunnethOf, GysinPairRetractOf |
| adb163993 | 0911-231754-79319 (PROBE GREEN) | ThomHabsOf, ThomBridgeTotalOf, ThomProjectivePuncturedOf |

Further content over K (probes 3–5):
- **The Thom data over K** (`ThomChernDegreewiseOf`, `ThomHabsOf`, `ThomBridgeTotalOf`).  The degreewise Chern relation,
  `lhTopEquivOf`, the restriction square, habs, relToAbs injectivity, `thomData_of_lerayHirschOf`, the Thom bridge
  `bridgeTotalOf K`, and `thomData_total_of_lerayHirschOf`.  The Leray–Hirsch generator is left arbitrary.
- **Künneth factors, top lines, projective base case over K** (`ThomKunnethOf`, `ThomTopLineOf`,
  `ThomProjectivePuncturedOf`).  `kunnethFactor_sphereOf`, `kunnethFactor_CPOf`; `HasTopLineOf`, with the circle step
  proved over a field by the rank count; `hasTopLineOf_prod_sphere`, `hasTopLineOf_prod_CP`;
  `isZero_cohomology_CPOf` (from the Künneth factor with a point), `puncturedAcyclic_CPOf`,
  `kunnethFactor_CP_puncturedOf`.  Step C over F_p gets its `hacyclic` and `absLine` inputs from these.
- **Gysin pair condition over K** (`GysinPairTautOf`, `GysinPairRetractOf`).

| (identical) | 0911-233524-73677 (GREEN) | GysinTautChartOf |
| ffc437ff2 | 0911-234055-22190 (GREEN) | ThomBridgeTotalNaturalOf, ThomJmNaturalOf (compiled before the relaunch, landed 09-12) |
| e70b58371 | 0911-234431-51070 (GREEN) | ThomBridgeRelToAbsOf (compiled before the relaunch, landed 09-12) |

Further content over K (probes 6–8):
- **The tautological class dies on the chart** (`GysinTautChartOf.rChartOf_tautEulerK`), for every generator `hgen`,
  against lix-lh's `eulerOfBundleOf`.
- **Naturality** (`ThomBridgeTotalNaturalOf`, `ThomJmNaturalOf`): `bridgeTotalRestrictOf`, `thomJm_naturalOf` (any ring),
  `thomJmTotalOf`, `thomJmTotal_restrictOf` (the generators and their compatibility `hξ` are arguments).
- **The bridge commutes with relToAbs** (`ThomBridgeRelToAbsOf.relToAbs_bridgeTotalOf`).

| 8ada97d0e | probe 10 | ThomHyperplaneLHOf (`hyperLHOf`, `thomData_total_of_tautOf`; the Leray–Hirsch instances are arguments) |
| (landed) | probe 11 (GREEN) | ThomSphereSubspaceOf (`absToSub_injective_of_sphereOf`, `relQuotEquiv_of_sphereOf`), BundleTotalPiCohIsoOf |

All authored modules of this lane are compiled.

## STOPPED (09-12)

The lead relayed the user's 09-12 ruling ("LIX is too low impact"): no new authoring and no new probes.  At the stop
this lane had no probe running and no unlanded file.  Every path in `lanes/lix-thom.files` is on main, byte-identical and
compiled.  Nothing from this lane is landed UNVERIFIED or in the attic.  The next targets, the `Slice*Of` port and
ThomChartTautZero over K, were not authored.  Their exact statements follow, for a restart.

## Left F₂-only in the lane's prefixes, and why

- `SliceHomogeneous`, `SliceValueV`, `SliceSplitV`, `SliceRoots`: `Finset.prod` of degree-two classes needs a
  `CommMonoid`, and at odd p the total ring over K is only a `GRing`.

  **Lead ruling (09-11):** port these into new `Slice*Of` files that multiply in the commutative even subring
  `Gen.evenPart K`.  This is lix-evenside's convention in `ChernSplittingOfWhitney`: Whitney in `Gen.evenPart K F`, with
  ρ = `Gen.evenMap K proj`.

  None of these files is authored.  The residual statements use `{K : Type} [CommRing K]` unless marked, and
  `evenTautOf K ξ = ⟨TotalHOf.of K _ 2 ξ, _⟩`:

  ```lean
  -- SliceHomogeneousOf
  theorem exists_of_prodOf {X : TopCat.{0}} {σ : Type} (B : Finset σ) (y : σ → Hmod K X 2) :
      ∃ a : Hmod K X (2 * B.card),
        ((∏ l ∈ B, evenTautOf K (y l) : Gen.evenPart K X) : TotalHOf K X)
          = TotalHOf.of K X (2 * B.card) a
  theorem of_component_esymmOnOf {X : TopCat.{0}} {σ : Type} (s : Finset σ) (y : σ → Hmod K X 2)
      (q : ℕ) :
      TotalHOf.of K X (2 * q) (TotalHOf.component K X (2 * q)
          (esymmOn s (fun l => evenTautOf K (y l)) q : TotalHOf K X))
        = (esymmOn s (fun l => evenTautOf K (y l)) q : TotalHOf K X)

  -- SliceValueVOf.  Proof: chern_split_of_splitPoly D (𝟙 Y) with
  -- splitPoly_of_splitRelation D D (𝟙 Y) (𝟙 P), and totalHOf_map_id for evenMap (𝟙 Y).
  theorem chern_eq_esymmOn_of_splitRelationOf {Y P : TopCat.{0}} [Nontrivial (Gen.evenPart K Y)]
      (D : LerayHirschDataEvenOf K Y P) (r : ℕ) (hr : D.rank = r) (root : ℕ → Hmod K Y 2)
      (hrel : ∏ l ∈ Finset.range r,
        (evenTautOf K D.taut + Gen.evenMap K D.proj (evenTautOf K (root l))) = 0) (q : ℕ) :
      D.chern q = esymmOn (Finset.range r) (fun l => evenTautOf K (root l)) q
  theorem chern_eq_sliceClass_coeffOf  -- binders `dd`, `ℓ` as in F₂ SliceValueV
      [Nontrivial (Gen.evenPart K Y)] (D : LerayHirschDataEvenOf K Y P) (hr : D.rank = lixRank dd)
      (root : ℕ → Hmod K Y 2)
      (hrel : ∏ l ∈ Finset.range (lixRank dd),
        (evenTautOf K D.taut + Gen.evenMap K D.proj (evenTautOf K (root l))) = 0)
      (gen : Fin ℓ → Gen.evenPart K Y)
      (hzero : ∀ i : Fin 3, root (vIndexEquiv dd (Sum.inl i) : ℕ) = 0)
      (hgen : ∀ b : HBlk dd, evenTautOf K (root (vIndexEquiv dd (Sum.inr b) : ℕ)) = gen b.1)
      (q : ℕ) :
      D.chern q = (sliceClass Finset.univ gen dd).coeff q

  -- SliceSplitVOf  [Field K], hgen : Hmod K (CPtop d) 2
  def lineEulerOfK (hgen) (q) (hq) : Hmod K _ 2 :=
    eulerOfBundleOf K hgen (pushforward (tautEmbOf ι) (tautEmbOf_injective ι) q) (trace_pushforward_one …)
  theorem pull_factor_eq_zeroOf … :
      pull (opIncl (lineOpens p q)) 2
        (tautEulerDualK K hgen p + pull (projMapOf p) 2 (lineEulerOfK K hgen q hq)) = 0
  theorem splitRelation_of_sumOf (D : LerayHirschDataEvenOf K _ _) (hDproj : D.proj = projMapOf p)
      (hDtaut : D.taut = tautEulerDualK K hgen p) (r : ℕ) (hr : 0 < r)
      (qf) (hq) (hsum)  -- as in F₂ SliceSplitV.splitRelation_of_sum
      : ∏ l ∈ Finset.range r, (evenTautOf K D.taut
          + Gen.evenMap K D.proj (evenTautOf K (lineEulerOfK K hgen (qf l) (hq l)))) = 0
  ```

  **Proof route for `splitRelation_of_sumOf`.**
  1. `prod_eq_zero_of_coverOf` with `coverSup_lineOpens` makes the ordered `List.prod` vanish in `TotalHOf`.
  2. `evenCoe_injective`, together with rewriting `Finset.range` to `List.range`, moves that vanishing into the even part.

  **Sign trap over K:** e(L)|U = π^*e(q)|U.  So the `+` form needs ξ = `tautEulerDualK` (= −`tautEulerOfK`) with
  roots e(q_l).

  **SliceRootsOf:** Euler roots `vRootOf`, which are zero on the three constant lines.  It also needs the block
  identification `lineEulerOfK K hgen (vLineYBundle (Sum.inr b)) _ = pull (cmap (baseYFactor dd b.1)) 2 (g b.1)`.

  **Inputs, all on main but UNVERIFIED** (lix-lh, 77c5176d3):
  - In `CharClass/ChernEulerIsoOf`: `CPn.eulerOfBundle_eq_of_bundleIsoOf K hd hgen p q hp hq e` and
    `CPn.eulerOfBundle_pushforward_congrOf`.
  - In `CharClass/ProjectiveSpaceStableOf`: `CPn.bijective_pull_cpBlockInclIterOf K d hd`, the generator
    compatibility.
- `ThomChartTautZero`: the K-form of `CPn.eulerOfBundle_pushforward_congr` is now on main, UNVERIFIED (lix-lh,
  77c5176d3, `CharClass/ChernEulerIsoOf`):

  ```lean
  theorem CPn.eulerOfBundle_pushforward_congrOf (K) [Field K] … {N : ℕ} (hN : 1 ≤ N) (hgen : Hmod K (CPtop N) 2)
      (p : Bundle X ι) (q : Bundle X κ) (hf : Function.Injective f) (hg : Function.Injective g)
      (hfp : ∀ x, (pushforward f hf p x).trace = 1) (hgq : ∀ x, (pushforward g hg q x).trace = 1)
      (e : BundleIso p q) :
      eulerOfBundleOf K hgen (pushforward f hf p) hfp = eulerOfBundleOf K hgen (pushforward g hg q) hgq
  ```

  It holds for every `hgen`.  The K analogue of ThomChartTautZero:96 is
  `rw [CPn.eulerOfBundle_pushforward_congrOf K hN hgen q (triv X (Fin 1)) hf hg hfq hgq e]`.  It is not authored,
  because of the stop order.
- `ThomTopLineLIX`, `ThomCoordinates`: rank-two LIX instances, consumed by the LIX lanes.
- `ThomSectionDetect` / `ThomStepCOdd*` / `ThomStepCSection` / `ThomChainHne`: superseded over K by the `…Of` forms in
  ThomStepCEulerOf / ThomStepCLocalOf.

## NEEDS (declaration level)

- Line in degree 2d of `H^*(ℂP^d; K)` (lix-lh's projective computation over K) for `HasTopLineOf K (CP d) (2d)`.  Not
  needed for the recursion: the vanishing comes from `kunnethFactor_CPOf`.

## TRAPS

- Subscript `₊` in a binder name breaks the parse (`ξ₊` → "unexpected token '₊'"), and every declaration below the break
  reports as unknown.

- `RelativeLES` does not bring `Hmod` into scope; import `CohomologyBasic`.  `sInclusion` lives in
  `GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree`; open it.
- `cohPullbackK_apply_eq` is `rfl`, so `show pull … = _` replaces the import of `CohomologyKunnethHemiOf`, whose
  closure reaches `MayerVietorisPullOf`.
- `KroneckerContractible.pull_eq_of_homotopicOf` is not reached by the F₂ Gysin files.  Adding it to their imports would
  change the F₂ closure, so K-forms go in a new module that imports it.
- `excisionIsoOf` takes its section variables first: `excisionIsoOf U V K hUV n`, not `excisionIsoOf K U V …`.  The old
  sp-thom A2 patch had the order wrong.
- A module-level duplicate scan must also compare content.  `RelativeLocalModelOf.ne_zero_of_isoOf` (CommRing) and
  `ThomStepCEulerOf.iso_hom_ne_zeroOf` (Ring) state the same fact at different generality.  Both are kept; the second
  keeps ThomStepCEulerOf's closure two modules wide.
