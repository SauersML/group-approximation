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

## AUTHORED, not compiled

- `GysinTautChartOf` (attic): `rChartOf_tautEulerK`, written against lix-lh's `ChernEulerBundleOf` /
  `LerayHirschChartClassK`, which are not on main yet.

## NEEDS (declaration level)

- An Euler class over K (`eulerOfBundle`, `eulerOfBundle_comap`, `eulerOfBundle_eq_zero_of_factors` over K), for
  GysinTautFields §4 (`rChart_tautEuler`) over K.  Owner unknown; asked the lead.
- Line in degree 2d of `H^*(ℂP^d; K)` (lix-lh's projective computation over K) for `HasTopLineOf K (CP d) (2d)`.  Not
  needed for the recursion: the vanishing comes from `kunnethFactor_CPOf`.

## TRAPS

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
