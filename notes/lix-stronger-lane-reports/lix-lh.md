# Lane `lix-lh` — the coefficient parameter through Leray–Hirsch, Chern, projective space, the chart tower, and Mayer–Vietoris

**WOUND DOWN 09-12.**  The lead's order passed on the user's ruling that LIX strengthenings have less impact than
non-MF work.  Everything is on main.  The remaining statements are in the last sections, ready for a restart.

Successor of `sp-lh` (`notes/lix-stronger-lane-reports/sp-lh.md`, read in full).  Clone `nm-b` (shared; lix-i
was never created).  Owns `CharClass/LerayHirsch*`, `Chern*` (incl. `ChernTotalRing`), `Projective*`,
`CohomologyChart*`, and `MayerVietoris*` + `CohomologyDelta*` (`nm/LIX_LANES.md` + lead rulings 09-11 ~21:40).
`CohomologyMayerVietoris*` stays lix-coeff's and is consumed read-only.

## STEP 0 (09-11 21:30)

- Six predecessor files differed from origin (`LerayHirschCover`, `RankTwo`, `Shift`, `Peel`, `PeelCP`,
  `PeelClosed`); each was md5-identical to rescue-lix's attic copy on origin.  Nothing untracked.  Everything
  else sp-lh authored (MVSequenceOf, lhDomainOf, colPullOf, HasCPCohomologyOf, tautEulerDual, ShiftTerm) was
  already compiled on origin; the `ChernRelation` Conventions block (the single source of the root convention)
  is on origin too.
- Why the six were red: the generic `LHOver_sup` called `bijective_lhSum_comap`, which runs on the F₂-only
  `mvSequence`, and `bijective_lhSum_two` used lix-thom's F₂-only `lhSum_two_apply`/`colTwo`.

## LANDED

| sha | what | state |
|---|---|---|
| `0b20e149e` | `ChernTotalRingOf` (TotalPieceOf, TotalHOf, instGRingOf, of/component/…/map) | UNVERIFIED, then compiled (probe 1) |
| `35c6f5056` | `MayerVietorisElementOf`, `SequenceOf`, `ZeroOf` | UNVERIFIED, then compiled (probe 1) |
| `3b4df4ec0` | ChartRankTwoInterface, ChartInduction, ChartGenBridge, ProjectiveSpaceGenHyp: `cup_comm_of_even` | COMPILED |
| `4252ac767` | `LerayHirschMVOf` (bijective_lhSum_comapOf, LHOver_supOf) | UNVERIFIED, then compiled (probe 3) |
| `4ad91fa8a` | PullOf, DeltaLiftOf/SpecOf/CupOf/NaturalOf, DisjointOf, Cover/RankTwo/Shift over K, Tower/TowerTop/Freeness | COMPILED |
| `6a5fd08ab` | LerayHirschPeel/PeelCP/PeelClosed/ColumnPack over K | COMPILED |
| `dc2f633a8` | `ChernClassesOf` + this report | COMPILED (probe 4) |
| `d1f4a9b27`, `ad93d6a93` | `ChernEulerBundleOf` (eulerOfBundleOf K hgen, comap, cpTaut, homotopic, zero_of_factors, hasPointCohomology_of_contractibleOf), `LerayHirschChartClassK` (`LH.tautEulerK`) | UNVERIFIED, then compiled (probe 5, same bytes) |
| `2e6ff7cd4` | `ChernClassesEvenOf` (the even-part carrier `LerayHirschDataEvenOf`) | UNVERIFIED, then compiled (probe 6, same bytes) |
| `d15ad41aa` | `ChernGammaBridgeOf` (`chern_relation_lhFunEvenOf`, `chern_relation_lhFunOf`, with the minus) | UNVERIFIED, then compiled (probe 6) |
| `83040f510`, `9e0fab4ac` | `ProjectiveSpaceComputationOf` (`hasCPCohomologyOf_CP K d`) | UNVERIFIED, then compiled (probe 7, same bytes) |
| `0b1db2833` | `LerayHirschChartClassGenK` (`tautEulerOfK`, `tautEulerDualK`, `tautEulerOf_comapOf`) | UNVERIFIED, then compiled (probe 7) |
| `fc92ba049` | `CohomologyChartCoverOf` (the chart cover of `U × ℂP^{d+1}` over K) | UNVERIFIED, then compiled (probes 8 and 9) |
| `52095fce7`, `bad666ccf` | `CohomologyChartFlatOf` (`eq_zero_interSpace_evenOf`, `exists_flat_of_mvResVOf`, `exists_flat_zeroOf`, `mvResVOf_surjective_zero`, `decomposition_zeroOf`) | UNVERIFIED; failed in probe 8 (a trailing `rfl`); fixed; then compiled (probe 9, same bytes as main) |
| `77c5176d3` | `ProjectiveSpaceStableOf`, `ChernEulerIsoOf` | **UNVERIFIED** (written during the wind-down; no probe started) |
| attics | e8c44817b, the PullOf/RankTwo fixes, ColumnPack over K | ATTIC |

## GREEN (with job counts)

- probe `0911-214535-67476` (nm-b, base d02e576c7, SLURM acn29): 9 files COMPILED.
- probe `0911-221318-90775` (nm-b, base 93e1d2992, acn112 88-95): 20 files COMPILED; LerayHirschChart, ChartTwo,
  Finite, Product built against the generic Cover/RankTwo.
- probe `0911-222934-2669` (nm-b): LerayHirschMVOf, Peel, PeelCP, PeelClosed, ColumnPack COMPILED; ChartGeneral,
  FreeTuple, Ladder, CohomologyLHDegreewise built against the new statements.
- probe `0911-223543-45625` (nm-b): `✔ [2460/2460] Built GroupApproximation.CharClass.ChernClassesOf`, PROBE GREEN.
- probe `0911-231924-87562` (nm-b): `✔ [8904/8904] Built GroupApproximation.CharClass.LerayHirschChartClassK`, PROBE GREEN; ChernEulerBundleOf compiled.
- probe `0911-235151-7107` (nm-b): ChernClassesEvenOf, ChernGammaBridgeOf COMPILED; ProjectiveSpaceComputationOf failed (namespace `Gysin.`).
- probe `0912-000310-7985` (nm-b): PROBE GREEN, ProjectiveSpaceComputationOf and LerayHirschChartClassGenK BUILT.
- probe `0912-004224-3272` (nm-b, probe 8): CohomologyChartCoverOf COMPILED; CohomologyChartFlatOf failed at 90:6
  ("No goals to be solved").
- probe `0912-092136-11818` (nm-b, probe 9): `✔ [8892/8892] Built GroupApproximation.CharClass.CohomologyChartFlatOf`,
  PROBE GREEN, 34 overlay files COMPILED (CoverOf and FlatOf included).

## AUTHORED, UNVERIFIED (on main at `77c5176d3`, never compiled)

`GroupApproximation/CharClass/ProjectiveSpaceStableOf.lean` (namespace `GroupApproximation.CharClass.CPn`) is
the `K` form of `ProjectiveSpaceStable` §1–2.  It carries the result along `cpInclIter` and the block inclusion:

```lean
theorem bijective_pull_cpInclPOf (K : Type) [CommRing K] (d n : ℕ) :
    Function.Bijective (pull (K := K) (cpInclP d) n)
theorem resVOf_eq_pull (K : Type) [Field K] (d n : ℕ) (a : Hmod K (CPtop (d + 1)) n) :
    (mvSequenceOf K (chartOpen d) (punctOpen d) (chartOpen_sup_punctOpen d)).resV n a
      = pull (punctIncl d) n a
theorem bijective_resVOf_two (K : Type) [Field K] (d : ℕ) (hd : 1 ≤ d) :
    Function.Bijective
      ((mvSequenceOf K (chartOpen d) (punctOpen d) (chartOpen_sup_punctOpen d)).resV 2)
theorem bijective_pull_punctInclOf_two (K : Type) [Field K] (d : ℕ) (hd : 1 ≤ d) :
    Function.Bijective (pull (K := K) (punctIncl d) 2)
theorem bijective_pull_cpInclOf (K : Type) [Field K] (d : ℕ) (hd : 1 ≤ d) :
    Function.Bijective (pull (K := K) (cpIncl d) 2)
theorem bijective_pull_cpInclIterOf (K : Type) [Field K] (d : ℕ) (hd : 1 ≤ d) (k : ℕ) :
    Function.Bijective (pull (K := K) (cpInclIter d k) 2)
theorem bijective_pull_cpBlockInclIterOf (K : Type) [Field K] (d : ℕ) (hd : 1 ≤ d) :
    Function.Bijective (pull (K := K) (cmap (cpBlockInclIter d)) 2)
```

`GroupApproximation/CharClass/ChernEulerIsoOf.lean` (namespace `CPn`) holds for ARBITRARY `hgen`, with no
stability hypothesis.  The block pullback is surjective, so it supplies `H` with `pull block 2 H = hgen`:

```lean
theorem eulerOfBundle_eq_of_bundleIsoOf (K : Type) [Field K] {X : Type} [TopologicalSpace X]
    {d : ℕ} (hd : 1 ≤ d) (hgen : Hmod K (CPtop d) 2) (p q : Bundle X (Fin (d + 1)))
    (hp : ∀ x, (p x).trace = 1) (hq : ∀ x, (q x).trace = 1) (e : BundleIso p q) :
    eulerOfBundleOf K hgen p hp = eulerOfBundleOf K hgen q hq
theorem eulerOfBundle_pushforward_congrOf (K : Type) [Field K] {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {N : ℕ} (hN : 1 ≤ N)
    (hgen : Hmod K (CPtop N) 2) (p : Bundle X ι) (q : Bundle X κ)
    {f : ι → Fin (N + 1)} (hf : Function.Injective f)
    {g : κ → Fin (N + 1)} (hg : Function.Injective g)
    (hfp : ∀ x, (pushforward f hf p x).trace = 1)
    (hgq : ∀ x, (pushforward g hg q x).trace = 1)
    (e : BundleIso p q) :
    eulerOfBundleOf K hgen (pushforward f hf p) hfp
      = eulerOfBundleOf K hgen (pushforward g hg q) hgq
```

Nothing on main uses these yet.  lix-thom records `eulerOfBundle_pushforward_congrOf` as the UNVERIFIED input
for ThomChartTautZero and SliceRootsOf over K (`lix-thom.md`).  lix-evenside records its planned use of
`eulerOfBundle_eq_of_bundleIsoOf` as an unfinished item (`lix-evenside.md`).  Both lanes stopped without writing
code that uses them.

A first probe should check these spots.  Each mirrors an F₂ proof that compiled:
- the `rfl` after `rw [mvResVOf_eq_pull]` in `resVOf_eq_pull`;
- the zero case of `bijective_pull_cpInclIterOf` (`funext fun a => pull_id 2 a` against `cpInclIter d 0`);
- the `rw [eulerClassOf, eulerClassOf, ← hH, ← pull_comp, ← pull_comp]` chain in
  `eulerOfBundle_eq_of_bundleIsoOf`.

## UNFINISHED at the wind-down (exact statements; nothing below was written as Lean)

The port of the chart tower over K was meant to end in the compact Leray–Hirsch theorem over K.  The F₂ version
is `LerayHirschCompact:62`:

```lean
theorem LH.lerayHirschGraded_compact [CompactSpace X] [Nonempty X]
    (q : Bundle X ι) (s : ℕ) (hs : ∀ x, q.rank x = s) (hs1 : 1 ≤ s) :
    LerayHirschGraded (projMapOf q) (tautEulerOf q) s
```

The K target (proposed spelling; not written):

```lean
theorem LH.lerayHirschGraded_compactOf (K : Type) [Field K] [CompactSpace X] [Nonempty X]
    (q : Bundle X ι) (s : ℕ) (hs : ∀ x, q.rank x = s) (hs1 : 1 ≤ s)
    (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2) (hgen0 : hgen ≠ 0) :
    LerayHirschGraded (projMapOf q) (tautEulerOfK K hgen q) s
```

The same statement is also needed with `tautEulerDualK K hgen q` (= `−tautEulerOfK K hgen q`), the class that
lix-evenside's flag relation uses.  Over a field, `hgen ≠ 0` is enough.  `H²(ℂP^N; K)` is a line
(`hasCPCohomologyOf_CP`), and `bijective_pull_cpInclIterOf` carries a nonzero class to a nonzero class, hence a
basis, of every `H²(ℂP^d; K)` with `1 ≤ d ≤ N`.

The intermediate results use F₂ types, and each needs a K counterpart (`Hmod2` → `Hmod K`, `cpGen` → the pulled
back `hgen`):

```lean
-- LerayHirschBundle:69
theorem lerayHirschGraded_of_trivializing_cover [CompactSpace X] [Nonempty X]
    (p : Bundle X ι) (f : P ⟶ TopCat.of X) (ξ : Hmod2 P 2) (r : ℕ)
    (hLH : ∀ (x₀ : X) (W : Opens (TopCat.of X)), LHOver f ξ r (trivOpen p x₀ ⊓ W)) :
    LerayHirschGraded f ξ r
-- LerayHirschRankOne:77
theorem lerayHirschGraded_rankOne (q : Bundle X ι) (hq : ∀ x, (q x).trace = 1)
    (ξ : Hmod2 (TopCat.of (Proj q)) 2) :
    LerayHirschGraded (projMapOf q) ξ 1
-- LerayHirschTrivOpen:50
--   LHOver_trivOpen q x₀ W d (hrank : q.rank x₀ = d + 1 + 1)
--     (hξ : pull (chartProdIsoOfHomeo q (trivOpen q x₀ ⊓ W) (d + 1) (projTrivStdOn …)).hom 2
--             (pull (KnCP.cpSnd …) 2 (cpGen …)) = …) : LHOver …
-- LerayHirschCompact:42
--   hxi_trivOpen q x₀ W d (hrank : q.rank x₀ = d + 1 + 1) : the same chart identity for tautEulerOf q
-- ChernEulerEmbed:43
theorem eulerClass_cpEmbed_iterMat {X : TopCat.{0}} (a k : ℕ) (ha : 1 ≤ a)
    (g : X ⟶ CPtop a) :
    eulerClass (cpGen (a + k) (by omega))
        (g ≫ cmap (cpEmbed (iterMat a k) (iterMat_isometry a k))) = …
```

Below these sits the F₂ chart chain `LerayHirschChartGeneral`, `ChartBundleGen`, `ChartHomeo`, `ChartClassIso`,
`ChartTautGen`, `TrivOpen`, `Bundle`, `Union`, `Finite`.  The chain also needs `ChernEulerIndex`'s
`eulerOfBundle_pushforward_iterFin` (line 88) and `eulerOfBundle_pushforward_eq_of_bundleIso` (line 109).  Some
K layers are already compiled: the Mayer–Vietoris gluing `LHOver_supOf`, the chart cover and flat layer, and
rank two.

State of the older open items at the wind-down:
1. `ChernSplitRelation`, `ChernGammaBridge` and `ChernGammaComponent` over K on `LerayHirschDataOf K`: not
   started.
2. The `Wu.HasSplitting` producers over K: not started.  They wait on lix-cupone's `TotalHOf.IsEven`.
3. The chart tower over `F_p`: its input `hasCPCohomologyOf_CP` is compiled, and the tower itself is the
   unfinished work above.

## Design decisions

- **The Mayer–Vietoris sign over K.**  The chain map is `biprod.lift ι (−ι')`, so the composite through the middle
  term on the `V` side is **minus** the restriction.  `mvResWVOf` is defined as its negative (the honest
  restriction); `exact_sum` is agreement of the honest restrictions; the cochain data of `mvDeltaOf_spec` is
  `α_U| − α_V| = α` (F₂: `+`).
- **Additive `Of` twins, F₂ names untouched.**  Every `MayerVietoris*Of`, `CohomologyDelta*Of`, `LerayHirschMVOf`,
  `ChernClassesOf`, `ChernTotalRingOf` is a new module, so no F₂ consumer rebuilds.  `LHOver_sup` stays F₂;
  `LHOver_supOf K` is the generic twin.
- **The Euler class over K takes the generator as data.**  Over `F₂` `cpGen` is canonical (a line has one nonzero
  element); over `K` it is not, so `eulerOfBundleOf K hgen`.  Naturality, normalisation, homotopy invariance,
  vanishing through a space without `H²`, and (unverified, `77c5176d3`) isomorphism invariance hold for every
  `hgen`.
- **Over K, stability is bijectivity, not a statement about a generator.**  Over `F₂` the hyperplane inclusion
  carries `cpGen` to `cpGen`.  Over `K` the statement carried over is that pullback is bijective on `H²`, which
  is enough for the Euler-class isomorphism invariance.
- **Chern classes over K take commutativity as data.**  `TotalHOf K X` is only a `DirectSum.GRing`; the base ring
  commutativity and the centrality of pulled-back classes are fields of `LerayHirschDataOf`, produced from even
  concentration (lix-cupone's `mul_comm_of_isEven`).  No `mul_comm` on `TotalHOf`, ever.
- **The degreewise `gamma` over K is `−c_k`.**  The monic relation `ξ^r + Σ c_k ξ^{r−k} = 0` makes the Leray–Hirsch
  coordinates of `ξ^r` the negated coefficients (`chern_relation_lhFunEvenOf`).  Consumers take the ring classes
  `LerayHirschDataEvenOf.chern`; a bridge to `LerayHirschGraded.gamma` carries the minus explicitly.
- **The flag-relation sign.**  The plus-sign relation `∏ (taut + e(L_l)) = 0` holds with
  `taut = e(O(1)) = tautEulerDualK = −tautEulerOfK` (answer to lix-evenside, input (d)).
- **Even parts at odd p.**  `LerayHirschDataEvenOf` runs Leray–Hirsch between `Gen.evenPart K X` and
  `Gen.evenPart K P` (lix-evenside-n), both commutative, so no commutativity/centrality data is needed; this is THE
  carrier lix-evenside consumes.

## NEEDS

- none (wound down).

## TRAPS

- **A `-` inside a composite whose middle object is spelled `(mvCoSCOf K U V hUV).X₃`** (a def's structure
  projection) does not match `Preadditive.neg_comp` / `HomologicalComplex.homologyMap_neg` under instance
  transparency: `rw`/`simp` report "did not find pattern" / "unused simp argument".  Move the sign on elements
  (`hom_apply_of_comp_eq` + `congrArg`), and use `exact`/`Eq.trans`, which unify at default transparency.
- **`HasLowSurj π` cannot infer `K`** (π carries no coefficient): pin `(K := K)` at every binder.
- F₂ helper lemmas in a peer's file (`GysinFromGraded.lhSum_two_apply`, `colTwo`) silently pin a generic proof to
  `ZMod 2`: `rw` fails with "did not find pattern" on a goal that prints identically.  Grep the lemma's binder.
- **A `rw` that leaves both sides syntactically equal closes the goal.**  A trailing `rfl` then fails with
  "No goals to be solved" (FlatOf:90, probe 8).
- macOS `bash` is 3.2: no associative arrays; zsh does not word-split unquoted variables.
- zsh: an unquoted `echo ===` triggers equals-expansion and aborts the command ("== not found"); quote separators.
- `git diff origin/main -- <path>` shows a file absent from the shared index as "deleted" even when its bytes match
  main; compare `git show origin/main:<path> | md5` with `md5 -q <path>` instead.
