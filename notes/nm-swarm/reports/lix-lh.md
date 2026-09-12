# Lane `lix-lh` — the coefficient parameter through Leray–Hirsch, Chern, projective space, the chart tower, and Mayer–Vietoris

Successor of `sp-lh` (`notes/lix-stronger-lane-reports/sp-lh.md`, read in full).  Clone `nm-b` (shared; lix-i
was never created).  Owns (`nm/LIX_LANES.md` + lead rulings 09-11 ~21:40): `CharClass/LerayHirsch*`, `Chern*`
(incl. `ChernTotalRing`), `Projective*`, `CohomologyChart*`, and `MayerVietoris*` + `CohomologyDelta*`.
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
| `4252ac767` | `LerayHirschMVOf` (bijective_lhSum_comapOf, LHOver_supOf) | UNVERIFIED |
| `4ad91fa8a` | PullOf, DeltaLiftOf/SpecOf/CupOf/NaturalOf, DisjointOf, Cover/RankTwo/Shift over K, Tower/TowerTop/Freeness | COMPILED |
| (unverified) | `ChernClassesOf` | UNVERIFIED |
| attics | e8c44817b, the PullOf/RankTwo fixes, ColumnPack over K | ATTIC |

## GREEN (with job counts)

- probe `0911-214535-67476` (nm-b, base d02e576c7, SLURM acn29): 9 files COMPILED.
- probe `0911-221318-90775` (nm-b, base 93e1d2992, acn112 88-95): 20 files COMPILED; LerayHirschChart, ChartTwo,
  Finite, Product built against the generic Cover/RankTwo.

## AUTHORED, UNVERIFIED (running probe)

| file | change |
|---|---|
| `LerayHirschPeel` | K generic; `HasLowSurj (K := K) π` pin at the one binder |
| `LerayHirschPeelCP`, `PeelClosed` | `HasLowSurj (K := ZMod 2)` pins (sp-lh) |
| `LerayHirschColumnPack` | `HasFreeTuple`, `bijective_lhSum_of_freeTuple` over K |
| `LerayHirschMVOf` | the Mayer–Vietoris step and the two-set step over a field |
| `ChernClassesOf` | `LerayHirschDataOf K` with `mul_comm_base`/`map_central` data; Chern classes from `ChernRelation` |

## Design decisions

- **The Mayer–Vietoris sign over K.**  The chain map is `biprod.lift ι (−ι')`, so the composite through the middle
  term on the `V` side is **minus** the restriction.  `mvResWVOf` is defined as its negative (the honest
  restriction); `exact_sum` is agreement of the honest restrictions; the cochain data of `mvDeltaOf_spec` is
  `α_U| − α_V| = α` (F₂: `+`).
- **Additive `Of` twins, F₂ names untouched.**  Every `MayerVietoris*Of`, `CohomologyDelta*Of`, `LerayHirschMVOf`,
  `ChernClassesOf`, `ChernTotalRingOf` is a new module, so no F₂ consumer rebuilds.  `LHOver_sup` stays F₂;
  `LHOver_supOf K` is the generic twin.
- **Chern classes over K take commutativity as data.**  `TotalHOf K X` is only a `DirectSum.GRing`; the base ring
  commutativity and the centrality of pulled-back classes are fields of `LerayHirschDataOf`, produced from even
  concentration (lix-cupone's `mul_comm_of_isEven`).  No `mul_comm` on `TotalHOf`, ever.

## NEEDS

- none blocking.  lix-cupone: `TotalHOf.IsEven` / `mul_comm_of_isEven` against `ChernTotalRingOf` for the
  `LerayHirschDataOf` producers.

## TRAPS

- **A `-` inside a composite whose middle object is spelled `(mvCoSCOf K U V hUV).X₃`** (a def's structure
  projection) does not match `Preadditive.neg_comp` / `HomologicalComplex.homologyMap_neg` under instance
  transparency: `rw`/`simp` report "did not find pattern" / "unused simp argument".  Move the sign on elements
  (`hom_apply_of_comp_eq` + `congrArg`), and use `exact`/`Eq.trans`, which unify at default transparency.
- **`HasLowSurj π` cannot infer `K`** (π carries no coefficient): pin `(K := K)` at every binder.
- F₂ helper lemmas in a peer's file (`GysinFromGraded.lhSum_two_apply`, `colTwo`) silently pin a generic proof to
  `ZMod 2`: `rw` fails with "did not find pattern" on a goal that prints identically.  Grep the lemma's binder.
- macOS `bash` is 3.2: no associative arrays; zsh does not word-split unquoted variables.
