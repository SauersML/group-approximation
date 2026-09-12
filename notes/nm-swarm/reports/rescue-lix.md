# rescue-lix → endpoint (successor of sp-endpoint), running report, 2026-09-11

## WHERE THE 09-10 IN-FLIGHT LIX WORK WENT (every path below is on origin/main)

| what | commit | state |
|---|---|---|
| sp-* lane reports (cupone, descent, endpoint, evenside-n, lh, oddside-n, relhomotopy, thm) + tools check_general.py, descent_ext.py, descent_lemmas.py | d9a4490a7 | notes |
| KroneckerEquiv, KroneckerContractible, LIXKCount, LIXKMap, LIXKSection, LIXKGenMap, LIXKGenSection, OddPDescentWord/Shift/Complex/Clifford/Pairing, ParityPCoeffBridge, ParityPAxiomGuard, LIXLemmaSixFrameGeneric, LIXPowersAngle | 8cdb6b3fb | COMPILED (gate A) |
| the 38 pass-2 CharClass edits: ChernEulerBundle, ChernRelation, GysinFromLerayHirsch, GysinPair, GysinRanged, LerayHirsch{Bridge,ChartClassGen,Column,Degree,GradedIso,Homotopy,Induction,Natural,NaturalCoeff,ShiftTerm,Squares,TowerBridge,Transport}, MayerVietorisSequence, ProjectiveSpace{Cohomology,Computation,Ring}, Relative{Dual,Excision,HomotopyInvariance,LES,Local,SmallChains}, Thom{BridgeChartHom,BridgeNaturalHyper,BridgeNaturalSquare,ChartSquare,EulerNaturality,FibreRestriction,FieldTwo,HyperSquare,PuncturedPi,PuncturedRecursion} | dd28464fc | COMPILED (gate B, with all 277 origin importers) |
| LIXKPunctured, LIXKGenPunctured, LIXKGenSphere, LIXKRelativeMV, LIXKStepC, LIXKStepCTwo, LIXKStepCWired, LIXShapeGenericRank, LIXStepDGenData, LIXStepDGenParity, LIXStepDGenAxiomCheck, RelHomotopyPrism, RelHomotopyInvariance | 5c0663f0a + dd28464fc | COMPILED (gate B) |
| Analysis/LIXPowers{Pinch,Normalise,Homotopy,Chain,Export} | e76e62198 + 9d5cf111f + 00b07a9b9 | COMPILED (probes C2, C3) |
| CharClass/OddPTupleBd, OddPTupleSlot | e76e62198 | UNVERIFIED, RED: parked by author ("STATUS: PARKED AND RED"), duplicate `tagAt`/`tagAt_single` of the landed OddPTuple; imported by nothing |
| CharClass/OddPDescentDomino, OddPDescentValue | e76e62198 | UNVERIFIED, RED: "not yet elaborated" (sp-descent); Domino has real proof errors (argument order after `add_comm`, `Function.update_eq_self_iff` direction, unknown `eq_update_self_iff`, stuck `NeZero`, unsolved `succ` goals); Value not reached |
| CharClass/LerayHirschCover, Peel, PeelCP, PeelClosed, RankTwo, Shift (generic pass) | attic 8dc05f669 (`attic/inflight/rescue-lix/…`) | NOT compiled: generic Cover needs a coefficient-generic `bijective_lhSum_comap` (LerayHirschMV is still F₂; no K-generic concrete MV sequence). Origin's F₂ versions build green against the generic tower. |
| Palomar/LIXStrongSolution.lean, comparator-lix-strong.json, scripts/PalomarLIXStrong{Axioms,ChallengeType,SolutionType}.lean | 81a64c86f | landed (Palomar surface, pending config) |
| Palomar/LIXStrongChallenge.lean | 70f6d12ce | landed |
| lakefile.toml (two PalomarLIXStrong libs), .github/workflows/palomar-{check,comparator}.yml, scripts/check_palomar_{statement_match.sh,submission.py} | attic 8dc05f669 | verification job running (SLURM 16 cpus) |

Repairs made while rescuing (no statement changed anywhere): `Finsupp.single_eq_of_ne` argument
order + `finsetSum_apply` (OddPDescentPairing); explicit `tendsto_const_nhds (x := Complex.I)`
(LIXPowersAngle); missing import of the audited module (ParityPAxiomGuard); `sub_eq_add_neg` in
two `simpa` (LerayHirschInduction); section-variable order of `isIso_excisionOf`
(RelativeExcision); unused `all_goals simp` (RelHomotopyPrism); `include` before the docstring
(LIXKRelativeMV); `dualMapOf_quasiIso` → `relDualMapOf_quasiIso` in RelativeDual (collided with
CohomologyMayerVietoris on origin, broke 5 importers); `pullEquivOfHomotopyEquivOf K`
(LerayHirschHomotopy); structure fields elaborated in tactic blocks (RelHomotopyInvariance);
`push Not`, `le_or_gt`, `simpa [← hzdef, hz]`, dropped `← hidef`, `lt_or_gt_of_ne hjne.symm`,
four `_`-binders (LIXPowersPinch); `fun _ hy` (LIXPowersHomotopy).

## WIRING TOPS (compiled-only, not imported by the root or by another landed module)

GroupApproximation.Analysis.LIXLemmaSixFrameGeneric, GroupApproximation.CharClass.KroneckerContractible,
GroupApproximation.CharClass.LIXKGenSection, GroupApproximation.CharClass.OddPDescentPairing,
GroupApproximation.CharClass.ParityPAxiomGuard, GroupApproximation.CharClass.LIXKGenPunctured,
GroupApproximation.CharClass.LIXKRelativeMV, GroupApproximation.CharClass.LIXKStepCTwo,
GroupApproximation.CharClass.LIXKStepCWired, GroupApproximation.CharClass.LIXShapeGenericRank,
GroupApproximation.CharClass.LIXStepDGenAxiomCheck, GroupApproximation.CharClass.RelHomotopyInvariance,
GroupApproximation.Analysis.LIXPowersExport.
Do not wire: OddPTupleBd, OddPTupleSlot, OddPDescentDomino, OddPDescentValue (red), ProblemLIXStrongAssembly (unverified until its probe).

## ENDPOINT (scope from 21:20)

- `ProblemLIXStrong.lean`: docstrings corrected (text only; the family was ill-typed and unshifted).
  Agreed family `b k := fun j => CharClass.KGen.bVecK n (k - 1)`.  Attic copy cfbf8ca42; probe after
  the Palomar job.
- `ProblemLIXStrongAssembly.lean` (unverified 852a5e45a): `powersSections`, `powersSections_one`,
  `lemmaTwoHoldsForSections_powersSections_one_iff` (↔ `LIX.Gen.LemmaTwoHolds n`),
  `lemmaTwoHoldsForSections_powersSections_two_one` (theorem, from the mod-2 `CharClass.lemmaTwoHolds`),
  `exists_isSimpleRing_separable_hasK1InjPowerWitness_of_powersSections`,
  `exists_simple_separable_not_k1Inj_of_powersSections`.

## TRAPS

- zsh does not split `$VAR` word lists: pass path lists through `$(cat file)`.
- nmland's lexical scan once refused Palomar challenge holes; the lead now allows `sorry` in `Palomar/*Challenge.lean` only.
- A SLURM gate can be cancelled from outside (job 417774, 19:40 CDT, CANCELLED+ SIGTERM); the remote build leaves no summary, so no compiled evidence is written; relaunch replays the partial artifacts.
- The cs-endpoint lock was held for ~27 min by an unidentified holder (20:20–20:47 CDT); a queued job waits inside its allocation.

## 23:50 CDT: Corollary 4 discharged; ONE named input left

- `ProblemLIXStrongAssemblyCor4.lean` (COMPILED, probe 0911-234757-76086): `powersSections_eq_degreeFamily` (rfl),
  `LemmaTwoHoldsAtPowers n := ∀ p, p.Prime → p ∣ n → ∀ k, ¬ p ∣ k → LemmaTwoHoldsForSections n (powersSections n k)`,
  `lemmaTwoHoldsAtPowers_iff` (glue's per-stage form), `corollary4Powers_powersSections` (from lix-tower's
  `LIX.Gen.corollary4Powers`), `climbedPowersOutside_of_lemmaTwoHoldsAtPowers`,
  `hasK1InjPowerWitness_of_lemmaTwoHoldsAtPowers`, `exists_isSimpleRing_separable_hasK1InjPowerWitness_of_lemmaTwoHoldsAtPowers`,
  `exists_simple_separable_not_k1Inj_of_lemmaTwoHoldsAtPowers`.
- `ProblemLIXStrongAssemblyHalves.lean` (COMPILED, same probe): imports Cor4; glue names fully qualified (rank-two
  `VIdx`/`baseM`/`Vmat` in `CharClass` collide with `CharClass.Gen` under `open`); `lemmaTwoHoldsAtPowers_of_glue`,
  `exists_isSimpleRing_separable_hasK1InjPowerWitness_of_glue`.
- `Palomar/LIXStrongSolution.lean` docstrings (ff690fad2, text only, shared block untouched): the one remaining
  named proposition is `NinetyNineProblems.LemmaTwoHoldsAtPowers n`.
- Wiring tops: `ProblemLIXStrongAssemblyHalves` (reaches Cor4, Assembly, Glue, Diag).

## 09-12 WIND-DOWN: the lead stopped the LIX-stronger program (LIX strengthenings too low impact)

State at the stop check (origin/main a30e7e4ca):
- No rescue-lix probe was running and no file was in flight.  The lane overlay (Cor4, Halves) matches
  origin byte for byte, and the attic ProblemLIXStrong copy (cfbf8ca42) matches the landed module.  So
  nothing needed an NM_ATTIC or NM_UNVERIFIED landing.  Nothing was deleted.
- Per the stop order I authored no new module and started no new probe.  ProblemLIXStrongAssemblyTwo and
  ProblemLIXStrongAssemblyOddP were designed only; the design is under RESTART DESIGN below.
- The row "verification job running (SLURM 16 cpus)" in the first table is stale.  lakefile.toml,
  the workflows and the scripts landed in ad2f71c9f.  This report holds no compiled evidence for the
  Palomar libraries themselves.

### GREEN (green-record md5 = origin = shared-tree disk, checked 09-12)

| probe | module | md5 |
|---|---|---|
| 0911-215808-83196 | Manuscript/NinetyNineProblems/ProblemLIXStrong | 938bb11b3f6e3154a2fe14f27f369c49 |
| 0911-215808-83196 | Manuscript/NinetyNineProblems/ProblemLIXStrongAssembly | e8dba04452ba1ba33918fe110cc9626d |
| 0911-234757-76086 | Manuscript/NinetyNineProblems/ProblemLIXStrongAssemblyCor4 | 99893b9673d83fad9d81547f77a7c5b8 |
| 0911-234757-76086 | Manuscript/NinetyNineProblems/ProblemLIXStrongAssemblyHalves | a7025bd7a4a67ceec681189dba1b3c85 |

Earlier compiled gates (first table): gate A 8cdb6b3fb; gate B dd28464fc + 5c0663f0a; C2/C3 LIXPowers* (e76e62198,
9d5cf111f, 00b07a9b9).  Lane green records: 0911-180944-63887, 0911-191258-25403, 0911-194230-57555,
0911-201556-40659, 0911-204944-13265, 0911-215808-83196, 0911-234757-76086.

All rescue-lix landings: 8cdb6b3fb, 5c0663f0a, e76e62198, 81a64c86f, 70f6d12ce, 8dc05f669, dbad50286, 036f19c47,
20fc92c1a, f643c96ea, dd28464fc, 9d5cf111f, 00b07a9b9, 2525ed987, 852a5e45a, cfbf8ca42, ad2f71c9f, 29e95e247,
7aa5d8ba0, b082f80a6, f01a6c1f7, ff690fad2, 3c2f78cf9, c54128086.

### STAYS UNVERIFIED / RED (left in place)

- CharClass/OddPTupleBd, OddPTupleSlot: parked by their author, red, imported by nothing.
- CharClass/OddPDescentDomino, OddPDescentValue: red (proof errors listed in the first table).
- Generic CharClass/LerayHirschCover, Peel, PeelCP, PeelClosed, RankTwo, Shift: attic only (8dc05f669), never compiled.
- The Palomar comparator's third value fails by design until `LemmaTwoHoldsAtPowers` is discharged.  The comments
  in `.github/workflows/palomar-comparator.yml` and `scripts/check_palomar_submission.py` (c54128086) say exactly
  that and are still correct.

### THE ONE NAMED INPUT (ProblemLIXStrongAssemblyCor4.lean:40, compiled)

```lean
def LemmaTwoHoldsAtPowers (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → ∀ k : ℕ, ¬ p ∣ k →
    LemmaTwoHoldsForSections n (powersSections n k)
```

`exists_isSimpleRing_separable_hasK1InjPowerWitness_of_lemmaTwoHoldsAtPowers n (hn : 2 ≤ n)` consumes it and
gives `∃ (A : Type) (_ : CStarAlgebra A), Nontrivial A ∧ IsSimpleRing A ∧ TopologicalSpace.SeparableSpace A ∧
HasK1InjPowerWitness A n`, with Corollary 4 already discharged.  `lemmaTwoHoldsAtPowers_iff` (Iff.rfl) reads
it per prime as `∀ p, p.Prime → p ∣ n → ∀ k, ¬ p ∣ k → ∀ j, LIX.Gen.LemmaTwoFor n (LIX.Gen.lixDD n j)
(CharClass.KGen.bVecK n (k - 1))`.

### RESIDUAL AT p = 2 (producer on main: CharClass/LIXLemmaTwoGenTwo.lean:45, namespace CharClass.Gen)

```lean
theorem lemmaTwoFor_powers_two_lixChernOf (n : ℕ) [NeZero n] (hn : Even n) (hn2 : 2 ≤ n)
    {Y S₁ Sodd : ℕ → TopCat.{0}}
    (pY : ∀ j, KGen.lixN n (LIX.Gen.lixDD n j) ⟶ Y j)
    (q₁ : ∀ j, KGen.lixN n (LIX.Gen.lixDD n j) ⟶ S₁ j)
    (qodd : ∀ j, KGen.lixN n (LIX.Gen.lixDD n j) ⟶ Sodd j)
    (hC : Wu.CartanTotal)
    (hS₁ : ∀ j, HasSphereCohomology (S₁ j) 1)
    (hSodd : ∀ j, HasSphereCohomology (Sodd j) (2 * n + 1))
    (σ₁ : ∀ j, Hmod2 (S₁ j) 1) (σodd : ∀ j, Hmod2 (Sodd j) (2 * n + 1))
    (data : ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ m, IsCornerUnitary (Vmat n m) (G m)) →
      WuStepDData n (LIX.Gen.lixDD n j) (pY j) (q₁ j) (qodd j) (σ₁ j) (σodd j)
        (KGen.lixChernOf n (KGen.lixChern n (LIX.Gen.lixDD n j))
          (mappingTorus (Vmat n) G circHoriz circHeight)))
    (hloc : ∀ (e : ℕ), Odd e → ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ)
      (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat n m) (G m))
      (hGe : ∀ m, G m *ᵥ Sum.elim (KGen.aVecK n m) 0 = Sum.elim (KGen.bVecK n (e - 1) m) 0),
      KGen.KZeroLocalData n (e - 1) (LIX.Gen.lixDD n j) hGc hGu hGe) :
    ∀ k : ℕ, ¬ 2 ∣ k → ∀ j : ℕ,
      LIX.Gen.LemmaTwoFor n (LIX.Gen.lixDD n j) (KGen.bVecK n (k - 1))
```

- Discharged: `hC` is `CharClass.Wu.cartanTotal` (ParityEvenTransport.lean:284, a theorem).  `2 ∣ n` and `2 ≤ n`
  give `Even n` and `NeZero n`, and `¬ 2 ∣ k` gives `Odd k` for `hloc`.
- Open, inputs 1 and 2: `hloc`, i.e. `KGen.KZeroLocalData` (CharClass/LIXKGenStepCHalfTop.lean:51):
  ```lean
  def KZeroLocalData (n k : ℕ) (dd : Fin ℓ → ℕ)
      {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
      (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
      (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) : Prop :=
    ∃ xloc : ∀ i : Fin (k + 1), relCohomology (ZMod 2) (lixN n dd)
        ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd),
      LocalSplit (fun i => lixKRho n k dd i (2 * lixRank n dd))
          ((lixKSRel n k hGc hGu hGe (2 * lixRank n dd)).hom (lixThomClassTerm n hGc hGu)) xloc ∧
        ∀ i, xloc i ≠ 0
  ```
  and `data`, i.e. `Gen.WuStepDData n dd p q₁ qodd σ₁ σodd γ` (CharClass/LIXStepDGenData.lean:80), fields
  `a b : ℕ → TotalH Y`, `gen : Fin ℓ → TotalH Y`, `tx_inj`, `gamma_eq`, `sq_b`, `split : Wu.HasSplitting N γ`,
  `slice : ∀ q, a q = (sliceClass Finset.univ gen dd).coeff q`; together with the spaces `Y S₁ Sodd`, the maps
  `pY q₁ qodd`, `hS₁ hSodd` and the classes `σ₁ σodd`.

### RESIDUAL AT A PRIME p (producer on main: CharClass/LIXStepDGenReal.lean:335, namespace CharClass.Gen)

```lean
theorem lemmaTwoFor_powers_of_stepC_realModP (n p : ℕ) (hp : p.Prime) (hn : 1 ≤ n)
    (hpn : p ∣ n) {K : Type} [CommRing K] {N Y S₁ Sodd : ℕ → TopCat.{0}}
    {pY : ∀ j, N j ⟶ Y j} {q₁ : ∀ j, N j ⟶ S₁ j} {qodd : ∀ j, N j ⟶ Sodd j}
    {σ₁ : ∀ j, TotalPieceOf K (S₁ j) 1} {σodd : ∀ j, TotalPieceOf K (Sodd j) (2 * n + 1)}
    (T : ∀ j, RealTorusModP n K (pY j) (q₁ j) (qodd j) (σ₁ j) (σodd j))
    [∀ j, ExpChar (evenPart K (Y j)) p]
    (γfun : ∀ j : ℕ, (↥sphereOne × baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
          (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j)) ℂ) → ℕ → TotalHOf K (N j))
    (data : ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ m, IsCornerUnitary (Vmat n m) (G m)) →
      RealBundleModP p (LIX.Gen.lixDD n j) (T j)
        (γfun j (mappingTorus (Vmat n) G circHoriz circHeight)))
    (hC : ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
      StepCHalf n (LIX.Gen.lixDD n j) (KGen.bVecK n (k - 1))
        (fun W => γfun j W ((∑ i, LIX.Gen.lixDD n j i) + (n + 1)))) :
    ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
      LIX.Gen.LemmaTwoFor n (LIX.Gen.lixDD n j) (KGen.bVecK n (k - 1))
```

- Open: `T`, i.e. `Gen.RealTorusModP n K pY q₁ qodd σ₁ σodd` (LIXStepDGenReal.lean:130), fields `circle_two`, `z_inj`,
  `PN`, `PY`, `PN_even`, `PY_even`, `PN_zero`, `cartan`, `natural`, `P_t`, `P_x`, `PY_unstable`.
- Open: `data`, i.e. `Gen.RealBundleModP p dd T γ` (LIXStepDGenReal.lean:191), fields `γ_even`, `a`, `b`, `a_even`, `b_even`,
  `γ_eq`, `b_low`, `b_deg`, `gen`, `slice`, `c`, `c_isUnit`, `wu` (the diagonal Wu relation with a unit leading
  coefficient, in the even part of `N`).
- Open: the instance `[∀ j, ExpChar (evenPart K (Y j)) p]`.
- Open: `hC`, meant to come from `KGen.stepCHalf_of_kZeroStepCDataOf` (CharClass/LIXKGenOfStepC.lean:152):
  ```lean
  theorem stepCHalf_of_kZeroStepCDataOf (K : Type) [Field K] (n k : ℕ)
      (hk : ((k + 1 : ℕ) : K) ≠ 0) (dd : Fin ℓ → ℕ) (hdd : ∀ j, 0 < dd j)
      (topClass : (↥sphereOne × Gen.baseM n dd →
        Matrix (Gen.VIdx n dd ⊕ Gen.VIdx n dd) (Gen.VIdx n dd ⊕ Gen.VIdx n dd) ℂ) →
          Hmod K (lixN n dd) (2 * lixRank n dd))
      (hdata : ∀ (G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ)
        (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
        (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0),
        KZeroStepCDataOf K n k dd hGc hGu hGe
          (topClass (mappingTorus (Gen.Vmat n) G circHoriz circHeight))) :
      Gen.StepCHalf n dd (bVecK n k) topClass
  ```
  with the open data `KGen.KZeroStepCDataOf` (LIXKGenOfStepC.lean:134):
  ```lean
  def KZeroStepCDataOf (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ)
      {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
      (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
      (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
      (gamma : Hmod K (lixN n dd) (2 * lixRank n dd)) : Prop :=
    ∃ (u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
        (2 * lixRank n dd))
      (xloc : ∀ i : Fin (k + 1), relCohomology K (lixN n dd)
        ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd))
      (c : Hmod K (lixN n dd) (2 * lixRank n dd)),
      LocalSplit (fun i => lixKRhoOf K n k dd i (2 * lixRank n dd))
          ((lixKSRelOf K n k hGc hGu hGe (2 * lixRank n dd)).hom u) xloc ∧
        (∀ i, xloc i ≠ 0) ∧
        LocalClassesAgree (fun i => lixKJlocOf K n k dd i (2 * lixRank n dd)) xloc c ∧
        (lixJEOf K n hGc hGu (2 * lixRank n dd)).hom u
          = (lixPiStarOf K n hGc hGu (2 * lixRank n dd)).hom gamma
  ```
- The seam (not written): `hC` takes values in `TotalHOf K (N j)` at the index `(∑ i, lixDD n j i) + (n + 1)`, while
  `stepCHalf_of_kZeroStepCDataOf` takes values in `Hmod K (lixN n dd) (2 * lixRank n dd)`.  Joining them needs
  `N j = KGen.lixN n (lixDD n j)`, a link hypothesis `htop : γfun j W top = TotalHOf.of K _ (2 * lixRank n _) (topClass j W)`,
  and `CharClass.TotalHOf.of_eq_zero_iff` to move `≠ 0` across.  It also needs a field `K` with `CharP K p`, so that
  `((k - 1 + 1 : ℕ) : K) ≠ 0` for `p ∤ k` (note `k ≠ 0`), and positivity `0 < lixDD n j i` for `hdd`, which was not checked on main.

### RESTART DESIGN (nothing authored)

- `ProblemLIXStrongAssemblyTwo` (imports Halves + LIXLemmaTwoGenTwo + ParityEvenTransport): the adapters
  `odd_of_not_two_dvd` and `neZero_of_two_le`, and `eq_two_of_prime_dvd_two_pow`.  Named Props `LemmaTwoPowersTwoLocalData n`
  (the `hloc` binder) and `LemmaTwoPowersTwoWuData n` (the spaces, maps, sphere data and `data`, existentially bundled).  Then
  `lemmaTwoHoldsForSections_powersSections_two`, and `lemmaTwoHoldsAtPowers_two_pow (m) (hm : 1 ≤ m)`, which reads
  `LemmaTwoHoldsAtPowers (2 ^ m)` from the two named Props, with `hC := Wu.cartanTotal`.
- `ProblemLIXStrongAssemblyOddP`: `stepCHalf_of_eq_zero_imp` (StepCHalf along a map reflecting zero), and the per-prime
  `lemmaTwoHoldsForSections_powersSections_of_kZeroStepC_realModP` (field `K`, `CharP K p`, `htop`, `hkz`).  Named Prop
  `LemmaTwoPowersModPData n p`.  Then `lemmaTwoHoldsAtPowers_of_modPData` and `lemmaTwoHoldsAtPowers_of_twoData_of_modPData`.

### TRAP (09-12)

- In the shared tree, `git diff origin/main` lists `Palomar/LIXStrongSolution.lean` as deleted because the file is missing from
  the shared index.  The on-disk bytes equal origin (md5 8cd2b0af3d0bc3693db2b49afd160ee3, landed ff690fad2).  Never land it from
  the shared tree on the strength of that diff.
