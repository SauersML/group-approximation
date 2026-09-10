# sp-tower — the C*-side tower, generic in the rank `n`

Lane of `notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.1.  Clone `cs-stages` (cores 88-95).
Owns `GroupApproximation/Analysis/LIX*.lean` and their closure under `Analysis/`.

## Strategy: (a) generalise in place, `STW59.Gen.*` generic, old names as `n = 2` abbrevs

The launch message offered (a) generalise in place with `n` a parameter, keeping the
existing `STW59.*` names as `n = 2` specialisations, or (b) a parallel namespace.  **(a),
realised as a nested namespace.**  Reasons, in the order they decided it:

1. **`LIXBlockProjections` has 125 transitive importers**, ~100 of them `CharClass` files
   owned by other lanes, plus `Manuscript/NinetyNineProblems/ProblemLIX` and
   `Palomar/LIXSolution`.  The path is `CharClass/* → Analysis/LIXLemmaTwoProp → Analysis/
   LIXBlockProjections`, through `LIX.lixDD` (121 uses in `CharClass`).  Any change to the
   *arity* of `STW59.stageRank` etc. would edit files this lane does not own.  So the old
   names must survive at their old arity and old meaning.
2. **No `CharClass`, `Palomar` or `Manuscript` file uses a term-level name from the
   tower.**  Outside `Analysis/`, the only `STW59.*` names used are the already-generic
   model names (`unitVectors`, `cpSet`, `CP`, `taut`, `matEval`, `exists_natCast_trace`,
   `eq_rankOneProj_of_trace_one`, `isCompact_unitVectors`, `exists_rankOneProj_absorbed`,
   `colAt`, `exists_continuous_corner_unitary_apply_eq`).  `STW59.Fproj` and
   `STW59.sphereFive` appear only in `CharClass` **docstrings**.  So the whole coupling is
   through `lixDD`, i.e. through `stageRank`.
3. **The generic definition can be chosen so the `n = 2` instance is *definitionally* the
   old one.**  `Gen.stageRank n i := 2 ^ i * n`, **not** `n * 2 ^ i`: `Nat.pow` recurses on
   the exponent, so `2 ^ i * 2` reduces to the same term as `2 ^ (i + 1)`.  Hence
   `LIXLemmaTwoProp.lixDD_apply : lixDD j i = 2 ^ ((i : ℕ) + 1) := rfl` still holds by
   `rfl`, and the hundred `CharClass` modules downstream of it see no change at all.
4. Strategy (b) would duplicate ~500 lines of proof and leave two towers for the
   duplicate scan to trip over.  (a) replaces those 500 lines with ~300 lines of
   delegation (`:= Gen.<same name> 2`), each of which is a defeq check rather than a proof.

The generic layer is the nested namespace `GroupApproximation.STW59.Gen`; the `n = 2`
layer keeps every old name in `GroupApproximation.STW59` with its old arity, its old
`@[simp]` attributes, and its old `def`/`abbrev` keyword (so that downstream `rw [foo]`
against a definition's equation lemma behaves as before — a grep found only one such use
in the whole closure, `newBlock` inside this file itself).

## The inventory: every declaration that hard-coded `2`

`Analysis/LIXProjectiveSpaceModel.lean` — **already fully generic in `d`.  No change.**
`CP d`, `unitVectors n`, `rankOneProj`, `taut`, `tautMat`, `matEval`, `exists_frame`'s
inputs: all parametric.  This was the pleasant surprise of the reading pass.

`Analysis/LIXBlockProjections.lean` — lines 1-415 (block lemmas, `constMat`, `pullMat`,
reindexing, `exists_frame`, `eq_zero_of_trace_conjTranspose_mul_self`) and lines 972-1015
(`isLocallyConstant_trace`) are n-free.  Everything between them hard-coded `n = 2`:

| declaration | hard-coding | generic form |
|---|---|---|
| `sphereFour` | `EuclideanSpace ℝ (Fin 5)` | `Gen.sphereEven n`, ambient `Fin (2n+1)` |
| `sphereFive` | `unitVectors (Fin 3)` | `Gen.sphereOdd n = unitVectors (Fin (n+1))` |
| `stageRank i` | `2 ^ (i+1)` | `Gen.stageRank n i = 2 ^ i * n` |
| `stageRank_zero` | `= 2` | `= n` |
| `stageRank_pos` | unconditional | needs `[NeZero n]` |
| `hrank_add_two` | `hrank i + 2` | `Gen.hrank_add_rank : hrank n i + n = stageRank n i` |
| `realDim_baseX` | `4 + 2·hrank` | `2n + 2·hrank n i = 2·stageRank n i` |
| `baseY`, `baseX`, `basePr`, `baseProj` | via `stageRank`, `sphereFour` | `Gen.* n` |
| `NIdx`, `HIdx` | via `stageRank` | `Gen.* n` |
| `EIdx i` | `Fin 2 ⊕ HIdx i` | `Gen.EIdx n i = Fin n ⊕ Gen.HIdx n i` |
| `eIdxSucc` | `Equiv.sumAssoc (Fin 2) …` | `Equiv.sumAssoc (Fin n) …` |
| `Eproj i` | `fromBlocks (1 : M_{Fin 2}) 0 0 (Hproj i)` | `(1 : M_{Fin n})` |
| `Eproj_ne_zero` | unconditional | needs `[NeZero n]` |
| `blockUnitary i u` | `u : Matrix (Fin 2) (Fin 2) …` | `u : Matrix (Fin n) (Fin n) …` |
| `hopfCol`, `hopfProj`, `Fproj` | `Fin 3` | `Fin (n+1)` over `Gen.sphereOdd n` |
| `trace_Fproj` | `= 2` | `= n` |
| `murrayVonNeumannEquiv_Fproj` | `𝟏³` | `𝟏^{n+1}` |

`lineProj`, `newLine`, `newBlock`, `Hproj`, their `Y`-level twins and every trace lemma
hard-code `2` only *through* `stageRank`, and generalise by threading `n`.

`Analysis/LIXConnectingMapPoints.lean` — `baseXinf`, `truncate`, `infDenseSeq`,
`stagePoint` and the density lemmas hard-code `2` only through `sphereFour`/`stageRank`.
`Analysis/LIXStageAlgebra.lean` — the `Bridge` section is already generic in `(X, ι)`;
`stageProj`, `StageAlgebra`, `stageEval` and the nontriviality argument thread `n`.
`Analysis/LIXConnectingMap.lean`, `LIXCornerAlgebra`, `LIXSimplicity`, `LIXLimit*`,
`SequentialGroupColimit`, `CStarSimple`, `CStarKOne*`, `CStarUnitaryComponent` — **already
generic**: they are stated over `stageRank i`, `EIdx i`, `baseX i`, `Eproj i`, `stagePoint
i` or over an abstract tower `A : ℕ → Type`, and thread `n` mechanically.
`Analysis/LIXClutching.lean` — **already generic** in the index type `n : Type*`, the
equatorial normed space `E` and the base `X`.  No change needed at any rank.
`Analysis/LIXGeneratorUnitary.lean` — the Householder/frame layer (`rk1`, `reflMat`,
`transportRot`, `frameRot`, `frameNorth`, `frameSouth`, `seamGen`, `poleRotation`,
`contractNorth/South`, `seamPath`) is **already generic in `n : Type*`**; only the final
instantiation section (`e3 : Fin 3 → ℂ`, `genU x = seamGen e3 x`) hard-codes `Fin 3`.  The
`SU(2)`/`hopfSuspension` block at the top is the `n = 2` quaternionic closed formula and is
**used by nothing** (grep: no occurrence of `hopfSuspension`, `su2`, `SquareNullHomotopy`,
`StableNullHomotopy` outside that file), so the seam generator at general `n` is
`seamGen (eLast n) x` with `eLast n = Pi.single (Fin.last n) 1`, and that block is dead
weight for the generalisation.

## GREEN

Every claim below is a `✔ … Built <module> (Ns)` line, never a `Replayed` line, from a
clone whose copy of the file was verified `md5sum`-identical to the local one — the warm
script made that check necessary (see TRAPS).

* `GroupApproximation.Analysis.LIXBlockProjections` — **PROBE GREEN, 2966 jobs**
  (cs-stages, 2026-09-10).  Generic `STW59.Gen` layer (spheres, `stageRank`, `hrank`,
  `baseX/Y`, `basePr`, index types, `lineProj`/`newLine`/`newBlock`, `Hproj`/`Eproj` with
  traces and `Eproj_succ`, the `Y`-level twins, `blockUnitary`, `hopfCol`/`hopfProj`/
  `Fproj` with `F ⊕ 𝟏 ≅ 𝟏^{n+1}`) plus the `n = 2` compatibility layer.
* Baseline before the change: `LIXProjectiveSpaceModel + LIXBlockProjections +
  LIXStageAlgebra` PROBE GREEN, 2976 jobs.
* In the probe of the seven closure leaves, every `Analysis/` module rebuilt green —
  `LIXProjectiveSpaceModel`, `LIXClutching`, `LIXSimplicity`, `LIXLimitTower`,
  `LIXLimitCompletion`, `LIXFiniteStageNullHomotopy`, `LIXEndpointStatement`,
  `CStarSimple`, `CStarKOne`, `CStarKOneInjectivityCriterion`,
  `CStarUnitaryComponent`, `CStarMatrixBlockInclusion` — before the run died in
  `CharClass` on a peer's half-synced edit (see TRAPS).  No error anywhere in
  `Analysis/`.  **Read this as corroboration, not as the gate**: the warm script
  overwrote that clone's sources partway through the run, so only the modules built
  before the overwrite are certainly mine.  The gate is the dedicated
  `CharClass`-free probe listed under AUTHORED, UNVERIFIED.

* **The C*-side gate, 2026-09-10 10:25 (cs-stages).**  Rebuilt from my sources, verified
  `md5sum`-identical in the clone, with every one of the three a real `Built` line:

  | module | |
  |---|---|
  | `Analysis.LIXBlockProjections` | `✔ [3015/3040] Built (41s)` |
  | `Analysis.LIXConnectingMapPoints` | `✔ [3017/3040] Built (32s)` |
  | `Analysis.LIXStageAlgebra` | `✔ [3019/3040] Built (39s)` |

  and with them the whole `Analysis/` closure: `LIXProjectiveSpaceModel`, `LIXCornerAlgebra`,
  `LIXConnectingMap`, `LIXConnectingMapFullness`, `LIXStageAlgebraSeparable`,
  `LIXLimitTower`, `LIXLimitCompletion`, `LIXLimitWitness`, `LIXLimitMatrixFlatten`,
  `LIXLimitMatrixTransport`, `LIXLimitSectionMatrix`, `LIXSimplicity`,
  `LIXSimplicityInstance`, `LIXGeneratorUnitary`, `LIXLemmaSixGenerator`,
  `LIXLemmaSixShape`, `LIXLemmaSixDiagPath`, `LIXLemmaSixClimb`, `LIXLemmaSixSouth`,
  `LIXEndpointStatement`, `LIXFiniteStageNullHomotopy`, `SequentialGroupColimit`,
  `CStarSimple`, `CStarKOne`, `CStarKOneInjectivityCriterion`, `CStarUnitaryComponent`,
  `CStarMatrixBlockInclusion`, `KTheory.MatrixProjection`.  The `#audit_axioms` lines that
  ran in that closure all printed exactly `[propext, Classical.choice, Quot.sound]`.

  **One genuine failure, found and fixed:** `LIXLemmaSixStageZero.lean:38` did
  `rw [STW59.stageProj, Eproj_zero_eq_one, …]`, and `stageProj` is now an `abbrev`, so its
  equation lemma unfolds to `Gen.stageProj 2 0` and the next rewrite loses its pattern.
  Fixed by publishing `STW59.stageProj_def` and `STW59.stageEval_def` (`… = rfl`) and
  pointing that `rw`, and the one other unfold-by-name in the closure
  (`LIXLemmaSixCor4.lean:133`, `rw [STW59.stageEval, …]`), at them.  The confirming
  re-probe is queued behind `warm4.sh`, which wiped the clone's whole olean tree
  (`rm -rf .lake/build/lib/lean/GroupApproximation`) and is `cp -a`-ing the node tree's
  back in, so it will be a full rebuild.  `warm4.sh` does now take `laneprobe.lock`, so
  the probe will at least not be torn.

## AUTHORED, UNVERIFIED

Probes are held by the lead while the clones are converted to real copies; everything in
this section is in the shared tree and waits for the gate.

* The `stageProj_def` / `stageEval_def` fix and its two call sites
  (`LIXLemmaSixStageZero:38`, `LIXLemmaSixCor4:133`).  A probe holding **exactly** this
  state, and nothing later, is queued on cs-stages — the clone's `LIXConnectingMap.lean`
  is still `731ccc82…`, the pre-generalisation file, so its verdict is about deliverable 1
  alone.
* `Analysis/LIXGeneratorUnitary.lean` — the instantiation section generic in `n`:
  `Gen.ePole n = Pi.single (Fin.last n) 1`, `Gen.genU n x = seamGen (ePole n) x`, both
  hemisphere trivialisations of `F`, and `diag(u,1) ≃ 1` in `U(n+1)` through
  `seamPath (ePole n)`.  `e3` and `genU` keep their own one-line definitions with
  `e3_eq_ePole` / `genU_eq` as `rfl` bridges, because two consumers unfold those names
  with `rw`/`simp`; every *theorem* in the `n = 2` section is now the generic one at `2`.
  The `SU(2)`/`hopfSuspension` block stays in place as documentation of the `n = 2`
  generator.  No declaration removed.
* `Analysis/LIXConnectingMap.lean` — the connecting map generic in `n`:
  `Gen.stageFrame n i`, `Gen.compressMat n i` with multiplicativity on the corner,
  `Gen.connectMatrix`, `Gen.connectFun`, `Gen.connect` and its injectivity, with the
  `n = 2` layer delegating.  One new lemma, `STW59.connectMatrix_def`, because
  `LIXLemmaSixClimb:58` unfolds `connectMatrix` by name; that `rw` now names it.  No
  declaration removed.
* `Analysis/LIXStageAlgebra.lean`, one addition —
  `Gen.instCStarAlgebraStageAlgebraPi (n) : ∀ i, CStarAlgebra (Gen.StageAlgebra n i)`, the
  pi-shaped instance `CStarTower` binds.  It is a **data** class, so the `n = 2` one is
  left as `fun _ => inferInstance` and now resolves *through* the generic one, which makes
  the two definitionally the same term rather than an independent second instance.
* `Analysis/LIXStageAlgebraSeparable.lean` — `Gen.instSecondCountableBaseX`,
  `Gen.instSeparableSpaceStageAlgebra`, `Gen.instSeparableSpaceStageAlgebraPi` at general
  `n`.  All `Prop` classes, so the `n = 2` ones stay beside them.
* `Analysis/LIXLimitAlgebra.lean` — **the tower and the limit at general `n`**:
  `Gen.lixTower n`, `Gen.LIXLimit n`, `Gen.lixIota`, `dense_iUnion_lixStage`,
  `lixLimit_hasK1InjWitness` and `lixLimit_separableSpace`, with the `n = 2` layer
  delegating and every old name kept.  The C*-algebra structure of the limit is
  unconditional; only `Nontrivial (Gen.LIXLimit n)` carries `[NeZero n]`, and it is
  checked by `example`.  The `2` in `CStarMat 2 (…)` is the `K₁` witness's matrix size and
  stays `2` at every rank — the docstring now says so, because it is one character away
  from reading as the rank.  Six `#audit_axioms` gates, three generic and three at `n = 2`.

* `Analysis/LIXConnectingMapFullness.lean`, `…Sum.lean`, `…Tower.lean` — the whole
  stagewise-fullness chain generic in `n`: `Gen.compressMat_eq_zero_iff`,
  `Gen.stageEval_connect_ne_zero`, `Gen.sum_single_conj` (the matrix-unit averaging),
  `Gen.isFull_of_forall_stageEval_ne_zero`, `Gen.isFull_connect_of_stageEval_ne_zero`,
  `Gen.stageEval_climb_ne_zero` and `Gen.isFull_climb_of_ne_zero`.  `sum_single_diag` and
  `ofFunctionMatrix_sum` are stated for an arbitrary index type, so they do **not** move
  into `Gen`; they are hoisted above it because `Gen.sum_single_conj` consumes the first.
* `Analysis/LIXLimitSimple.lean` — `Gen.lixLimit_isSimpleCStar_of_full n` and
  `Gen.lixLimit_isSimpleCStar n`, i.e. **the counterexample algebra is simple at every
  rank**, with `#audit_closed_axioms` on both the generic theorem and the `n = 2` one.
  `LIXSimplicityInstance` needed no change: it was already abstract over `A : ℕ → Type u`.

Every one of these keeps the old name with its old signature and removes no declaration;
the diff is additive plus delegation.  Backups of the pre-edit files are in this session's
scratchpad, so any single file can be reverted to its green form in one copy if the gate
localises a failure there.
* `Analysis/LIXStageAlgebra.lean`'s `CStarAlgebra` *pi*-instance
  `∀ n, CStarAlgebra (StageAlgebra n)` is deliberately left only at `n = 2`: a second,
  generic one would be a data-class diamond, and the tower/limit lane is the next
  deliverable, where it belongs.
* `Analysis/LIXGeneratorUnitary.lean` generic instantiation, drafted in this session's
  scratchpad (`sp/genu_gen.lean`) and **not yet installed**: `Gen.ePole n =
  Pi.single (Fin.last n) 1`, `Gen.genU n x = seamGen (ePole n) x`, both hemisphere
  trivialisations, `diag(u,1) ≃ 1` in `U(n+1)` via `seamPath (ePole n)`.  The whole
  Householder/frame engine above it is already generic, so this is a 150-line
  transcription with `Fin 3 ↦ Fin (n+1)` and `x 2 ↦ x (Fin.last n)`.

## The fresh-clone gate, 2026-09-10 11:29 (cs-stages, 9357 jobs)

Run on the lead's rebuilt clone (real copies, no hard links), with **my fourteen modules'
`.olean`/`.ilean`/`.trace`/`.c` deleted first**, so every line below is a genuine compile.
All fourteen clone sources were `md5sum`-verified identical to my working copies before it
started.

Green, with times: `LIXBlockProjections` 67s, `LIXGeneratorUnitary` 32s,
`LIXConnectingMapPoints` 35s, `LIXStageAlgebra` 51s, `LIXConnectingMap` 44s,
`LIXStageAlgebraSeparable` 42s, `LIXLimitAlgebra` 39s, `LIXConnectingMapFullness` 39s,
`LIXLemmaSixStageZero`, `LIXLemmaSixClimb` 41s, and the surrounding LemmaSix chain
(`HIdx` 96s, `Generator` 38s, `Shape` 65s, `Diag` 39s, `Glue` 40s, `Equator` 38s,
`LimitSectionMatrix` 42s).

**The three defeq claims I could not check by reading all held**: `Fin.last 2` against the
numeral `2` in `Fin 3` (`LIXGeneratorUnitary` green), the `CStarTower` instance argument
agreeing between `STW59.StageAlgebra` and `Gen.StageAlgebra 2` (`LIXLimitAlgebra` green),
and `variable (n : ℕ)` putting `n` first in the scripted rewrites (`LIXConnectingMap` and
`LIXConnectingMapFullness` green).

**Two genuine misses of mine, both fixed:**

1. `LIXLemmaSixDiagEnd:93` left `(Gen.stageProj 2 0) w (inl a) (inl b) = if a = b then 1
   else 0` unsolved: its `simp` list named `STW59.stageProj`, whose equation lemma now
   unfolds to the generic name, so `Eproj_zero_eq_one` lost its pattern.  Fixed by naming
   `stageProj_def`.  My earlier grep missed it because that `simp` list spans four lines
   and I had matched only single-line brackets; the scan is now a bracket-balancing parser
   over every `rw`/`simp`/`unfold` in the repository, and this was the last such site.
2. `LIXConnectingMapFullnessSum:122,129` passed `isStarProjection_stageProj j` where the
   generic form needs `… n j` — that name was absent from the scripted rewrite's
   substitution list.  Fixed, and the class of mistake is now closed by a checker that
   extracts every `Gen` declaration whose first argument is `n` (162 of them) and flags
   applications inside `Gen` blocks not followed by `n`.  It found exactly these two.

Blocked, not failed: `LIXConnectingMapFullnessSum`, `…Tower` and `LIXLimitSimple` sat
behind the miss above, and `LIXLemmaSixCor4` cannot build while `CharClass` is red.
`CharClass` is at eighteen errors, all `sp-coeff`'s in-flight coefficient parameter
(`CoeffField:53` fails to synthesize an instance; `CohomologyAssoc:93,:103` follow).
**Nothing of mine is implicated there**, so the seven-importer gate cannot go green today
and the narrow CharClass-free gate is the strongest verdict available.

## PLAN for the remaining layers

Scoped by reading, in dependency order.  Every one is the same recipe — a `Gen` namespace
with `n` first, the old names kept as the `n = 2` specialisation — and for each I record
the only thing that is *not* mechanical.

1. **`LIXStageAlgebra`, one addition.**  `Gen.instCStarAlgebraStageAlgebraPi (n) :
   ∀ i, CStarAlgebra (Gen.StageAlgebra n i)`.  It has to be pi-shaped because
   `CStarTower` binds `[∀ i, CStarAlgebra (A i)]` and instance search does not assemble
   that from the per-stage instance.  Not mechanical: this is a **data** class, so the
   `n = 2` one must not be an independent second instance; it stays `fun _ => inferInstance`
   and therefore resolves *through* the generic one.
2. **`LIXStageAlgebraSeparable`.**  `instSecondCountableBaseX`,
   `instSeparableSpaceStageAlgebra`, `instSeparableSpaceStageAlgebraPi` at general `n`.
   All `Prop` classes, so duplicates are harmless.  Purely mechanical.
3. **`LIXConnectingMapFullness`, `…Sum`, `…Tower`.**  Stated throughout over `EIdx i`,
   `baseX i`, `StageAlgebra i`, `stageEval`, `connect`, so the same scripted `n`-insertion
   that did `LIXConnectingMap` applies.  `…Tower`'s `isFull_climb_of_ne_zero` is already
   abstract over the tower `T`, so only its `StageAlgebra` argument moves.
4. **`LIXLimitAlgebra`.**  `Gen.lixTower n := CStarTower.ofInjective (STW59.Gen.connect n)
   (STW59.Gen.connect_injective n)`, `Gen.LIXLimit n`, `lixIota`, the witness theorem and
   separability.  Not mechanical: `Nontrivial (Gen.LIXLimit n)` needs
   `Gen.instNontrivialStageAlgebra`, which carries `[NeZero n]`, so `Gen.LIXLimit`'s
   nontriviality is `[NeZero n]`-conditional while the algebra itself is not.
5. **`LIXLimitSimple`.**  Two delegating theorems once (3) and (4) are generic.
   `LIXSimplicityInstance` needs **no change**: it is already abstract over
   `A : ℕ → Type u`.
6. **The Corollary-4 chain** (`LIXLemmaSixHIdx/Field/Compare/Cor4`) stays abstract over
   the `LemmaTwoHolds` `Prop`, with the seam left where the `k`-index will enter:
   `LemmaTwoHolds` becomes `LemmaTwoHolds n p k` and `climb_genUnitary_notMem` becomes
   `climb_genUnitary_pow_notMem k (hk : ¬ p ∣ k)`.  This chain cannot move until (7).
7. **The `CharClass/LIX*` shape layer** (mine by the lead's ruling of 2026-09-10).  The
   only things pinning `Fin 3` on the definitional side are two lines:
   `LIXSectionManuscript:82` `VIdx dd = Fin 3 ⊕ HIdx dd` and `:88`
   `baseM dd = ↥(unitVectors (Fin 3)) × baseY dd`.  `HBlk`, `HIdx`, `baseY` and `Hmat` are
   already `dd`-generic and `n`-free.  So: `Gen.VIdx n dd = Fin (n+1) ⊕ HIdx dd`,
   `Gen.baseM n dd = ↥(unitVectors (Fin (n+1))) × baseY dd`, and `Vmat`, `sProj`, `eProj`,
   `FHmat`, `EHmat` (`LemmaTwoStatement`) follow.  `eThree` becomes `Gen.eLast n =
   Pi.single (Fin.last n) 1` with `eThree` keeping its numeral spelling and an `rfl`
   bridge, exactly as `e3` did — several `CharClass` files `simp [eThree]`.  **Out of
   scope by the lead's ruling:** the coefficient parameter (sp-coeff) and the Step C
   geometry (`LIXSectionChart/Deriv/LocalHomeo`, `LIXHsq*`, `LIXStepCOdd*`,
   `RelativeSupport`, `Thom*`, and any move of the constant section off `e_last`), which
   are sp-oddside's after sp-design reports where the zero sits.

## NEEDS

* **`CharClass.VIdx`/`baseM` are `Fin 3`-bound** (`CharClass/LIXSectionManuscript.lean:82,
  88).  The Corollary-4 chain (`LIXLemmaSixCor4`, `LIXLemmaSixField`, `LIXLemmaSixHIdx`)
  crosses into `CharClass.FHmat`/`EHmat` over `VIdx dd = Fin 3 ⊕ HIdx dd`, so that chain
  cannot go generic in `n` until `CharClass` does.  `CharClass` belongs to `sp-coeff` by
  the note's table, but the *rank* generalisation of `VIdx`/`baseM` is not a coefficient
  question; the lead should say who owns it.  Until then this lane keeps the Cor-4 chain
  abstract over the `LemmaTwoHolds` `Prop` and leaves the `k`-indexed seam there.
* Nothing else is blocking.

## TRAPS

* `lake build Palomar.LIXSolution` is **not** available in a lane clone: `laneprobe.sh`
  rsyncs only `GroupApproximation/` and `GroupApproximation.lean`, so the `Palomar*` lib
  roots do not exist there and the probe dies with `unknown target` before building
  anything.
* **`warm_clones.sh` was still running 50 minutes in and rewrites lane clones under
  running probes**, in three ways, each of which can produce a wrong verdict:
  it `rsync -a --delete`s the *node-side* `nonsofic_existence/GroupApproximation/` over
  the clone's **sources** (that tree is stale — its `LIXBlockProjections.lean` was still
  the old `n = 2` file while mine was in the clone); it `rm -rf`s
  `.lake/build/ir/GroupApproximation`; and it `cp -al`s the node tree's oleans into the
  clone.  Consequences, all observed today: a probe that reads `failed to open file
  '...olean'` or `bad import` on a module it never touched is seeing this, not a
  regression; a peer's brand-new module can be deleted from the clone *after*
  `laneprobe.sh` put it there; and a hard-linked olean can in principle be replayed for a
  module you have edited.  **Before trusting a probe: `md5sum` your file in the clone
  against your local copy, and require `✔ … Built <your module> (Ns)` in the log, never
  `ℹ … Replayed <your module>`.**  Reported to the lead.
* `lake build GroupApproximation` (the library root) is the wrong gate for a lane: it
  builds every file under `GroupApproximation/`, including the untracked files other lanes
  are dropping into the shared tree while the probe runs, so the job count climbs and a
  peer's red file fails a probe that has nothing to do with this lane.  **The right target
  is the seven maximal elements of the closure**, which between them cover all 124
  transitive importers of `LIXBlockProjections`:
  `GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIX`,
  `GroupApproximation.CharClass.ChernTautHyperIso`,
  `GroupApproximation.CharClass.LIXLerayHirschInstance`,
  `GroupApproximation.CharClass.LIXStepCOddHsq`,
  `GroupApproximation.CharClass.LerayHirschCoeffComap`,
  `GroupApproximation.CharClass.ParityEvenLemmaTwoClosed`,
  `GroupApproximation.CharClass.SliceRootsBlock`.
* `Nat.pow` recurses on the exponent, so `2 ^ (i + 1)` and `2 ^ i * 2` are definitionally
  equal but `2 ^ (i + 1)` and `2 * 2 ^ i` are **not**.  Any rank generalisation that wants
  to keep the mod-2 `rfl`s must write `2 ^ i * n`, never `n * 2 ^ i`.
