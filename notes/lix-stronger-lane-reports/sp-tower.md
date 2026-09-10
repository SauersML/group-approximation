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

## AUTHORED, UNVERIFIED

* `Analysis/LIXConnectingMapPoints.lean` — `Gen.baseXinf n`, `Gen.truncate n i`,
  `Gen.infDenseSeq n`, `Gen.stagePoint n i` and the two density lemmas, plus the `n = 2`
  layer.  Landed in the tree, awaiting a probe.
* `Analysis/LIXStageAlgebra.lean` — `Gen.stageProj n i`, `Gen.StageAlgebra n i` with the
  full C*-instance ladder checked by `example`, `Gen.stageEval`, the zero/corner lemmas,
  and `Gen.stageAlgebra_one_ne_zero` / `Gen.instNontrivialStageAlgebra` under `[NeZero n]`,
  plus the `n = 2` layer.  Landed in the tree, awaiting a probe.  The `CStarAlgebra`
  *pi*-instance `∀ n, CStarAlgebra (StageAlgebra n)` is deliberately left only at `n = 2`:
  a second, generic one would be a data-class diamond, and the tower/limit lane is the
  next deliverable, where it belongs.
* `Analysis/LIXGeneratorUnitary.lean` generic instantiation, drafted in this session's
  scratchpad (`sp/genu_gen.lean`) and **not yet installed**: `Gen.ePole n =
  Pi.single (Fin.last n) 1`, `Gen.genU n x = seamGen (ePole n) x`, both hemisphere
  trivialisations, `diag(u,1) ≃ 1` in `U(n+1)` via `seamPath (ePole n)`.  The whole
  Householder/frame engine above it is already generic, so this is a 150-line
  transcription with `Fin 3 ↦ Fin (n+1)` and `x 2 ↦ x (Fin.last n)`.

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
