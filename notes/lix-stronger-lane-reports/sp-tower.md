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

Everything else this lane wrote is in the GREEN section above.

* `Analysis/LIXLemmaSixCor4.lean` — the `stageEval_def` fix in it is authored and its file
  cannot be compiled while `CharClass` is red for `sp-coeff`'s reasons.  Its sibling
  `LIXLemmaSixStageZero`, which carries the identical `stageProj_def` fix, **is** green, so
  the fix itself is verified; what is unverified is only that this one file still elaborates
  once `CharClass` builds again.

### What the gate proved, file by file (kept for the record)

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

## THE C*-SIDE GATE — 2026-09-10 11:56 (cs-stages, PROBE GREEN, 3040 jobs) — **RETIRED, RE-RUNNING**

> **Superseded 13:2x.**  `purge_stale.py` gained an import-transitive criterion after this
> run.  Measured on this same clone minutes apart with no edits between: 13:0x printed
> `purged 0 stale artifact sets (source newer than olean)`, 13:2x printed `purged 2870
> stale artifact sets (source-newer=0, import-newer=2870) of 4838 oleans`.  Fifty-nine
> percent of cs-stages was stale by the import test while source-newer was zero — which is
> the fresh-trace-over-stale-olean mode seen from the only angle that can see it.  So the
> run below, the 12:15 equator run and the 13:0x shape-layer run were all taken over a
> clone in that state.  They are not necessarily wrong; they are **unevidenced**, and I am
> not restating them as confirmed.  The whole gate plus all four new leaves has been
> relaunched on one command under the strengthened purge, and that verdict replaces this
> section.  The axiom lines below stand or fall with it.

### The retired run, kept for the record

Target: the seven `CharClass`-free maximal elements of my closure — `LIXLemmaSixField`,
`LIXLemmaSixClimb`, `LIXLemmaSixDiagEnd`, `LIXLimitSimple`, `LIXStageAlgebraSeparable`,
`LIXConnectingMapFullnessTower`, `LIXLimitSectionMatrix`.  That set covers every file this
lane touched except `LIXLemmaSixCor4`, which cannot build while `CharClass` is red for
`sp-coeff`'s reasons.  **The whole C*-side of the LIX tower is now generic in the rank `n`
and green.**

The two headline axiom lines from that run:

```text
'GroupApproximation.LIX.lixLimit_isSimpleCStar'     depends on axioms: [propext, Classical.choice, Quot.sound]
'GroupApproximation.LIX.Gen.lixLimit_isSimpleCStar' depends on axioms: [propext, Classical.choice, Quot.sound]
```

so **the counterexample algebra is simple at every rank, unconditionally**, on exactly the
classical allowlist — and so is `lixLimit_separableSpace`.

Every file's `Built` line, with the run that produced it (all on the lead's rebuilt clone,
real copies, no hard links, my modules' artifacts deleted before the first of them):

| module | | run |
|---|---|---|
| `LIXBlockProjections` | Built 67s | 11:29 |
| `LIXStageAlgebra` | Built 51s | 11:29 |
| `LIXConnectingMapPoints` | Built 35s | 11:29 |
| `LIXGeneratorUnitary` | Built 32s | 11:29 |
| `LIXConnectingMap` | Built 44s | 11:29 |
| `LIXStageAlgebraSeparable` | Built 42s | 11:29 |
| `LIXLimitAlgebra` | Built 39s | 11:29 |
| `LIXConnectingMapFullness` | Built 39s | 11:29 |
| `LIXLemmaSixStageZero`, `LIXLemmaSixClimb` | Built (41s) | 11:29 |
| `LIXLemmaSixDiagEnd` | Built 46s | 11:44 |
| `LIXConnectingMapFullnessSum` | Built 160s | 11:44 |
| `LIXConnectingMapFullnessTower` | Built 64s | 11:44 |
| `LIXLimitSimple` | Built 46s | 11:56 |

## The generic equator, 2026-09-10 12:15 (cs-stages, **PROBE GREEN, 2386 jobs**)

`Analysis/LIXGenericEquator.lean`, a **new file imported by nothing**, probed on its own so
that a red in it could not redden the `n = 2` closure:

```text
✔ [2386/2386] Built GroupApproximation.Analysis.LIXGenericEquator (57s)
```

It carries `Gen.equatorEmb n : ℝ^{2n+1} → ℂ^{n+1}`, built over the index equivalence
`Gen.eqIdx n : (Fin n × Fin 2) ⊕ Unit ≃ Fin (2n+1)`, and the two facts the whole power
chain rests on — both holding for **every** `a`, with no norm hypothesis:

* `Gen.re_equatorEmb_last` — the last complex coordinate is purely imaginary, so the image
  is always on the equator, `x (Fin.last n)` is never `±1`, and *both* hemisphere frames
  are defined at every point.  This is the reason a usable formula exists at all.
* `Gen.sum_norm_sq_equatorEmb` — the embedding is an isometry, so a unit vector of `E n`
  goes to a unit vector of `ℂ^{n+1}`.

Together they say the **norm is the only hypothesis that fails off the sphere**, which is
what makes radial normalisation the right and sufficient repair.

The gate found five defects on the first pass, all mechanical and all fixed: two `dif_pos`
patterns that could not match because the `Fin` coercion had not been reduced (fixed by
publishing `eqFwd_inl_val` / `eqFwd_inr_val` as `rfl` simp lemmas), a `Finset.sum_const`
applied to a sum over `Unit` whose body mentions the bound variable, and two `simpa`
continuity steps that normalised the *term* into `Pi.mul` shape while the goal stayed a
lambda (fixed by `simp only [equatorEmb_last]` and `exact`).

**Extended and green again at 12:25, 2386 jobs** (`✔ … Built … (52s)`), with the interface
lane `sp-powers` consumes:

```text
Gen.genSphere n y := Gen.genU2 n (Gen.equatorEmb n (‖y‖⁻¹ • y))
Gen.continuousOn_genSphere (n) : ContinuousOn (genSphere n) {y | y ≠ 0}
Gen.genSphere_conjTranspose_mul_self (n) {y} (hy : y ≠ 0) : (genSphere n y)ᴴ * genSphere n y = 1
Gen.genSphere_mul_conjTranspose      (n) {y} (hy : y ≠ 0) : genSphere n y * (genSphere n y)ᴴ = 1
```

`ContinuousOn` on the punctured space is the shape `sp-powers` asked for, and unitarity is
hypothesised on `y ≠ 0` rather than `‖y‖ = 1`, which is what the radial normalisation
actually gives and is strictly stronger than their `IsSphereUnitary` fields.  With them:
`Gen.incl n` and `Gen.incl_mul_conjTranspose : incl n * (incl n)ᴴ = 1 - rk1 (ePole n)
(ePole n)`, `Gen.genU2 n` with unitarity and continuity, and a **rank-generic
`Gen.conjTranspose_mul_self_of_comm`** replacing `LIXLemmaSixGenerator`'s `Fin 3`/`Fin 2`
version: compressing a unitary that commutes with `s sᴴ` by an isometry `s` gives a
unitary, with no rank argument and no determinant.

I had cut these three before the first probe rather than ship proofs I could not stand
behind; writing them properly took two more probe cycles, and both rounds of errors were
the same missed rewrite — a `dif_pos`/`Finset.sum` pattern that could not match because a
`Fin` coercion or a `ᴴ` had not been reduced first.

## The first fresh-clone run, 2026-09-10 11:29 (cs-stages, 9357 jobs)

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

## The rank-generic shape layer, 2026-09-10 12:40 (cs-stages) — AUTHORED, one probe round done

Item 7 of the plan, the lead's ruling of 2026-09-10 ("you own the RANK parameter in the
`CharClass/LIX*` shape layer as well").  Two new files, both **leaves — imported by
nothing**, so neither can redden anything while they are in flight.

**`GroupApproximation/CharClass/LIXShapeGeneric.lean`** (380 lines, import closure 16).
`Gen.VIdx n dd = Fin (n+1) ⊕ HIdx dd`, `Gen.baseM n dd = ↥(unitVectors (Fin (n+1))) ×
baseY dd`, `Gen.Vmat n`, `Gen.eLast n = Pi.single (Fin.last n) 1`, `Gen.aVec/bVec/cVec`,
`Gen.sProj/eProj/FHmat/EHmat n`, and the two theorems that carry the content —
`Gen.isMTSectionData_manuscriptData n` (the manuscript's pair is section data for `W_g` at
every rank) and `Gen.manuscriptSection_eq_zero_iff_concrete n` (**exactly one zero, at
every rank**).  Plus `Gen.HasStepAUnitary n dd`.

Three decisions worth writing down.

* **Purely additive.**  Not one line of `LIXSectionManuscript.lean` or
  `LemmaTwoStatement.lean` changed.  Those two names are consumed by 83 `CharClass` files;
  rewriting them as `n = 2` specialisations the way the `Analysis` side was done would put
  every one of those files at risk for zero mathematical gain, because the rank-two
  spellings are already definitionally the generic ones.  §7 of the new file proves
  exactly that, fourteen bridges, every one `rfl`: `VIdx`, `baseM`, `Hmat`, `Vmat`,
  `eThree`, `aVec`, `bVec`, `cVec`, `negEThree`, `sProj`, `eProj`, `FHmat`, `EHmat`,
  `HasStepAUnitary`.  **All fourteen elaborated on the first probe.**  `Fin 3` really is
  `Fin (2 + 1)` and `(2 : Fin 3)` really is `Fin.last 2` at default transparency, so no
  `cast` and no `Equiv` stands between the fixed-rank layer and the generic one.
* **`H` and `c` are re-indexed by the point of `Y` alone**, not by the pair `(x, y) ∈ M`,
  because at general rank the first factor of `M` moves and `H` does not.  `Hmat_eq` and
  `cVec_eq` record that this too is a `rfl`.  This is bookkeeping on the coefficient side,
  not a generalisation of it: the coefficient parameter `dd` is untouched and stays
  `sp-coeff`'s.
* **The constant section is the generator's pole, and that is now a theorem.**
  `Gen.eLast n` and `LIX.Gen.ePole n` are the *same term*, `Pi.single (Fin.last n) 1`, so
  `eLast_eq_ePole` and `eThree_eq_ePole` are `rfl`.  That is the mechanical content of the
  lead's "do not move the constant section off `e_last`": the analysis side's Householder
  frames are built around `Fin.last n`, and any other choice inserts a permutation between
  the two sides of Step A for no gain.  The bridge costs three modules of import closure
  (16 against `LemmaTwoStatement`'s 13) because `LIXGeneratorUnitary`'s own closure is 2.

**`GroupApproximation/Analysis/LIXLemmaTwoPropGeneric.lean`** (131 lines).
`Gen.lixDD n j = fun i => STW59.Gen.stageRank n i`, with `even_lixDD` now taking
`Even n` as a hypothesis (at rank two it was automatic; at rank `n` it is a condition on
`n`, and it is the condition Step D consumes), `lixDD_pos` under `[NeZero n]`, and
`dvd_lixDD` from `STW59.Gen.dvd_stageRank` — the shape the mod-`p` argument wants, and the
reason the rank carries the prime rather than the stage.

**Where `k` enters, and why it is the section rather than the winding.**  `LemmaTwoHolds`
compares two complements inside one `V = 𝟏^{n+1} ⊕ H`, and uses nothing about the
tautological section beyond its being a continuous unit section of the trivial block.  So
the seam is stated for an arbitrary such section,

```
Gen.LemmaTwoFor n dd b  :=  ¬ ContinuousMvNEquiv (Gen.FHmatOf n b) (CharClass.Gen.EHmat n)
Gen.LemmaTwoHolds n     :=  ∀ j, Gen.LemmaTwoFor n (Gen.lixDD n j) (CharClass.Gen.bVec n)
```

with `Gen.FHmatOf_bVec : FHmatOf n (bVec n) m = CharClass.Gen.FHmat n m := rfl`.  When
`sp-powers`' `exists_homotopy_pow_comp_normGen` lands, the `k`-indexed seam is
`LemmaTwoFor n (lixDD n j) b_k` — **no statement in this file changes and no step of the
reduction changes**.  Naming the section rather than the winding is what makes this layer
independent of how the degree-`k` section is built, which is the only reason it could be
written before that lane is green.

### Probe round 1 (12:40, cs-stages, 8671 jobs, `purged 0`) — RED, one cause

`✖ Building GroupApproximation.CharClass.LIXShapeGeneric (87s)` with **two errors, both
the same one**: `Unknown identifier LIX.Gen.ePole`, written `STW59.Gen.ePole`.  The
generator file lives in `GroupApproximation.LIX`, not `GroupApproximation.STW59` — the two
halves of my own lane sit in different namespaces and I had assumed one.  Everything else
in 380 lines, including all fourteen `rfl` bridges and both content theorems, elaborated.

### Probe round 2 (13:0x, cs-stages, **PROBE GREEN, 8676 jobs**, `purged 0`)

```
✔ [8675/8676] Built GroupApproximation.CharClass.LIXShapeGeneric (110s)
✔ [8676/8676] Built GroupApproximation.Analysis.LIXLemmaTwoPropGeneric (159s)
Build completed successfully (8676 jobs).
EXIT=0
```

Both modules **`Built`, neither `Replayed`, and neither absent** — the three-way check, not
the two-way one.  What the green establishes, beyond the two files compiling:

* **All fourteen rank-two spellings are definitionally their `n = 2` instances.**  `Fin 3`
  is `Fin (2 + 1)`, `(2 : Fin 3)` is `Fin.last 2`, and the `Fintype`/`TopologicalSpace`
  instances synthesised on either side are defeq, since `Iff.rfl` had to check them.
* **`eThree = LIX.Gen.ePole 2` is a `rfl`.**  The manuscript's constant section and the
  Householder generator's pole are one term.  This is the mechanical justification for the
  lead's "do not move the constant section off `e_last`", and it now survives review
  without anyone re-deriving it.
* **`LemmaTwoHolds ↔ Gen.LemmaTwoHolds 2` is an `Iff.rfl`.**  The endpoint's single
  topological input at rank two *is* the rank-`n` input at `n = 2`, so nothing that
  consumes `LemmaTwoHolds` — `not_problemLIX_of_lemmaTwo` included — has to change for the
  generic seam to exist.
* The rank-`n` "exactly one zero" theorem
  (`Gen.manuscriptSection_eq_zero_iff_concrete`) is proved, not assumed: over
  `S¹ × S^{2n+1} × Y` the manuscript's section vanishes at exactly one point at **every**
  rank, with no characteristic class and no counting.

## The rank-generic H-index bridge, 2026-09-10 13:1x — AUTHORED, UNVERIFIED

`GroupApproximation/Analysis/LIXLemmaSixHIdxGeneric.lean` (296 lines, leaf).  The rank-`n`
form of `LIXLemmaSixHIdx`: `Gen.hMatY n j`, `Gen.hIdxTo/hIdxFrom/hIdxEquiv n j`, and the
two theorems that matter, `Gen.hMatY_hIdxTo` and `Gen.hMatY_reindex` — **the manuscript's
`H` is the tower's `H`, at every rank**, entrywise and as matrices.

Why this one is safe to write before the renormalised generator exists: the redesign
changes the **trivial block** — the section, the generator, the winding — and touches `H`
nowhere.  So this identification is needed by the Corollary-4 chain in either form and
cannot be invalidated by the `k`-indexed rebuild.  It is also the piece that lets the chain
cross into `CharClass` at general rank, and it needs nothing from `sp-powers`.

Two simplifications fell out of `LIXShapeGeneric` re-indexing `Hmat` by the point of `Y`
alone: `hMatY` is `CharClass.Gen.Hmat` outright, so it needs no `Classical.arbitrary` point
of the sphere and no `Nonempty` instance; and `continuous_hMatY` is
`CharClass.Gen.continuous_Hmat` outright, with no composition against a constant first
factor.

**One bridge deliberately not written.**  `hIdxTo`, `hIdxFrom` and `hIdxEquiv` get no
`n = 2` bridge, unlike all fourteen in `LIXShapeGeneric`.  They would not be `rfl`: the
rank-two file compiles its own structural recursion on `j`, so identifying it with this
file's is a theorem **by induction on `j`**.  The induction is four lines, but its closing
step lands on the reducible-transparency `rfl` that `rw` inserts, across `lixDD j` versus
`Gen.lixDD 2 j` — exactly the shape that costs a probe round.  Nothing consumes it: the
only consumer would be a port of the Corollary-4 chain, which will restate the reindexing
at rank `n` outright.  Writing a declaration into a leaf file to see whether it elaborates
is a probe cycle spent on a decoration, so it waits for a consumer.

## The landing set, as of 2026-09-10 13:15

Fifteen modified, five new, all mine, nothing else in `Analysis/LIX*` or
`CharClass/LIXShape*` touched by this lane.

Modified (these are what the seven-importer gate covers): `LIXBlockProjections`,
`LIXConnectingMap`, `LIXConnectingMapFullness`, `LIXConnectingMapFullnessSum`,
`LIXConnectingMapFullnessTower`, `LIXConnectingMapPoints`, `LIXGeneratorUnitary`,
`LIXLemmaSixClimb`, `LIXLemmaSixCor4`, `LIXLemmaSixDiagEnd`, `LIXLemmaSixStageZero`,
`LIXLimitAlgebra`, `LIXLimitSimple`, `LIXStageAlgebra`, `LIXStageAlgebraSeparable`.

New, all leaves imported by nothing: `Analysis/LIXGenericEquator`,
`Analysis/LIXLemmaTwoPropGeneric`, `Analysis/LIXLemmaSixHIdxGeneric`,
`Analysis/LIXLemmaSixFieldGeneric`, `CharClass/LIXShapeGeneric`.

**Twenty files, every one green under a `Built` line in a log from this afternoon.**

**The seven-importer gate does not test the four new files**, precisely because nothing
imports them.  The landing probe must name them explicitly alongside the seven, or they
land unverified.  That is a trap in the gate design, not in the files.

## The re-verification, 2026-09-10 13:15–14:0x — and the no-op green that nearly passed

Re-running the whole `CharClass`-free gate plus all four leaves under the strengthened
purge produced `PROBE GREEN`, `Build completed successfully (8719 jobs)`,
`purged 0 (source-newer=0, import-newer=0) of 1972 oleans`, zero errors, zero `sorryAx`,
and these lines:

```text
'GroupApproximation.LIX.Gen.lixLimit_isSimpleCStar'  depends on axioms: [propext, Classical.choice, Quot.sound]
'GroupApproximation.LIX.lixLimit_isSimpleCStar'      depends on axioms: [propext, Classical.choice, Quot.sound]
'GroupApproximation.LIX.Gen.lixLimit_hasK1InjWitness' depends on axioms: [propext, Classical.choice, Quot.sound]
'GroupApproximation.LIX.lixLimit_separableSpace'      depends on axioms: [propext, Classical.choice, Quot.sound]
```

Then I counted the log: **`grep -c Built` = 0, `grep -c Replayed` = 6.**  Of 8719 jobs, not
one of my nineteen modules was elaborated.  The six that printed anything printed it
because they carry `#audit_axioms`, and lake replayed their recorded `info:` lines
verbatim — so **the axiom-allowlist lines above came back word for word from a run that did
not happen.**  A replayed audit line is indistinguishable from a fresh one.

This is my own "absence is not evidence" rule turned around and pointed at me, and the
purge is what disarmed it: `purged 0` made deleting artifacts look unnecessary.  It was
not.  The artifacts were *consistent* — they were simply not mine to trust yet.  Two
habits, both now in `FLEET_TRAPS`:

* after any gate you intend to land on, `grep -c 'Built' $LOG` and require it to be at
  least the number of modules you changed — **a job count is not a work count**;
* "delete your own modules' remote artifacts first" is not a precaution for the stale
  case, it is the only way to force elaboration.

So I deleted them: 73 artifact files across the nineteen modules
(`.olean`, `.ilean`, `.trace`, `.olean.hash`, `ir/*.c`; `.ilean.hash` may stay, it is
IDE-only), and relaunched the same eleven-module gate.

### THE GATE, FOR REAL — `laneprobe-20260910-132043.log`, **PROBE GREEN, 8719 jobs**

```text
purged 12 stale artifact sets (source-newer=0, import-newer=12) of 1954 oleans
Build completed successfully (8719 jobs).   EXIT=0   PROBE GREEN
grep -c Built = 29        grep -c Replayed = 3
grep -c sorryAx = 0       grep -c "uses 'sorry'" = 0
no axiom anywhere in the log outside [propext, Classical.choice, Quot.sound]
```

**Eighteen of my nineteen files were freshly elaborated in this run**, by name:
`LIXBlockProjections` 82s, `LIXGeneratorUnitary` 69s, `LIXConnectingMapPoints` 77s,
`LIXConnectingMap` 81s, `LIXConnectingMapFullness` 120s, `LIXConnectingMapFullnessSum`
250s, `LIXConnectingMapFullnessTower` 93s, `LIXStageAlgebra` 93s,
`LIXStageAlgebraSeparable` 78s, `LIXLimitAlgebra` 121s, `LIXLimitSimple` 90s,
`LIXLemmaSixStageZero` 136s, `LIXLemmaSixClimb` 114s, `LIXLemmaSixDiagEnd` 90s, and the
four new leaves — `LIXGenericEquator` 64s, `CharClass/LIXShapeGeneric` 187s,
`LIXLemmaTwoPropGeneric` 262s, `LIXLemmaSixHIdxGeneric` 268s.  Eleven more of the
`LIXLemmaSix*` chain came with them.

### The nineteenth, 2026-09-10 13:41 — `LIXLemmaSixCor4` GREEN

`LIXLemmaSixCor4` imports `CharClass` and so cannot appear in a `CharClass`-free gate.
Probed on its own after the artifact deletion: **PROBE GREEN, 8711 jobs**, `purged 0
(source-newer=0, import-newer=0) of 1971 oleans`, zero errors, zero `sorryAx`, with
`✔ Built GroupApproximation.Analysis.LIXLemmaSixCor4 (266s)` and `LIXLemmaSixCompare`
(212s) beside it.  Built = 2, Replayed = 5.

**So all nineteen of my files are green under fresh elaboration.**  Read the Replayed = 5
honestly, though: the `CharClass` modules in Cor-4's closure were replayed from artifacts
the purge judged consistent, not rebuilt.  That is fine for *my* file, whose own
elaboration is what the `Built` line certifies, and it is not evidence about `sp-coeff`'s
layer — the seven-importer gate is what tests that, and it reaches cohomology modules this
probe never touches.

One gap found and deliberately not fixed yet: `LIXLemmaSixCor4` carries **no**
`#audit_axioms` line, so `lixLimit_hasK1InjWitness_of` — the endpoint the C⋆-side consumes
— has never had its axiom closure printed.  It cannot use `#audit_closed_axioms`, which
rejects a leading hypothesis by design, but `#audit_axioms` applies.  Adding it now would
edit a file in the landing batch and invalidate the green it just earned, so it waits until
after the batch lands.

The axiom lines, now genuinely computed rather than replayed:

```text
'GroupApproximation.LIX.lixLimit_isSimpleCStar'       [propext, Classical.choice, Quot.sound]
'GroupApproximation.LIX.Gen.lixLimit_isSimpleCStar'   [propext, Classical.choice, Quot.sound]
'GroupApproximation.LIX.lixLimit_hasK1InjWitness'     [propext, Classical.choice, Quot.sound]
'GroupApproximation.LIX.Gen.lixLimit_hasK1InjWitness' [propext, Classical.choice, Quot.sound]
'GroupApproximation.LIX.lixLimit_separableSpace'      [propext, Classical.choice, Quot.sound]
```

Two of the `LIXLimitSectionMatrix` lines look at first like a violation because they end
`[propext,` — they are the multi-line form, `Classical.choice,` and `Quot.sound]` follow on
the next two lines.  Grepping a single line for the closing bracket reports a false red on
every long axiom list in the repository.

**So: the counterexample algebra is simple and separable at every rank, unconditionally, on
exactly the classical allowlist — and this time the run that says so is a run that
happened.**

## The rank-generic extension layer, 2026-09-10 14:0x — AUTHORED, one probe round

`GroupApproximation/Analysis/LIXLemmaSixFieldGeneric.lean` (307 lines, leaf).  §3 of
`LIXLemmaSixField` — "the corner, its ambient, and the extension" — at rank `n`: the
null-homotopy lives in the corner `𝟏^n ⊕ P` inside `M_{Fin n ⊕ H}`, the unitary field has
to live in `M_{Fin (n+1) ⊕ H}`, and `Gen.extAmb n` crosses between them.  `Gen.cornerE`,
`Gen.bigE`, `Gen.bigF`, `Gen.jIncl`, `Gen.IsCornerUnit`, and the four results that carry
the weight: `extAmb_conjTranspose_mul_self`, `extAmb_mul_conjTranspose` (**the extension of
a corner unitary is unitary, at every rank**), `extAmb_mul`, `extAmb_fromBlocks`.

The port needed **no new geometry**.  Everything the extension wants from the isometry is
`inclᴴ incl = 1` and `incl inclᴴ = 1 − e eᴴ`, and both were already proved at every rank in
`LIXGenericEquator` for `sp-powers`.  The section was already abstract in the block bundle
`P : Y → Matrix HI HI ℂ` and in the base `Y`, so the rank was the only thing left to
generalise.

This one also survives the renormalised generator by inspection: the redesign changes
*which* corner unitary gets extended, not the corner, the ambient, the isometry, or any
identity in the section.

### Probe round 1 — RED, and the interesting failure

Four errors, two causes, both in the rank-two bridge section; the entire generic layer
elaborated.  `cornerE_eq_gen`, `bigE_eq_gen` and `bigF_eq_gen` were `rfl` as expected —
which incidentally re-confirms `e₃ = ePole 2` from the other side of the repository.
`jIncl_eq_gen` and `ext3_eq_gen` were not, with

```text
Not a definitional equality: the left-hand side
  jIncl HI
is not definitionally equal to the right-hand side
  Gen.jIncl 2 HI
```

a message that names the wrapper and never the cause.  The cause is two spellings of one
isometry: rank-two `incl` is `if (i : ℕ) = (j : ℕ) then 1 else 0`, through `Nat.decEq` on
the coerced values, and `Gen.incl n` is `if i = j.castSucc then 1 else 0`, through
`instDecidableEqFin`.  **Every entry agrees; `rfl` sees the instances, not the entries.**

This is the first place in the whole rank generalisation where a bridge was not free, and
it is worth being precise about why it is not a counterexample to the others: the fourteen
`rfl`s in `CharClass/LIXShapeGeneric.lean` all cross `Fin 3` versus `Fin (2+1)` and
`(2 : Fin 3)` versus `Fin.last 2`, which are literal-arithmetic questions the kernel
settles; this one crosses a `Decidable` instance, which it does not.  Repair is one
`ext`/`fin_cases`/`rfl` lemma plus two `rw`s.  In `FLEET_TRAPS`, with the rule: when a
generic definition must stay `rfl`-compatible with a fixed-size one, copy the original's
decidable condition verbatim rather than writing the more natural one.

### Probe round 2 — **PROBE GREEN, 2988 jobs**

```
✔ [2988/2988] Built GroupApproximation.Analysis.LIXLemmaSixFieldGeneric (156s)
purged 0 stale artifact sets (source-newer=0, import-newer=0) of 1973 oleans
```

`Built`, not `Replayed`, not absent.

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
6. **The `k`-indexed Corollary-4 chain, around the renormalised generator.**  Lead's
   design decision of 2026-09-10, which *replaces* the abstract seam this lane had been
   keeping.  The endpoint witness stops being `u` and becomes

   > `ũ := Aᴴ u` with `A := U ∘ wallRetract` (`sp-powers`' `LIXPowersNormalise`), `U` the
   > seam generator as a ball unitary and `wallRetract` the radial retraction onto the
   > wall, so `A` is a ball unitary and **`ũ` is identically `1` on the wall**.

   What this lane carries:
   * the stage-zero unitary and everything climbing the tower are built from `ũ ⊕ 1_H`,
     not `u ⊕ 1_H`;
   * `diag(ũ ⊕ 1_H, 1) ∈ U₀` needs **no new geometry**: it follows from this lane's
     existing contraction of `u ⊕ 1` (`Gen.seamPath_ePole_zero/_one/_unitary`) together
     with `A ⊕ 1` extending over the ball, a product of two contractible maps;
   * the frames for the power chain are the hemisphere frames gauged by `A` on one
     hemisphere (seam `ũ`, still `pole ↦ x`), pulled back along `Σψ_k` for the `k`-th
     power (seam `ũ ∘ ψ_k`, `pole ↦ x ∘ Σψ_k`);
   * the input consumed from `sp-powers` is `exists_homotopy_pow_comp_normGen`: for a
     ball-unitary generator that is `1` on the wall, an explicit unitary homotopy from
     `W^{k+1}` to `W ∘ ψ_k`.
   Then "`v^k ∈ U₀(A_j)` ⇒ a unitary field conjugating `EHmat` onto `FHmat_k`" is
   `LIXLemmaSixField`'s existing construction with the substituted frames.  **No clutching
   layer anywhere and no path in `U(n)` anywhere** — the live Corollary 4 never used the
   clutching layer, and the power version does not either.  `FHmat_k` is `FHmat` with
   `b = x ∘ Σψ_k`, which is `CharClass`-side and `sp-oddside`'s.

   The generator's domain, settled for `sp-powers` on 2026-09-10: what this lane can
   supply is **not** a ball unitary but `Gen.genSphere n y := Gen.genU2 n (Gen.equatorEmb n
   (‖y‖⁻¹ • y))`, continuous and unitary at every `y ≠ 0`, hence on any shell and on the
   sphere.  The ball is impossible, not merely unproved: `midNorm p x =
   sqrt (2 + 2 Re⟨p,x⟩)` is the length of `p + x` *only for unit vectors* and hits zero on
   the whole half-space `Re⟨p,x⟩ ≤ -1`, and `transPhase a b = ⟨a,b⟩/‖⟨a,b⟩‖` is
   discontinuous where `⟨a,b⟩ = 0`.  What makes the sphere case work is that
   `equatorEmb`'s last complex coordinate is purely imaginary **for every** `a ∈ E`, not
   just on the sphere, so the image always lies on the equator and both hemisphere frames
   are always defined; the norm is the only hypothesis that fails, and `‖y‖⁻¹ • y` repairs
   it.  Still to write: `Gen.equatorEmb n`, `Gen.incl n`, `Gen.genU2 n`, `Gen.genSphere n`.
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

* ~~**`CharClass.VIdx`/`baseM` are `Fin 3`-bound.**~~  **Resolved 2026-09-10.**  The lead
  ruled the rank parameter in the `CharClass/LIX*` shape layer mine, and
  `CharClass/LIXShapeGeneric.lean` supplies `Gen.VIdx n`, `Gen.baseM n` and everything
  built on them additively, with all fourteen rank-two spellings proved to be the `n = 2`
  instances by `rfl`.  The Corollary-4 chain can now cross into `CharClass` at general
  rank.
* **The `k`-indexed Corollary-4 chain is input-blocked, not design-blocked.**  Its two
  inputs are `sp-powers`' `exists_homotopy_pow_comp_normGen` and the renormalised
  generator's `wallRetract`, neither of which is green yet (`sp-powers` reported
  `LIXPowersAngle` red at 12:2x).  What did not have to wait is the seam itself:
  `Gen.LemmaTwoFor n dd b` is stated over the section, so the `k`-indexed instance is a
  choice of `b` and costs no new statement here.  I am not authoring the degree-`k`
  geometry ahead of their signature — that is exactly the class of guess that costs a
  probe cycle and lands wrong.
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
