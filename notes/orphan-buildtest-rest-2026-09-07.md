# Build test of the remaining 20 non-AlgTop orphans — 2026-09-07

Lane `lix-wire`. Assignment: build-test the 20 modules at
`scratchpad/lix/orphans-rest.txt` (all unreachable non-`AlgTop` orphans from
`notes/orphan-module-sweep-2026-09-07.md`, six of which repeat the previous
build-test round). Do not wire, do not edit `GroupApproximation.lean`.

## Method and provenance

Probed as 20 explicit `lake build` targets in one call, `lixprobe10.sh
lix-wire` (clone `census`, node acn116, cores 16-47). First attempt (against a
different, freshly-being-created clone) came back with every target failing
"no such file or directory" — recognized as a clone-population race (0
`GroupApproximation/` files synced) rather than 20 content failures, reported
as such, and re-run against a warm clone once confirmed ready. **This run's
`== lake build ...` line names all 20 targets and `acn116`**, confirming it is
this probe, not a stale or crossed one.

**Compiles yes/no** read off `lake`'s own `Some required targets logged
failures:` list. **Sorry count** is `grep -c "declaration uses" <log>`
restricted to lines Lean itself emitted (promoted to `error:` under this
project's `-DwarningAsError=true`), not a lexical scan of source text.

## Table

| Module | Compiles | Sorry (Lean) | Bucket |
|---|---|---|---|
| `Analysis.ChernCommonZeroBridge` | YES | 0 | compiles-and-dead |
| `Analysis.CuntzPedersenJordanMatrixTest` | YES | 0 | compiles-and-wanted |
| `Analysis.CuntzPedersenJordanModelTest` | YES | 0 | compiles-and-wanted |
| `Analysis.FiniteDimensionalFactorialTraceCore` | YES | 0 | compiles-and-wanted |
| `Analysis.LIXObstructionContradiction` | YES | 0 | compiles-and-dead |
| `Analysis.LIXObstructionLowPowerSums` | YES | 0 | compiles-and-dead |
| `Analysis.STW22CounterexampleAssemblyModelTest` | YES | 0 | compiles-and-wanted |
| `Analysis.SequentialGroupColimitDirectLimit` | **NO** | 0 | does-not-compile |
| `GGT.DGOLemma421FourGon` | **NO** | 0 | does-not-compile |
| `GGT.KazhdanHypGirthEightGenericProducers` | **NO** | **2** (lines 84, 87) | does-not-compile |
| `GGT.KazhdanHypGirthEightGeodesicWord` | **NO** | 0 | does-not-compile |
| `GGT.VanKampen.Estimating.UnboundScaled` | N/A | N/A | **tombstone — not applicable** |
| `KTheory.Basic` | YES | 0 | compiles-and-wanted |
| `KTheory.Functorial` | YES | 0 | compiles-and-wanted |
| `KTheory.Spaces` | (was NO; **fixed and landed**, see below) | 0 | compiles-and-wanted (after fix) |
| `Topology.AntipodalObstructionFromOddDegree` | YES | 0 | compiles-and-dead |
| `Topology.OddMapNormalization` | YES | 0 | compiles-and-dead |
| `Topology.TautologicalAntipodal` | YES | 0 | compiles-and-dead |
| `Topology.TautologicalCommonZero` | YES | 0 | compiles-and-dead |
| `Topology.TautologicalLineWinding` | YES | 0 | compiles-and-dead |

**14 of 20 compile as landed, 5 fail, 1 is a tombstone (N/A).** `KTheory.Spaces`
is fixed (below), bringing the compiling count to 15/20 as of `06739cc77`.
Total sorry, by Lean's own report: 2, both in one file
(`KazhdanHypGirthEightGenericProducers.lean`) — identical to the previous
round; no new sorry anywhere in this batch.

## `KTheory.Spaces` — fixed and landed, `06739cc77`

Repeat of the earlier finding, now acted on per instruction: `Spaces.lean:43`'s
`pullbackCoeffHom` failed to compile because it depends on
`instCommCStarAlgebraComplex`, itself noncomputable. One-keyword fix
(`noncomputable def`), no content change. Probed alone afterward:
`PROBE GREEN`, `Build completed successfully (2966 jobs)`, `sorryAx: none`.
With this, **all three of `KTheory.{Basic,Functorial,Spaces}` compile clean**
as explicit targets. The "UNPROBED, do not import yet" caution
(`0eede6bc0`, 2026-09-05) is now stale for all three files, not two.

## `GGT.VanKampen.Estimating.UnboundScaled` — tombstone, not a candidate

Emptied to 25 lines at `c685697b9` (landed roughly an hour before this probe):
zero declarations, one import, a docstring stating the content moved into
`Estimating/Assembly.lean` (`EstimatingUnboundOutputStatement`/
`EstimatingSelectionConstructionStatement` now carry `UnboundEstimate.OsinUnboundScale`
in place; the refuted form was renamed `EstimatingUnboundOutputHistoricalStatement`
with both refutations repointed). Confirmed this file's current content does
**not** reference the refuted statement family at all — nothing left to rest
on it. Recorded as not applicable rather than any bucket; the file's own
docstring says it may be deleted outright.

## The three `*Test` modules — the Prop each tests (read, not built, until now)

All three now confirmed **compiling**, so this evidence is live, not just
theoretical:

* `CuntzPedersenJordanModelTest` (at `A = ℂ`): `HasJordanDecomposition`,
  `HasUniqueJordanDecomposition`, `HasCuntzPedersenSeparation` — the two
  Jordan hypotheses are jointly satisfiable.
* `CuntzPedersenJordanMatrixTest` (at `M₂(ℂ)`, the noncommutative half the
  `ℂ` test structurally cannot reach): `IsTracialFunctional` proved
  **non-vacuous** (`trace2`) and **non-trivial**
  (`not_isTracialFunctional_entryFunctional`); separately,
  `isTracialFunctional_of_unitary_invariant`'s hypothesis proved **not
  automatic** (`exists_unitary_moving_entryFunctional`) — false at `ℂ`, which
  is exactly why the commutative test cannot see it.
* `STW22CounterexampleAssemblyModelTest`: `CoordinateStateBlockData`,
  `IsUniformTwoContinuous`, `HasUniformTwoDiscontinuousTracialState`,
  consuming `ArbitrarilyLateCoordinateStateConstraints` and
  `TracialTwoGauge` — a satisfiability check, a non-vacuity check, and an
  exact numeric verification of the audit's own (A16)/(A17) bound.

Per the standing rule that every hypothesis-bearing `Prop` is model-tested:
this evidence was previously unverifiable by anyone not running these files
by hand. It now builds.

## Five `Topology.Tautological*`/antipodal modules — content, not name, comparison

Read all five in full (~1043 lines). Grepped the whole reachable closure for
their distinctive vocabulary (`TautSection`, `CommonZeroProperty`,
`HasCommonZero`): one hit, `CharClass/LIXSectionManuscript.lean`, a false
positive (`dualTautSection`, unrelated). Read for mathematical content, not
just names, per the standing warning that an isolated file with disjoint
vocabulary defeats a grep: these five prove
`TautologicalCommonZero.CommonZeroProperty` (sections of `L^{⊕κ}` over `ℂPᴺ`
have a common zero, `κ ≤ N`) via an elementary route — Borsuk–Ulam/antipodal
reduction in general, a bare covering-space/winding-number argument (no
cohomology) for the proved rank-1 case.

**Decisive evidence is the files' own current text**:
`AntipodalObstructionFromOddDegree.lean`'s docstring states outright that its
conclusion rests on the same base theorem as the already-wired
`STW22.complexOddMapCommonZero_unconditional` — "the two routes now rest on
one theorem." So by content: **duplicated by the already-wired STW22 route**,
confirming the original sweep note's DEAD verdict independently. All five
confirmed compiling as landed (all `YES` above), so the duplication is a live
fact about a working cluster, not a stale one about a broken one.

**Limit of what this rules out, stated rather than elided**: this confirms no
overlap with the closed STW Problem LIX (K1-injectivity) chain specifically —
different bundles (mapping torus vs. tautological line over `ℂPᴺ`), different
techniques (Leray–Hirsch/Thom class vs. elementary winding number), different
end theorems — and no overlap with the wired STW22 route beyond what these
files already say about themselves. It is not an exhaustive search for every
possible disguised restatement across the whole reachable corpus.

## What was not done

No file besides `KTheory/Spaces.lean` was edited. `GroupApproximation.lean`
was not touched. No wiring performed.
