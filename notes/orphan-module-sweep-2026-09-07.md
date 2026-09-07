# Orphan module sweep, 2026-09-07

Lane `lix-orphans`. Task: classify every `.lean` file under `GroupApproximation/`
that is landed on `origin/main` but unreachable from `GroupApproximation.lean`'s
transitive import closure.

## Method

Computed independently, not taken on faith from the assignment:

1. Parsed `GroupApproximation.lean`'s import list and walked every `import` line
   transitively through the repo's own `.lean` files (skipping anything without a
   local file, i.e. Mathlib), to get the reachable set.
2. Diffed that against every `.lean` file under `GroupApproximation/` (found via
   `os.walk`, not `git ls-files`, so it matches what `lake build` actually globs).
3. **101 orphans**, matching the assignment's count.
4. Confirmed all 101 are landed (`git cat-file -e origin/main:<path>` — 101/101).
5. Built the import graph *among the orphans themselves* (108 internal edges) and
   confirmed, by exact module-string matching over every `.lean` file in the repo
   (not substring grep — a substring search on `HamSandwich` false-positived
   badly, see below), that **zero non-orphan file imports any orphan module**.
   This is a consistency check on the closure computation, not a new fact.
6. For each cluster: git history (`git log -- <path>`, `-S<string>` on the root
   file for the wiring commit), content comparison against same-topic reachable
   files, and a repo-wide grep for duplicate declarations by name.
7. Lexical `sorry`/`axiom` scan across all 101: **clean**. Every "hit" was a
   docstring sentence *about* having no sorry/axiom. This is a high-quality
   orphan set — none of it is scratch or stub work — which is exactly why the
   DEAD calls below lean on positive evidence of supersession, not on the
   material looking unfinished.

Breakdown by directory: AlgTop 46, ThirdParty 28, Analysis 14, Topology 5, GGT 5,
KTheory 3. Total 101.

**Verdict counts: DEAD 81, INTENTIONAL 6, WIRE 14.**

---

## DEAD (81)

### AlgTop/* — all 46 orphans in the directory

`GroupApproximation/AlgTop/` has 49 files; only 3 are reachable
(`ComplexProjectiveBasic.lean`, `CPTautologicalSection.lean`, both pulled in
transitively through `CharClass/`, and `PuncturedNormedSphere.lean`, imported
directly by root). The other 46 are orphans and none of them were touched after
the commit that superseded them.

Evidence, not inference:

- Root line 3458 reads (verbatim): `-- LIX characteristic-class layer
  (CharClass), wired 2026-09-05 23:33 EDT`, followed by ~210 `CharClass`
  imports. The commit that added this block
  (`92e358f9d`, 2026-09-05 23:32:25) is titled *"root: wire the LIX
  characteristic-class layer (210 CharClass modules + AlgTop.PuncturedNormedSphere),
  closure-checked, duplicate-free"* — i.e. the person who wired it explicitly
  decided to keep exactly one AlgTop file and leave the rest behind.
- `AlgTop/SteenrodCut.lean` and `CharClass/SteenrodCut.lean` are the same
  theorem (`cutU`/`cutV`/`cutU_union_cutV`/`cutU_inter_cutV`/...) with the same
  docstring voice; the CharClass version generalizes `Fin (m+1)` to `Fin N` and
  adds `eq_faceOfFinset`, `delta_comp_faceOfFinset` etc. This is a rewrite, not
  a coincidence.
- `CharClass/LemmaTwoZero.lean`'s own docstring says it outright: *"This is the
  same linear-algebra content as `AlgTop/ManuscriptSectionZeroCount.lean`'s
  `manuscriptSection_eq_zero_iff`, run in the clutched-circle model of `S¹`
  instead of the raw `[0,1]` interval that file uses."*
- Timeline: the real `algtop:` commits run 2026-09-05 15:47–20:26 (`git log
  --format="%ai %s" -- GroupApproximation/AlgTop/`, excluding snapshot
  commits). The `cc-*` commits that became `CharClass/` start at 18:17 the same
  day and the wiring lands at 23:32. Nothing in the 46 orphans has a commit
  timestamp after the wiring commit — I checked every one of them.
- `CharClass/` independently covers every AlgTop topic: Chern classes
  (`ChernClasses.lean`, `ChernRelation.lean`, ...), singular cohomology
  (`CohomologyBasic.lean`, ...), cup products (`CupVanish*`), bundle calculus
  (`Bundle*`), Leray-Hirsch (`LerayHirsch*`), Thom classes (`Thom*`), Gysin
  (`Gysin*`), Mayer-Vietoris, projective space, and the LIX Lemma 2 assembly
  itself (`LemmaTwo*`, 18 files — see next item).

Files: `BundleCalculusInvariant/ModelBridge/Projection/Pullback/Transport/UnitSection`,
`ChernEvenTopClass/LineRoots/Map/NewtonDischarge/NewtonIdentity/NewtonSquareZero/ParityCoefficient/PolynomialModel/PowerSums/Series/SplitNewton/SquareZeroIdeal`,
`CochainLeibniz`, `ComplexProjectiveChart/Cover/Hyperplane/Product/Puncture/PunctureRetract/Sphere`,
`CrossProduct`, `CupAssoc`, `CupCommutativitySign`, `CupProduct`, `EulerLocalModel`,
`EulerParityBridge`, `EvenCohomologyRing`, `FreeSubmodulePID`, `Kronecker`,
`ManuscriptSectionZeroCount`, `MappingTorusParity/ParityCore/SectionZeros`,
`OddDegreeOfHomeomorphism`, `SingularChainFree`, `SingularCohomology`, `Spheres`,
`SteenrodCut`, `UniversalCoefficients`, `WuBinomialGap`.

### Analysis/LIXObstructionContradiction.lean, Analysis/LIXObstructionLowPowerSums.lean (2)

Both import `AlgTop.*` (`MappingTorusParity`, `ChernPowerSums`), so they die with
their dependency. But there is direct positive evidence beyond that: both
files claim to close "Lemma 2"/"Lemma 3" of the LIX manuscript
(`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`),
committed 2026-09-05 16:36–16:49. The *landed* replacement is
`CharClass/LemmaTwoStatement.lean`'s `false_of_stepC_stepD`, assembled from
Steps A/C/D across an 18-file `CharClass/LemmaTwo*` cluster, committed
2026-09-05 20:05–20:28 ("cc-lix-odd: Step D at the LIX base, and Lemma 2
assembled") — later the same day, same shape of contradiction (Step C says a
top class is nonzero, Step D says it's zero). Same conclusion, same day, later
timestamp, wired. This is the AlgTop story repeating at the lemma level, not a
separate case.

### ThirdParty/HamSandwich.lean + ThirdParty/HamSandwich/SphereOddDegree/* — 27 files

`ThirdParty/HamSandwich/` has 199 files; 172 are reachable. The 27 orphans are
the wrapper `HamSandwich.lean` (which imports exactly this cluster and nothing
else — it was never itself imported by anything) plus 26 files under
`SphereOddDegree/`.

The landed route to the odd-degree theorem runs
`STW22NegativeSolution → STW22UnconditionalCore → ComplexOddMapCommonZero →
BorsukUlam → Final/OddDegreeTheoremUnconditional → ... → RPnInclusionCohomology`
(traced explicitly with a BFS, not assumed) — through an *affine cover / Mayer–
Vietoris* model. The orphan cluster is a **different, self-consistent, complete
route** through *cellular cohomology and cup products*, explicitly named
**Branch3** and **Branch4** in its own filenames
(`Branch3RPnGeneratorIdentificationFromCellular.lean`,
`Branch34OddMapFixesTopClassAssembly.lean`,
`AlgebraicTopology/Branch4Transfer{API,TopClass,Witness,Nonzero,Nonvanishing,
NonvanishingUnconditional}.lean`), each self-documented as sorry-free and
axiom-free (docstrings: "No `axiom`, `sorry`, `opaque`... is used").

**Branch2 is the winner** and it is landed: `AlgebraicTopology/Branch2{CoefficientReduction,
IntegralDegreeAction,RankOne}.lean` and `Final/OddDegreeTheoremBranch2Discharged.lean`
are all reachable. Branch3/4 lost and were never deleted. All 27 orphan files
were committed in one bulk landing, `land local work: Hull SC separation-2
rework, STW22 nuclear layer, HamSandwich SphereOddDegree port, manuscript sync`
(2026-08-31 13:58:55) or the earlier vendoring commits the same night — nothing
touched since.

Files: `HamSandwich.lean`; `SphereOddDegree/{Branch34OddMapFixesTopClassAssembly,
Branch3RPnGeneratorIdentificationFromCellular, RPnActualAlphaPowerEqGeneratorNoCup,
RPnActualAlphaPowersGenerate, RPnCellularCochain, RPnCellularCupProduct,
RPnCellularDiagonal, RPnCellularFiltration, RPnCupProductNonvanishing,
RPnCupProductNonvanishingTarget, RPnCupProductStructureConstruction,
RPnCupProductStructureFinal, RPnFiltrationCofiber, RPnGeneratorCupNoCup,
RPnGeneratorIdentification, RPnHomologyNotation, RPnSingularCellularCupComparison,
RPnTopClassTransferAssembly, RPnTopClassTransferNonzero}`;
`SphereOddDegree/AlgebraicTopology/{Branch4RPnTopClassTransfer, Branch4TransferAPI,
Branch4TransferNonvanishing, Branch4TransferNonvanishingUnconditional,
Branch4TransferNonzero, Branch4TransferTopClass, Branch4TransferWitness}`.

### Analysis/ChernCommonZeroBridge.lean + Topology/* — 6 files, content-verified DEAD

**Update, re-checked at the lead's request with content, not names, at
origin/main `0927623bcfb7c5ebe7cbc1fe3e4917408dbc14d8`.** Original pass
flagged this cluster as low-confidence DEAD; it is now DEAD with certainty,
and the replacement is named precisely below.

`CommonZeroProperty` (`Topology/TautologicalCommonZero.lean`), verbatim:
`∀ (N : ℕ) (κ : Type) (_ : Finite κ), Nat.card κ ≤ N → ∀ f : TautSection N κ,
∃ z : Fin (N+1) → ℂ, z ≠ 0 ∧ f.toFun z = 0` — sections of a rank-≤N sum of the
tautological line bundle over `ℂPᴺ` have a zero, in homogeneous coordinates.

`Analysis/ChernCommonZeroBridge.lean` has `open TautologicalCommonZero` and
passes its `hprop : CommonZeroProperty` directly to `hasCommonZero_of_property'
hprop`, a theorem declared in `TautologicalCommonZero.lean` with exactly that
argument type — this only type-checks against the identical constant, so the
hypothesis is confirmed to be the *same* Prop, not a same-named one.

`Topology/AntipodalObstructionFromOddDegree.lean` proves
`commonZeroProperty_unconditional : CommonZeroProperty` with zero leading
hypotheses. Checked this is a real gate, not a docstring claim: read
`Meta/AxiomGuard.lean`'s implementation — `#audit_closed_axioms` calls Lean's
own `collectAxioms` on the elaborated term and separately rejects any
declaration whose type has a leading Pi-binder (`stripMData ci.type
|>.isForall`), calibrated against a working/failing pair at the bottom of that
file. Read the full 3-file proof chain (`TautologicalAntipodal.lean`,
`OddMapNormalization.lean`, `AntipodalObstructionFromOddDegree.lean`)
end to end: no sorry, no hidden hypothesis. Its Step 1 applies
`@ThirdParty.HamSandwich.SphereOddDegree.complexOddMapCommonZero` directly —
itself a **reachable, landed**, separately `#audit_closed_axioms`-gated theorem
(`ComplexOddMapCommonZero.lean:80`, `complexOddMapCommonZero_closed`).

**Why DEAD, verified rather than inferred**: the wired XXII endpoint does not
need `CommonZeroProperty` — it gets its topological input a completely
different way, confirmed by reading the actual dependency chain:

* `Analysis/STW22AntipodalBlockData.lean` (landed) independently *defines its
  own* copy of the topological input, `GroupApproximation.STW22.ComplexOddMapCommonZero`
  (line 34) — same shape, stated directly for `C(Sphere d, κ → ℂ)`, no
  tautological bundle, no `ℂPᴺ`.
* `Analysis/STW22UnconditionalCore.lean` proves
  `complexOddMapCommonZero_unconditional : ComplexOddMapCommonZero` (line ~30)
  from the *same base theorem* `ThirdParty.HamSandwich.SphereOddDegree.complexOddMapCommonZero`,
  then feeds it straight into `antipodalCoordinateStateBlockData hBU`
  (`STW22AntipodalBlockData.lean:284`), which calls
  `antipodalWitness_arbitrarilyLateCoordinateStateConstraints hBU` for the
  "simultaneous zero" witness the block construction needs — via
  `simultaneousOffDiagonalMap` (`AntipodalBlockOffDiagonal.lean:92`). Grepped
  that file, `STW22AntipodalBlockData.lean`, and `STW22UnconditionalCore.lean`
  for `TautSection`/`TautologicalCommonZero`/`CommonZeroProperty`: zero hits.
  This route never touches the Chern-class/tautological-bundle vocabulary.
* Corroborating: `ChernCompressionMatrix.norm_sub_sum_selfCommutator_ge_one`
  (the finite-dim inequality `ChernCommonZeroBridge` specializes) has exactly
  **one** consumer in the whole repo — `ChernCommonZeroBridge.lean` itself, the
  orphan. It's wired at root (line 1114, direct import) but functionally
  dead-ended: nothing reachable ever calls it. The landed route proves the
  analogous fact (`trivialLineState_selfCommutator_eq_zero_of_offDiagonal`,
  `STW22AntipodalBlockData.lean:44`) with completely different, block-specific
  machinery, never routing through matrix compression at all.

So two independent, complete, sorry-free derivations of the same underlying
Borsuk–Ulam content exist in this tree, both bottoming out at the identical
base theorem. One (bespoke, direct, block-specific) is wired and is the actual
proof. The other (general Chern-class/tautological-bundle route — the
*original* plan per the audit doc's §2, which derives (A2) via "the top Chern
class of `L^{⊕k}`") was completed later and never connected, not because it's
broken but because a more direct route got there first.

**Replaced by, precisely**: `GroupApproximation.STW22.complexOddMapCommonZero_unconditional`
(`Analysis/STW22UnconditionalCore.lean`) + `antipodalCoordinateStateBlockData`
/ `antipodalWitness_arbitrarilyLateCoordinateStateConstraints`
(`Analysis/STW22AntipodalBlockData.lean`), both landed, both feeding the wired
`antipodal_stw22_trace_problem_counterexample`.

**Separate, smaller flag**: `Analysis/ChernCompressionMatrix.lean` is wired at
root (line 1114) but — per the point above — functionally unused: its only
consumer anywhere in the repo is the orphaned `ChernCommonZeroBridge.lean`.
Not an orphan by the closure definition, but dead weight sitting inside the
closure itself. Your call whether that's worth a separate cleanup pass.

Files: `Analysis/ChernCommonZeroBridge.lean`,
`Topology/{AntipodalObstructionFromOddDegree, OddMapNormalization,
TautologicalAntipodal, TautologicalCommonZero, TautologicalLineWinding}.lean`.

---

## INTENTIONAL (6)

### ThirdParty/FLT/Definitions/Def_Mathlib_Algebra_IsDirectLimit.lean + Analysis/SequentialGroupColimitDirectLimit.lean

Self-documented. `SequentialGroupColimitDirectLimit.lean`'s docstring, verbatim:
*"Not wired into the root import: it imports the vendored slice, which has not
been compiled against this repository's Mathlib pin. See
`ThirdParty/FLT/UPSTREAM.md`."* `ThirdParty/FLT/UPSTREAM.md` confirms: the FLT
vendor tree was trimmed from 2,344 files to this one file on 2026-09-05
specifically because it was inflating orphan/rsync counts elsewhere, and states
"Nothing unpacked here is imported until it compiles against the pin and the
lead wires it."

**Flag, not a misleading-orphan case, but directly relevant to active work**:
this pair is the universal-property infrastructure for
`K₁(A) = colim_n U(Mₙ(A))/U₀(Mₙ(A))` — i.e. this is very likely part of what
Round 13's census entry means by *"only the K_1 gap remains"*
(`155ab89db`). Worth checking against whatever K_1 is currently blocked on
before assuming it's purely a build-pin issue.

### Analysis/FiniteDimensionalFactorialTraceCore.lean

Imports only `Mathlib`. Its own docstring: kernel-checks two *unconditional*
numeric lemmas (stable-range inequality, unbounded replication kills a bounded
trace) toward the finite-dimensional half of XXII, and explicitly disclaims
being a proof of the full statement: *"does not claim a kernel proof of the
full XXII statement."* No consumer, no chain, dated 2026-08-30 (the oldest
orphan in the set) and untouched since. Reads as a standalone sanity artifact,
same genre as the ModelTest files below, just without the `ModelTest` name.

### Analysis/STW22CounterexampleAssemblyModelTest.lean, CuntzPedersenJordanMatrixTest.lean, CuntzPedersenJordanModelTest.lean

All three exist to satisfy the repo's own standing order (verbatim from
`CuntzPedersenJordanModelTest.lean`): *"Repository standing order: every
hypothesis-bearing `Prop` is checked against a concrete instance before it is
used."* Each instantiates hypotheses from a landed, reachable file
(`STW22CounterexampleAssembly.lean`, `CuntzPedersenJordanTracial.lean`) at a
concrete object (`ℂ`, `M₂(ℂ)`) to prove the hypotheses are non-vacuous and
non-trivial. Their job is done by being compiled (`lake build` globs the whole
directory regardless of import wiring) — nothing downstream needs to cite a
model-test result, that's the point of the convention. `MatrixTest` isn't
literally named `*ModelTest` but is the same genre, explicitly the
"noncommutative half" of `CuntzPedersenJordanModelTest`'s test.

---

## WIRE (14)

**Superseded by an actual, comprehensive build-test — read this first.** Lane
`lix-wire` built all 14 WIRE/NEEDS-PROBE candidates as explicit `lake build`
targets (never through the root) and reported results in
`notes/orphan-buildtest-2026-09-07.md` (commit `f604cda72`). That table is now
the authoritative source for compile status and sorry count in this bucket;
everything below is reconciled against it. **10 of 14 compile clean, 4 fail,
and the true sorry count (Lean's own `declaration uses 'sorry'` diagnostic,
not a source grep) is exactly 2, both in one file.**

**Caveat, corrected three times now and load-bearing — read before wiring
anything below.** A WIRE verdict in this report originally meant exactly
three checked claims: *dependencies already in the root closure*, *no
duplicate top-level declaration name*, and *no `sorry`/`admit`/`axiom` token
found by a lexical scan of the file's own source text*. **It never meant
"compiles."** A fourth claim — *building it introduces no new admitted debt
reachable from the root* — was never checked by me, static analysis cannot
check it, and it took two rounds of the lead building this bucket by hand to
find out where that claim held and where it didn't:

* The four STW22 factorial-pair files were wired at `6111d2d08` (accidentally)
  and failed: `STW22TraciallyCompletePair.lean:80` unreferenced `σ`, `:268`
  type mismatch. Unwired at `091795e61`. **Since fixed** — see the TOP
  PRIORITY section below, now retitled FIXED AND CONFIRMED.
* Of the other ten, `KazhdanHypGirthEightGeodesicWord`,
  `KazhdanHypGirthEightGenericProducers`, and `DGOLemma421FourGon` fail;
  `KTheory.Spaces` fails; the remaining six compile clean. Detail for each is
  in its own section below.

**On the `sorry`: confirmed by two independent builds (the lead's isolated
build and `lix-wire`'s explicit-target probe), not a hypothesis.** Lean's own
error-log grep (`grep -n "declaration uses" <log>`, restricted to lines Lean
itself emitted as `error:` under this project's `-DwarningAsError=true`) finds
**exactly 2** occurrences across all 14 files, both in
`GenericProducers.lean` (lines 84, 87). A **lexical grep of source text**
finds **0** in all 14 files, `GenericProducers.lean` included — my original
scan checked for exactly that token and correctly found none, and both builds
independently confirm the file's source truly contains no literal `sorry`.
The log's own line ordering settles the mechanism: the type errors
`lix-wire` isolated (63, 78, 146, 160, 162, 179, 181, 185 — eight sites, more
than either build first reported individually) surround the two `sorry`
diagnostics (84, 87), and all of it sits inside the same handful of
declarations. Lean elaborated failing terms, inserted `sorryAx` to recover,
and reported those declarations as using `sorry`. **Nobody wrote it.** This is
API drift against `VanKampen.CombMapReduction`/`VanKampen.CombMapGluing`, both
actively developed, on a file dated 2026-09-02 — a repair with an owner, not
an admission someone wrote and walked away from. **It does not change what
wiring the file today would do**: `#print axioms`-style tooling would still
report two declarations depending on `sorryAx`, reachable from root, exactly
as first reported.

**General rule, worth carrying past this one file: `declaration uses 'sorry'`
does not imply anyone wrote `sorry`.** Lean emits it whenever a proof term's
kernel closure contains `sorryAx`, including the term the elaborator's own
error-recovery synthesizes after a genuine type error. A `sorry` count taken
purely from build output can therefore *overstate* admitted debt relative to
what an author actually typed, exactly as a lexical `grep` for the token over
source text can *miss* one reached only through a macro or generated code
(not the case here — both counts agree the source has none). Neither number
is the answer alone: the source grep, Lean's own build diagnostic, and the
full error list with its line ordering, together, tell you which kind of debt
is actually present. Two builds and a source grep were needed to settle one
file; budget for that when the next `sorry` count is quoted from either
source alone.

**Compile status and sorry count, all 14, from `lix-wire`'s explicit-target
build (`notes/orphan-buildtest-2026-09-07.md`, commit `f604cda72`), reconciled
with the source-text grep:**

| File | Compiles | Sorry (Lean diagnostic) | Sorry (source grep) |
|---|---|---|---|
| Analysis/STW22FactorialCore.lean | YES | 0 | 0 |
| Analysis/STW22TraciallyCompletePair.lean | YES (fixed `e8e613608`) | 0 | 0 |
| Analysis/STW22AntipodalGaugeFactorial.lean | YES | 0 | 0 |
| Analysis/STW22AntipodalFactorialPair.lean | YES | 0 | 0 |
| Analysis/STW22CounterexampleCompactnessRoute.lean | YES | 0 | 0 |
| Analysis/STW22FibreEvaluation.lean | YES | 0 | 0 |
| GGT/DGOLemma421FourGon.lean | **NO** | 0 | 0 |
| GGT/DGOProposition414SecondSeparationHalfWord.lean | YES | 0 | 0 |
| GGT/HullSCLemma44PrefixKernelCutConstruction.lean | YES | 0 | 0 |
| GGT/KazhdanHypGirthEightGenericProducers.lean | **NO** | **2** (lines 84, 87) | 0 |
| GGT/KazhdanHypGirthEightGeodesicWord.lean | **NO** | 0 | 0 |
| KTheory/Basic.lean | YES | 0 | 0 |
| KTheory/Functorial.lean | YES | 0 | 0 |
| KTheory/Spaces.lean | **NO** | 0 | 0 |

**10 of 14 compile. 4 fail. Total admitted debt introduced by this whole
bucket, if wired as-is: exactly 2 `sorryAx`-dependent declarations, both in
one already-identified, already-diagnosed file.** Every other failure
(`DGOLemma421FourGon`, `GeodesicWord`, `KTheory.Spaces`) is a genuine compile
error with zero sorry involvement — see each file's own section for the
specific cause, none of which is "unfinished mathematics."

Bottom line: **the ten files marked YES above are now confirmed compiling as
explicit targets and are safe to wire; the four marked NO need the fix named
in their own section first.**

## TOP PRIORITY, FIXED AND CONFIRMED — changes what the repository proves, and now compiles

### Analysis/STW22FactorialCore.lean → STW22TraciallyCompletePair.lean → STW22AntipodalGaugeFactorial.lean → STW22AntipodalFactorialPair.lean

**Status: FIXED, confirmed compiling, ready to wire.** Original failure (this
section's history, kept for the record): the lead's clean-export root build
failed with

```
STW22TraciallyCompletePair.lean:80:58: Variable name `σ` is not explicitly
  referenced        (fatal: the lib sets warningAsError=true)
STW22TraciallyCompletePair.lean:268:4: Type mismatch
```

Both were real compile failures, not classification errors — the file's
*content* was always exactly what I read it as (zero sorry, zero axiom, the
missing-conjunct claim below always true as mathematics), it just did not
typecheck against the repository's Mathlib pin / surrounding API as landed.
Unwired at `091795e61`. **Since fixed**, by a separate lane (`xxii-fix`) at
`e8e6136083f66c2bea79e6858add7a5ea7883878`: line 80's unused binder is now
`_σ`; line 268's unification-order failure (a subtype coercion the elaborator
couldn't pattern-match through) is fixed by passing the sequence explicitly.
The fix commit reports the chain green under an isolated probe: *"PROBE
GREEN, 9106 jobs, sorryAx none"*, with both
`antipodal_isFactorialTraciallyCompletePair` and
`antipodalFactorialNegativeSolutionToProblemXXII` reporting axiom closure
`[propext, Classical.choice, Quot.sound]`. Independently confirmed by lane
`lix-wire`'s explicit-target build (`notes/orphan-buildtest-2026-09-07.md`,
`f604cda72`): all four files in the chain compile clean, including
`STW22TraciallyCompletePair` itself and the two files downstream of it that
could only build if it is now sound. **The gap this section describes is real
and the fix is now landed on origin/main — only the root import is
missing.**

**Team lead independently verified the mathematical content** (the missing
conjunct itself, not the compile status) before building. `STW22AntipodalFactorialPair.lean:56`
proves `antipodal_isFactorialTraciallyCompletePair : IsFactorialTraciallyCompletePair
antipodalDesignatedTraces`. The wired endpoint
`antipodal_stw22_trace_problem_counterexample` (`STW22UnconditionalCore.lean:49`)
asserts a seven-clause conjunction and `IsFactorialTraciallyCompletePair` is not
among them. **The repository's current answer to STW Problem XXII refutes
something weaker than the printed problem, and the fix is already proved,
sorry-free, audit-gated, landed on origin/main, and unreachable.** Four files,
zero sorry/admit tokens, seven `#audit` lines between them, dependency chain
`STW22FactorialCore → STW22TraciallyCompletePair → STW22AntipodalGaugeFactorial
→ STW22AntipodalFactorialPair`, with `STW22AntipodalFactorialPair` already
importing `STW22UnconditionalCore` — written to be joined to the endpoint and
never was. This is the one action item in this report that changes a proved
result, not just corpus hygiene; treat it as a priority separate from the
other 10 WIRE items below.

Internal chain (FactorialCore ← TraciallyCompletePair ← AntipodalGaugeFactorial
← AntipodalFactorialPair), all four committed 2026-09-05 16:12–16:44
("xxii:" commits), zero sorry/axiom, `AntipodalGaugeFactorial.lean` and
`AntipodalFactorialPair.lean` both import `Meta.AxiomGuard` (audit-gated).

**This is the one to read closely.** `STW22AntipodalFactorialPair.lean`'s
docstring, verbatim: *"The endpoint asserts unitality, separability,
nuclearity, Type I, the gauge identity, Bauer-ness of the trace simplex,
compact metrizability of its boundary, and injectivity but not surjectivity of
the canonical extension. What it did not assert is the hypothesis of the
problem it refutes: that the pair `(M, X)` is factorial tracially complete.
Dropping a hypothesis makes a counterexample weaker, so without it the
endpoint refutes a weaker statement than STW Problem XXII.
`antipodal_isFactorialTraciallyCompletePair` is the missing conjunct."* That's
the file itself telling you the wired endpoint (`STW22UnconditionalCore`,
confirmed reachable) is provably weaker than the literature statement of
Problem XXII, and that the fix has already been proved and is sitting
unreachable. All four files' own dependencies
(`TraciallyCompleteCStar`, `STW22CanonicalTraceExtension`,
`STW22AntipodalNormComparison`, `STW22DesignatedTraces`, `STW22UnconditionalCore`,
`Meta.AxiomGuard`) are already inside the closure (confirmed by BFS, not
assumed), so this is a pure addition, no other file needs to change.

**Import and position below are unchanged from the original recommendation and
still correct once the file compiles — they are not what failed.** Only the
head of the chain needs adding — `import GroupApproximation.Analysis.STW22AntipodalFactorialPair`
— it pulls the other three transitively. **Position**: root already imports
`STW22NegativeSolution` (line 3416) and `STW22DesignatedTraces` (line 3417)
back to back; insert directly after line 3417, before
`CStarMatrixBlockInclusion`. Every other dependency
(`STW22UnconditionalCore` via `STW22NegativeSolution`,
`STW22AntipodalNormComparison` via `STW22ConditionalNegativeSolution`,
`Meta.AxiomGuard` via the Manuscript block) is already reachable by that point.
**The fix is landed and confirmed by two independent builds — this is now
ready to wire.**

### Analysis/STW22CounterexampleCompactnessRoute.lean, Analysis/STW22FibreEvaluation.lean, and the 5 GGT files below

**Status as of this edit: wired at `20e64a97c` on the same static basis as the
four factorial-pair files above, which failed to compile. A clean-export root
build to confirm these seven specifically is in progress; result not yet
known.** Given what happened to the factorial-pair chain, treat "WIRE" for
these seven as *recommended, unconfirmed* until that build reports back — the
static evidence below (sorry-free, dependencies present, no duplicate names)
is the same kind of evidence that was right about content and wrong about
compiling for the other four.

417 lines, committed 2026-08-31 01:44–02:01 ("Land compactness-route module:
T(A) proper-subset T(M) is a THEOREM"). Proves `T(A) ⊊ T(M)` two independent
ways from one shared lemma (`hasUniformTwoDiscontinuousTracialState_of_detected`):
the route the landed construction actually took
(`_of_compactness`), and a second, Hahn–Banach/Jordan-decomposition route
(`_of_jordan`) the docstring says was *"restored here after the assembly was
re-cut... kept because it is a genuinely different derivation of the same
conclusion, not because anything depends on it."* That's a self-declared
"keep this as a citable alternate," which is exactly the WIRE case — the
module has already decided it wants to exist in the corpus, it just never got
imported. Zero sorry/axiom. Depends on `STW22CounterexampleAssembly.lean` and
`CuntzPedersenJordanTracial.lean`, both already reachable.

**Recommended import**: `import GroupApproximation.Analysis.STW22CounterexampleCompactnessRoute`,
placed after line 1126 (`STW22ActualTraceSpaces`, in the same Analysis block
where `AntipodalHomogeneousBlock` at 1121 and the STW22 cluster already sit —
both of this file's dependencies are reachable by that point).

### Analysis/STW22FibreEvaluation.lean

223 lines, dated 2026-08-31 (a week untouched). Proves
`blockEval_surjective` — every fibre of the antipodal block `D_s` is the full
matrix algebra `M_(s+1)` — which its own docstring quotes as an explicit claim
of *"the STW Problem XXII audit"*. No duplicate declaration anywhere else in
the repo (`blockEval*` greps clean). Depends on `AntipodalHomogeneousBlock.lean`
(reachable, line 1121) and `ThirdParty.HamSandwich.SphereOddDegree.Basic`
(reachable transitively).

**One caveat, worth your judgment call**: the landed Type-I proof for the same
blocks, `STW22RealProjectiveBlockTypeI.lean`, takes a *different* route
(finite generation over the center + topological Schur + Burnside) and its own
docstring says its coordinate generators are *"named locally for the type-I
proof so this module has no dependency on the trace-size computation"* — a
soft signal that `FibreEvaluation`'s approach may have been tried and set
aside for type-I purposes specifically. I'm still calling this WIRE rather than
DEAD because (a) the fact it proves is real, true, and not otherwise proved in
the reachable set, (b) the audit document cites it as a target, and (c) unlike
the Topology/ChernCommonZeroBridge cluster above, nothing here says the two
routes "now rest on one theorem" — there's no explicit convergence claim, just
silence. If you disagree and want it DEAD instead, the topological-Schur
alternative is `STW22RealProjectiveBlockTypeI.lean`.

**Recommended import**: `import GroupApproximation.Analysis.STW22FibreEvaluation`,
same position as CompactnessRoute above (after line 1126).

### GGT/* — 5 files, DGO/Kazhdan lemma pieces — 3 of 5 BROKEN, 2 confirmed compiling

**Status, converged across two builds (the lead's isolated build and
`lix-wire`'s explicit-target probe, `notes/orphan-buildtest-2026-09-07.md`):
3 of these 5 do not compile. The other 2 built clean and stay wired.**

None of these import each other or any other orphan (checked — zero internal
edges among them). Each extends a *reachable* file with real content (not
stubs — 90 to 217 lines each), dated 2026-09-02, and nothing else in the repo
references their declarations (checked by grepping each file's main theorem
names across the whole tree, not just the orphan set — zero hits, so this
isn't a duplicate-content case either).

I flagged lower confidence here than the Analysis items above in the original
pass, and it held up worse than the STW22 chain: I did not cross-check each
against the specific manuscript lemma it claims to serve (DGO Lemma 4.21(b),
Prop 4.14, Hull SC Lemma 4.4, the girth-8 Kazhdan construction) — and it turns
out three of the five don't even build against their own repo as landed,
independent of manuscript fidelity.

- `GGT/DGOLemma421FourGon.lean` — **BROKEN, confirmed independently. My
  "build-graph artifact" hypothesis was tested and REFUTED — recorded here
  as a refuted prediction, not corrected quietly.** I predicted, from a
  transitive-closure argument (zero overlap with what the two Kazhdan
  failures actually touch), that this file was probably fine and had only
  been swept up in a batch-failure report. The lead ran it as a single
  explicit `lake build` target with nothing else in the invocation — the
  exact test I had named as the one that would settle it — and it produced
  eight of its own errors, all in lines 35–79, none inherited:
  `Function expected` at 35, 39; `Unknown identifier
  isGeodesicWord_one_of` at 46, 48; `Type mismatch` at 56, 59; `Application
  type mismatch` at 78, 79. `lix-wire`'s independent explicit-target probe
  confirms the same failure and adds detail: the line-35/39 error is
  specifically `wordDist` reported as an unknown identifier (not merely a
  function-expected mismatch), and a further unknown identifier
  `isQuasiGeodesicPolygon_translate` at line 86. **My closure analysis was
  right about the cause even though my conclusion was wrong**: the one
  dependency this file shares with the broken Kazhdan cluster is
  `OsinGeodesicWord`, and `isGeodesicWord_one_of` is exactly a name this file
  expects `OsinGeodesicWord` to still provide — checked directly,
  `OsinGeodesicWord.lean` no longer has a declaration by that name (it now
  has `exists_relWord`, `existsGeodesicWord`, `sepSet_finite'`). So this is
  the same disease as `GenericProducers` below — bit-rot against a moving
  dependency — contracted from `OsinGeodesicWord` rather than from
  `VanKampen.CombMapReduction`, and the reasoning that identified which
  dependency mattered was sound; only the inference that it hadn't caused a
  break was not. Zero sorry, per both builds. Imports `DGOLemma421Proof`,
  root line 3125. Do not re-wire until the identifier drift against
  `OsinGeodesicWord` is repaired.
- `GGT/DGOProposition414SecondSeparationHalfWord.lean` — **built clean, stays
  wired.** Imports `DGOProposition414SecondSeparationTransport`, root line
  3305.
- `GGT/HullSCLemma44PrefixKernelCutConstruction.lean` — **built clean, stays
  wired.** Imports `HullSCLemma44KernelGeodesicInductionConstruction`, root
  line 3318, and `HullSCLemma44PrefixKernelTransferInduction`, root line 3215.
- `GGT/KazhdanHypGirthEightGenericProducers.lean` — **BROKEN, confirmed
  bit-rot, not admitted debt.** `lix-wire`'s explicit-target build isolates
  eight error sites, not the three or four either earlier build report named
  individually: lines 63, 78, 146, 160, 162, 179, 181 and 185 — type
  mismatches, an argument expecting a `Prop` given a non-`Prop`, and two
  `omega` failures — plus `declaration uses 'sorry'` at lines 84 and 87.
  **Confirmed against the actual build log, not left as a hypothesis**:
  literal grep of the file's own source text finds zero `sorry`/`admit`
  tokens (table above), matching both a hand-read of all 217 lines and the
  lead's own `grep -c sorry` on the source. The log's own line ordering
  settles the mechanism — the type-mismatch sites bracket the two `sorry`
  diagnostics, all within the same two theorems
  (`cactusBaseCellDeletionForPower_of_foldStepSource`,
  `cactusRelatorRetypingForPower_of_foldChainSource`). Lean elaborated a
  failing term, inserted `sorryAx` to recover, and reported the declaration
  as using `sorry` — nobody wrote it. This is API drift against
  `VanKampen.CombMapReduction`/`VanKampen.CombMapGluing`, both actively
  developed, on a file dated 2026-09-02, and it is deeper drift than my first
  reading suggested (eight sites, not three). **This does not change the
  practical bottom line**: wiring the file today would still make
  `#print axioms`-style tooling report two `sorryAx`-dependent declarations
  reachable from root, exactly as first reported — it changes only what kind
  of bug it is (a repair against a moving dependency, with an owner) versus
  what it first looked like. Imports `KazhdanHypGirthEightTorsionExtraction`,
  root line 3168, and `VanKampen.CombMapReduction`/`CombMapGluing`, both
  reachable but not direct root imports.
- `GGT/KazhdanHypGirthEightGeodesicWord.lean` — **BROKEN, confirmed by two
  independent builds.** A single `rewrite` tactic at line 115 fails: the
  pattern `wordDist ?S ?x ?x` is not found in the goal
  `OsinComponents.IsGeodesicWord D x.val x.val word`. Shallow — one error
  site, no sorry — and, per `lix-wire`'s note, the same missing name
  (`wordDist`) that breaks `DGOLemma421FourGon` above, which is worth
  investigating as one shared root cause (drift in how `IsGeodesicWord` and
  `wordDist` relate to each other now, versus when both files were written
  on 2026-09-02) rather than two unrelated breaks, even though each fails
  independently as its own explicit build target. Imports
  `KazhdanHypGirthEightVKInterface`, root line 3118, and `OsinGeodesicWord`,
  root line 2394.

**Net for this section: three files need the same kind of repair (identifier
drift against `OsinGeodesicWord` or `VanKampen.CombMapReduction`/
`CombMapGluing`), not three unrelated deletions or three admissions. See the
general rule at the top of the WIRE section for what the `sorry` count does
and does not mean.**

### KTheory/Basic.lean → Functorial.lean → Spaces.lean — PROBED: 2 of 3 compile, 1 has a one-line fix

**The probe the author asked for has now happened** (`lix-wire`'s
explicit-target build, `notes/orphan-buildtest-2026-09-07.md`), so this is no
longer NEEDS-PROBE for two of the three files.

Chain: `Basic.lean` (imports the reachable `KTheory/BlockMoves.lean`, root
line 3426) builds `K₀` of a `*`-ring in the projection picture;
`Functorial.lean` makes it functorial in the coefficient ring;
`Spaces.lean` specializes to `K⁰(X) := K₀(C(X))` per "`lix-design`'s §B.4".
Zero sorry/axiom in all three (confirmed both by source grep and by the
probe's Lean-diagnostic count). The last commit to this chain
(2026-09-05 16:45:23, "ktheory: hand-build the pullback star ring hom instead
of coercing") is titled, in full: *"ktheory: K0 of a space and its
contravariance -- UNPROBED, do not import yet"* — that caution turns out to
have been **partially warranted, and precisely so**:

- `Basic.lean` — **compiles clean.** Safe to wire on its own.
- `Functorial.lean` — **compiles clean.** Safe to wire (pulls in `Basic`).
- `Spaces.lean` — **fails, shallow and specific**: line 43 defines something
  that needs `noncomputable` because it transitively depends on
  `instCommCStarAlgebraComplex`, itself noncomputable. This is the ordinary,
  one-keyword fix for this exact Lean message (`noncomputable def` /
  `noncomputable instance`) — not a sorry, not a type-theoretic gap, not drift
  against a moved dependency. It reads like the file was written and never
  run through the compiler even once, which is exactly what "UNPROBED" said
  it was. Note also: there is a *separate*, already-landed K-theory apparatus
  under `Analysis/` (`KKTheoryKGroups.lean`, `KKTheoryKasparov.lean`,
  `KasparovBimodule.lean`, `UniversalCoefficientTheorem.lean`,
  `CStarKOneWhitehead.lean`) built on KK-theory/Kasparov modules rather than
  the elementary projection picture here — whether that makes this chain
  redundant is a judgment call a compiler cannot answer, unchanged from the
  original report.

**Recommended import**: `import GroupApproximation.KTheory.Functorial` now
(pulls in `Basic`), inserted after line 3426 (`KTheory.BlockMoves`, its
transitive dependency) — both compile clean and are safe to wire today.
`Spaces` should follow once someone adds `noncomputable` at line 43 and
confirms the fix compiles; at that point the single import becomes
`import GroupApproximation.KTheory.Spaces` in the same position, which
transitively pulls in the other two.

---

## Build status of the WIRE bucket (final, reconciled with `lix-wire`'s explicit-target probe)

| Files | Status | Compiles? |
|---|---|---|
| STW22FactorialCore/TraciallyCompletePair/AntipodalGaugeFactorial/AntipodalFactorialPair (4) | broke main at `6111d2d08`, unwired `091795e61`, **fixed at `e8e613608`** | **YES**, confirmed by two builds — ready to wire |
| STW22CounterexampleCompactnessRoute, STW22FibreEvaluation, DGOProposition414SecondSeparationHalfWord, HullSCLemma44PrefixKernelCutConstruction (4) | wired `20e64a97c` | **YES**, confirmed, stay wired |
| KazhdanHypGirthEightGenericProducers, KazhdanHypGirthEightGeodesicWord, DGOLemma421FourGon (3) | wired `20e64a97c`, unwired `dcee3ff04` | **NO** — each is API drift against a moved dependency (`VanKampen.CombMapReduction`/`CombMapGluing` for the first, `OsinGeodesicWord` for the other two); GenericProducers additionally has 2 compiler-reported `sorryAx` recoveries from its own type errors, not hand-written admissions — see GGT section |
| KTheory.Basic, KTheory.Functorial (2) | not wired | **YES**, confirmed — safe to wire now |
| KTheory.Spaces (1) | not wired | **NO** — one missing `noncomputable` keyword, line 43 |

**Final tally: 10 of 14 wired-or-tested files compile clean, 4 do not. Every
failure has a named, specific cause** (API drift against two dependencies, or
one missing keyword) **and none is unfinished mathematics** — the corpus's
admitted-debt count from wiring this entire bucket, once the four are fixed,
would be exactly what it is today. WIRE in this report always meant "has its
dependencies, no duplicate declarations, no literal sorry/admit token in its
own source" — three checked claims, not "compiles" — see the caveat at the
top of the WIRE section for the full statement and for why a lexical scan
cannot see a compiler-synthesized `sorry`.

## Summary table

| Bucket | Count | Files |
|---|---|---|
| DEAD | 81 | AlgTop/* (46), ThirdParty/HamSandwich Branch3/4 (27), LIXObstruction{Contradiction,LowPowerSums} (2), ChernCommonZeroBridge + Topology/* (6) |
| INTENTIONAL | 6 | FLT vendor pair (2), FiniteDimensionalFactorialTraceCore (1), ModelTest/MatrixTest trio (3) |
| WIRE | 14 | STW22 factorial-pair chain (4, FIXED, confirmed compiling), STW22CounterexampleCompactnessRoute + STW22FibreEvaluation (2, confirmed compiling), GGT/* (5: 2 confirmed compiling, 3 BROKEN — API drift, named cause each), KTheory/* (3: Basic + Functorial confirmed compiling, Spaces needs one `noncomputable` keyword) |

No file was deleted or edited by this lane. `GroupApproximation.lean` was not
touched by this lane at any point — the lead wired and unwired it directly
(`6111d2d08`, `20e64a97c`, `091795e61`, `dcee3ff04`) and a separate lane
(`xxii-fix`) fixed and lane `lix-wire` build-tested the bucket
(`e8e613608`, `notes/orphan-buildtest-2026-09-07.md`), per the "Build status"
note above.
