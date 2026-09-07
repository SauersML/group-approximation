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

### Analysis/ChernCommonZeroBridge.lean + Topology/* — 6 files, the second flag item

This cluster proves the **XXII counterexample's Chern-class input** — the same
territory the landed proof covers a different way. Chain (confirmed by reading
each file, not just import lines):

- `Topology/TautologicalCommonZero.lean` states `CommonZeroProperty` as a named
  closed `Prop` — the exact statement `research/artifacts/stw22-trace-problem-counterexample-audit-2026-08-31.md`
  §2 calls **"the proof"**: sections of `L^{⊕s}` over `ℂP^{s²}` have a common
  zero.
- `Analysis/ChernCommonZeroBridge.lean` takes it as a **hypothesis**
  (`hprop : CommonZeroProperty`) and derives the audit's inequality (A2)
  conditionally on it.
- `Topology/TautologicalAntipodal.lean`, `Topology/OddMapNormalization.lean`,
  `Topology/TautologicalLineWinding.lean` build the Borsuk–Ulam bridge.
- `Topology/AntipodalObstructionFromOddDegree.lean` **discharges
  `CommonZeroProperty` unconditionally** (`commonZeroProperty_unconditional`),
  feeding off the now-landed odd-degree theorem, and is itself audit-gated
  (`#audit_closed_axioms` on both endpoints — commit message: *"topology: gate
  both antipodal endpoints with #audit_closed_axioms"*, 2026-09-05 15:53).

So the closer and the user of the same named gap are both orphaned, and the
closer never got imported into the user. **Why DEAD and not WIRE**: the
closer's own docstring says *"Step 1's endpoint is the same theorem that
`GroupApproximation.STW22.complexOddMapCommonZero_unconditional` ...
consumes on the operator-algebraic side of the counterexample ... so the two
routes now rest on one theorem"* — i.e. the actually-landed XXII refutation
(`STW22UnconditionalCore`/`STW22NegativeSolution`, confirmed reachable) goes
through the operator-algebraic route directly and never needed the Chern-class/
tautological-bundle vocabulary at all. This is a complete, high-quality,
audit-gated *alternative* proof of a fact the corpus already has by another
road, not a hole in the landed proof.

**I flagged this to you before writing it up because I'm not fully confident
DEAD is right** — unlike `STW22CounterexampleCompactnessRoute` (which
self-declares "kept... not because anything depends on it"), this cluster's
docstring reads as *converging* toward one shared theorem, not as a
deliberately-preserved alternate. If the operator-algebraic route ever needs
review, this is a second, independent, sorry-free proof of the same audit
requirement sitting ready. Worth a second look before treating it as settled.

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

### Analysis/STW22FactorialCore.lean → STW22TraciallyCompletePair.lean → STW22AntipodalGaugeFactorial.lean → STW22AntipodalFactorialPair.lean — the first flag item

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

**Recommended import**: only the head of the chain needs adding —
`import GroupApproximation.Analysis.STW22AntipodalFactorialPair` — it pulls the
other three transitively. **Position**: root already imports
`STW22NegativeSolution` (line 3416) and `STW22DesignatedTraces` (line 3417)
back to back; insert directly after line 3417, before
`CStarMatrixBlockInclusion`. Every other dependency
(`STW22UnconditionalCore` via `STW22NegativeSolution`,
`STW22AntipodalNormComparison` via `STW22ConditionalNegativeSolution`,
`Meta.AxiomGuard` via the Manuscript block) is already reachable by that point.

### Analysis/STW22CounterexampleCompactnessRoute.lean

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

### GGT/* — 5 files, DGO/Kazhdan lemma pieces

None of these import each other or any other orphan (checked — zero internal
edges among them). Each extends a *reachable* file with real content (not
stubs — 90 to 217 lines each), dated 2026-09-02, and nothing else in the repo
references their declarations (checked by grepping each file's main theorem
names across the whole tree, not just the orphan set — zero hits, so this
isn't a duplicate-content case either).

I flag lower confidence here than the Analysis items above: I did not
cross-check each against the specific manuscript lemma it claims to serve
(DGO Lemma 4.21(b), Prop 4.14, Hull SC Lemma 4.4, the girth-8 Kazhdan
construction) to confirm the assembling theorem still needs this exact piece
rather than having closed a different way — that would need reading four
separate large lemma developments end to end, which I didn't have room for.
Recommend at least a spot-check before wiring blind.

- `GGT/DGOLemma421FourGon.lean` (imports `DGOLemma421Proof`, root line 3125) —
  insert after 3125.
- `GGT/DGOProposition414SecondSeparationHalfWord.lean` (imports
  `DGOProposition414SecondSeparationTransport`, root line 3305) — insert after
  3305.
- `GGT/HullSCLemma44PrefixKernelCutConstruction.lean` (imports
  `HullSCLemma44KernelGeodesicInductionConstruction`, root line 3318, and
  `HullSCLemma44PrefixKernelTransferInduction`, root line 3215) — insert after
  3318 (the later of the two).
- `GGT/KazhdanHypGirthEightGenericProducers.lean` (imports
  `KazhdanHypGirthEightTorsionExtraction`, root line 3168, and
  `VanKampen.CombMapReduction`/`CombMapGluing`, both reachable but not direct
  root imports) — insert after 3168.
- `GGT/KazhdanHypGirthEightGeodesicWord.lean` (imports
  `KazhdanHypGirthEightVKInterface`, root line 3118, and `OsinGeodesicWord`,
  root line 2394) — insert after 3118.

### KTheory/Basic.lean → Functorial.lean → Spaces.lean — needs a build probe, not a confident WIRE

Chain: `Basic.lean` (imports the reachable `KTheory/BlockMoves.lean`, root
line 3426) builds `K₀` of a `*`-ring in the projection picture;
`Functorial.lean` makes it functorial in the coefficient ring;
`Spaces.lean` specializes to `K⁰(X) := K₀(C(X))` per "`lix-design`'s §B.4".
Zero sorry/axiom. **But** the last commit to this chain
(2026-09-05 16:45:23, "ktheory: hand-build the pullback star ring hom instead
of coercing") is titled, in full: *"ktheory: K0 of a space and its
contravariance -- UNPROBED, do not import yet."* That's the author's own
instruction, not my inference. I'm not overriding it. Per your rules I'm not
building anything myself — flagging that this needs a probe build before
anyone wires it, and after 2 days untouched it's worth finding out whether it
was probed and forgotten, or abandoned. Note also: there is a *separate*,
already-landed K-theory apparatus under `Analysis/` (`KKTheoryKGroups.lean`,
`KKTheoryKasparov.lean`, `KasparovBimodule.lean`,
`UniversalCoefficientTheorem.lean`, `CStarKOneWhitehead.lean`) built on
KK-theory/Kasparov modules rather than the elementary projection picture here
— I did not find evidence either way on whether that made this chain
redundant; that's part of what the probe should settle.

**If it probes clean, recommended import**: `import GroupApproximation.KTheory.Spaces`
(pulls in `Functorial` and `Basic`), inserted after line 3426
(`KTheory.BlockMoves`, its transitive dependency).

---

## Summary table

| Bucket | Count | Files |
|---|---|---|
| DEAD | 81 | AlgTop/* (46), ThirdParty/HamSandwich Branch3/4 (27), LIXObstruction{Contradiction,LowPowerSums} (2), ChernCommonZeroBridge + Topology/* (6) |
| INTENTIONAL | 6 | FLT vendor pair (2), FiniteDimensionalFactorialTraceCore (1), ModelTest/MatrixTest trio (3) |
| WIRE | 14 | STW22 factorial-pair chain (4), STW22CounterexampleCompactnessRoute + STW22FibreEvaluation (2), GGT/* (5), KTheory/* (3, pending probe) |

No file was deleted or edited. `GroupApproximation.lean` was not touched.
