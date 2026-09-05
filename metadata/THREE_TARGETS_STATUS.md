# The three STW targets: verification status

Lane `audit-gate`.  This file is the verification lane's record for the
2026-09-05 campaign of `notes/STW_THREE_TARGETS_PROGRAM_2026-09-05.md`.  It
carries, per target, the endpoint declaration and its full statement quoted
from source, its axiom report, the named `Prop`s and literature packages
reachable **from the statement** (the test the literature quarantine applies —
see `metadata/LITERATURE_QUARANTINE.md`), and a one-line verdict.

A verdict of UNCONDITIONAL here means three separate things, and this file
keeps them apart, because in this repository they fail independently:

* **stated** — the endpoint exists, its statement is the problem, and the
  statement reaches no named residue and no literature package;
* **closed** — `#audit_closed_axioms` reports `propext / Classical.choice /
  Quot.sound` and no leading binder;
* **compiled** — a build actually elaborated the module *at the current
  source*.  An `#audit` macro reads oleans, so a stale artifact reports on
  code that no longer exists, and an orphan module is never elaborated by a
  default build at all.

---

## Baseline, 2026-09-05 (taken before the wave lands anything)

Working tree at `3dc8e20d8`, plus two files a lane is editing
(`SphereOddDegree/BorsukUlam.lean`, `SphereOddDegree/ComplexOddMapCommonZero.lean`)
and one untracked driver (`scripts/ProblemXVerify.lean`).

Python gates, run locally, with their **counts** (a gate that checked zero
items also exits 0):

| gate | exit | count it reports |
|---|---|---|
| `scripts/check_non_mf_unconditional.py` | 0 | 36 cited declarations unconditional |
| `scripts/check_ledger_unconditional.py` | 0 | 136 classified, 0 not found, 0 conditional |
| `scripts/check_manuscript_claims.py` | 0 | passes; 15 line-number-citation warnings |
| `scripts/check_import_regression.py` | 0 | 3263 modules imported, **no new orphans** |
| `scripts/check.py --list-orphans` | — | **235 orphan modules** |

Orphan baseline, 235 modules, of which **196 are
`ThirdParty.HamSandwich.*`** (the vendored port, including its root
`GroupApproximation.ThirdParty.HamSandwich`).  The 39 non-HamSandwich orphans
include the entire XXII endpoint chain and the entire `Topology.Tautological*`
family; the full list is reproduced in the target sections below.

Lexical `sorry`/`admit`/`axiom`/`opaque` scan over `GroupApproximation/`,
`STW/`, `STWProblems.lean`, `scripts/*.lean`: **7 real `sorry`s, all in one
module**, `GroupApproximation/Manuscript/NonMF/TheoremCAssembly.lean` at lines
142, 200, 213, 243, 252, 259, 378.  That module belongs to the non-MF
manuscript and is **not** on any of the three targets' dependency paths; it is
recorded here so that a later reading of a clean scan is not mistaken for a
change.  Every other hit is the word inside a docstring.

---

## Target 1 — STW Problem X(1): is every amenable trace quasidiagonal?  **No.**

### Endpoint

`GroupApproximation.NinetyNineProblems.not_problemX1Statement`, in
`GroupApproximation/Manuscript/NinetyNineProblems/ProblemX.lean:287`.

```lean
theorem not_problemX1Statement : ¬ ProblemX1Statement.{1} :=
  not_problemX1Statement_of_literalFactorizationProperty
    literalFactorizationProperty
```

with, at `ProblemX.lean:105`,

```lean
def ProblemX1Statement : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] (τ : TracialState A),
    Quasidiagonal.IsAmenableTrace (fun a : A ↦ τ a) →
      Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a)
```

### Statement closure

Unfolding the statement (not the proof) reaches, inside `GroupApproximation`:

* `NinetyNineProblems.ProblemX1Statement`
* `Quasidiagonal.IsAmenableTrace` → `Quasidiagonal.AmenableTraceModel`
  (`Analysis/TikuisisWhiteWinterCore.lean:106`) → `FiniteModel`,
  `IsCompletelyPositiveOnMatrices`, `hsNorm`, `normTrace`
* `Quasidiagonal.IsQuasidiagonalTrace` → `Quasidiagonal.QuasidiagonalTraceModel`
  (`Analysis/QuasidiagonalTrace.lean:204`) → the same four

Both model structures are transcriptions of Brown's two definitions with no
hypothesis fields; the two differ in exactly one clause (`hsNorm` vs operator
norm).  **No entry of `literaturePackages` is reachable from the statement.**
In particular `QuasidiagonalMF.TikuisisWhiteWinterInput` is *not* reachable:
X(1) is the converse of TWW, and the endpoint refutes it rather than consuming
it.

`ProblemX1Statement` is universe-polymorphic and the endpoint pins it at
`.{1}`, which is forced: `MarkedGroup : Type` and `MaximalGroupCStar` raises
the level, so `C⋆(E) : Type 1`.  A reader should note this is a refutation of
the universe-1 instance, which is the strongest form available.

The witness group is concrete: `Sofic.LiteralNonMFPresentation.MarkedGroup`, a
finite presentation on `Fin 6 ⊕ Fin 2` (8 generators), not a group produced by
any universal-embedding citation.

### Axiom report

Declared in-source at `ProblemX.lean:296–305`:

```
#audit_axioms ProblemX1Statement
#audit_axioms LiteralFactorizationProperty
#audit_axioms isHyperlinearTrace_of_isAmenableTrace
#audit_closed_axioms literalCanonicalTrace_isHyperlinearTrace
#audit_closed_axioms literalCanonicalTrace_not_isQuasidiagonalTrace
#audit_closed_axioms literalCanonicalTrace_hyperlinear_not_quasidiagonal
#audit_closed_axioms literalFactorizationProperty
#audit_axioms not_problemX1Statement_of_literalFactorizationProperty
#audit_closed_axioms not_problemX1Statement
```

`#audit_closed_axioms` both rejects a leading binder and fails the build on any
axiom outside `propext / Classical.choice / Quot.sound`, so these lines are a
build-failing gate rather than a printed report — **at whatever source the
olean was built from**.  Baseline: not re-probed by this lane yet.

### Compilation status

`ProblemX.lean` is **in the root import closure** (absent from
`--list-orphans`), so a default build does elaborate it and does run those nine
audit lines.  This is the only one of the three targets of which that is true.

### Verdict

**UNCONDITIONAL (stated + closed), pending an independent statement-closure
run.**  The remaining check is mechanical and lane `brown-x1-verify` is
running it: `scripts/Audit.lean`'s quarantine walk is seeded at
`headlineTheorems ++ zeroInputEndpoints`, and **no `NinetyNineProblems` name is
on either roster**, so nothing in the corpus currently asks whether
`not_problemX1Statement` states a citation.  Until that driver runs, the
statement-closure claim above is this lane's reading of the source, not a
machine check.

---

## Target 2 — STW Problem XXII: the trace problem for factorial tracially complete C\*-algebras.  **No.**

Problem XXII (= Question 1.1 of CCEGSTW, arXiv:2310.20594): *for a factorial
tracially complete `(M, X)`, is every trace on `M` uniform-2-norm continuous?*

### Endpoint

`GroupApproximation.STW22NegativeSolution.negativeSolutionToProblemXXII`, in
`GroupApproximation/Analysis/STW22NegativeSolution.lean:50`.

```lean
theorem negativeSolutionToProblemXXII :
    Nonempty (CStarAlgebra AntipodalCounterexampleAlgebra) ∧
      TopologicalSpace.SeparableSpace AntipodalCounterexampleAlgebra ∧
      IsNuclearCStarAlgebra AntipodalCounterexampleAlgebra ∧
      STW22.IsTypeI.{0, v} AntipodalCounterexampleAlgebra ∧
      (∀ x : AntipodalCounterexampleAlgebra,
        STW22BaseUniformTracialGauge.baseTracialTwoSize x =
          UniformTracialSequenceCompletion.uniformTwoNorm
            antipodalAllTracesGauge x.1) ∧
      Set.Nonempty antipodalWeakStarTraceSimplex ∧
      IsBauerSimplex ℝ≥0 antipodalWeakStarTraceSimplex ∧
      (CompactSpace AntipodalWeakStarExtremeBoundary ∧
        MetrizableSpace AntipodalWeakStarExtremeBoundary) ∧
      Function.Injective (canonicalExtension
        antipodalAllTracesGauge_isCoordinateNormComparison) ∧
      ¬ Function.Surjective (canonicalExtension
        antipodalAllTracesGauge_isCoordinateNormComparison) := ...
```

with `#audit_closed_axioms negativeSolutionToProblemXXII` on the following
line, and `abbrev AntipodalCounterexampleAlgebra := BaseAlgebra
AntipodalCounterexampleBlock`.

The non-surjectivity conjunct is the negative answer, via
`STW22CounterexampleCompactnessRoute.isExtensionOfSomeBaseFunctional_iff`: a
trace of the completion is in the image of `T(A)` **iff** it is
uniform-2-norm continuous.

### Statement closure

The statement reaches no `literaturePackages` entry, and — importantly — it
does **not** mention `TautologicalCommonZero.CommonZeroProperty`,
`TautologicalAntipodal.AntipodalObstruction`, or
`STW22AntipodalBlockData.ComplexOddMapCommonZero`.  The topological input
enters through the **proof**, via
`STW22UnconditionalCore.antipodalCoordinateStateBlockDataUnconditional`, which
is `antipodalCoordinateStateBlockData complexOddMapCommonZero_unconditional`.
That is the correct shape.

`complexOddMapCommonZero_unconditional : ComplexOddMapCommonZero`
(`STW22UnconditionalCore.lean:32`) is a genuine theorem, discharged by
`ThirdParty.HamSandwich.SphereOddDegree.complexOddMapCommonZero`, which runs
`borsuk_ulam` on the realification.  `borsuk_ulam` runs
`no_odd_map_sphere_succ`, which runs
`odd_degree_of_odd_sphere_self_map_unconditional`
(`SphereOddDegree/Final/OddDegreeTheoremUnconditional.lean:35`), which takes
`hn : 1 ≤ n` and a map, and **no** cellular/comparison/top-class datum.  The
seven genuinely conditional root assumptions of the port
(`ModTwoTopClassComparison`, `RPnGeneratorIdentification`,
`RPnTopPowerIdentification`, `RPnCellularCochainStructure`,
`RPnTopClassTransfer`, `RPToSphereTransferTopNonzero`,
`TopHomologyTransferNonzeroWitness`) are deliberately **not** aliased into the
`final_*` namespace, per
`SphereOddDegree/Final/FinalAssumptionAliases.lean`, and are not on the
`odd_degree_of_odd_sphere_self_map_unconditional` path.

So on a source reading the XXII chain is unconditional.  **Two problems
remain, and they are not small.**

### Problem 2A — the load-bearing half of the chain is orphan, so it has never been compiled

Parsing the `import` lines transitively from the endpoint: the closure is
**443 project modules** (plus 186 Mathlib leaves), it is **acyclic**, and
**190 of the 443 are orphan** — outside the root import closure, so a default
build never elaborates them.  253 are already root-reachable.

The 190 split as **169 `ThirdParty.HamSandwich.SphereOddDegree.*`** (the
vendored Borsuk–Ulam port) and these 21:

```
GroupApproximation.Analysis.STW22NegativeSolution          <- the endpoint itself
GroupApproximation.Analysis.STW22UnconditionalCore
GroupApproximation.Analysis.STW22AntipodalTraceSimplexBauer
GroupApproximation.Analysis.STW22AntipodalBaseBoundaryMeasure
GroupApproximation.Analysis.STW22AntipodalBaseCoordinateMeasures
GroupApproximation.Analysis.STW22AntipodalBlockComplexCenter
GroupApproximation.Analysis.STW22AntipodalBlockMeasureTrace
GroupApproximation.Analysis.STW22AntipodalBlockTraceAffineEquiv
GroupApproximation.Analysis.STW22AntipodalBlockTraceClassification
GroupApproximation.Analysis.STW22AntipodalBlockTraceMeasure
GroupApproximation.Analysis.STW22AntipodalBoundaryComponents
GroupApproximation.Analysis.STW22AntipodalBoundaryMeasureRoundTrip
GroupApproximation.Analysis.STW22AntipodalBoundaryMeasureTrace
GroupApproximation.Analysis.STW22AntipodalBoundaryTraceFunction
GroupApproximation.Analysis.STW22AntipodalCoordinateRestriction
GroupApproximation.Analysis.STW22AntipodalFiniteBoundaryMeasure
GroupApproximation.Analysis.STW22AntipodalNormComparison
GroupApproximation.Analysis.STW22AntipodalTraceMeasureInverse
GroupApproximation.Analysis.STW22AntipodalTraceSimplexIntegration
GroupApproximation.Analysis.STW22BauerSimplexImage
GroupApproximation.Analysis.TracialStateWeakStarTopology
```

A further 8 orphans sit beside the path but are *not* in it —
`STW22CounterexampleCompactnessRoute`, `STW22CounterexampleAssemblyModelTest`,
`STW22FibreEvaluation`, `ChernCommonZeroBridge`,
`FiniteDimensionalFactorialTraceCore`, and the three `Topology.Tautological*`
modules.  Reading a lemma out of one of those (for instance
`isExtensionOfSomeBaseFunctional_iff`, which is the cleanest statement in the
tree of *why* non-surjectivity is the negative answer) does **not** put it on
the endpoint's path.  On the endpoint's own path the same bridge is
`STW22CanonicalTraceExtension.canonicalExtension_not_surjective_of_not_every`
together with `canonicalExtension_isContinuousExtension`, and it is there.

A default build never elaborates the 190, so
`#audit_closed_axioms negativeSolutionToProblemXXII` has never fired against a
green build, and neither has the port's own audit.  "The build is green" says
nothing whatever about target 2 today.  `check_import_regression.py` itself
prints, of the same list, *"These still fail the Source scan, so no certificate
passes until they are wired or deleted."*

**What would settle it:** an explicit `scripts/remote-build.sh
GroupApproximation.Analysis.STW22NegativeSolution` whose job count moves.  Not
attempted at baseline — the two HamSandwich lanes are mid-port and the module
is not expected to build yet.

### Problem 2B — the endpoint never says "factorial", and never says "tracially complete"

This is the substantive audit finding on target 2, and it is raised for the
`xxii-assembly` lane by name.

Problem XXII is a question **about factorial tracially complete pairs**.  A
counterexample has to exhibit such a pair.  The conclusion of
`negativeSolutionToProblemXXII` lists unitality, separability, nuclearity, Type
I, a gauge identity, Bauer-ness of the weak-\* trace simplex, compact
metrizability of its boundary, and injectivity-but-not-surjectivity of
`canonicalExtension`.  It does not assert that the pair
`(M, X)` it produces is factorial, and the word "factorial" does not occur in
any XXII Lean module (`FiniteDimensionalFactorialTraceCore.lean` has it in its
*name* and its docstring, and that file's own docstring says it "does not claim
a kernel proof of the full XXII statement"). There is no Lean definition of
`Factorial` or of `TraciallyComplete` anywhere in the corpus.

Two readings, and the lane has to say which:

1. factoriality is *implied* by the conjuncts already there — plausibly by
   `IsBauerSimplex` together with the centre computation in
   `STW22AntipodalBlockComplexCenter`, which would make the pair a W\*-bundle
   over `∂_e X` with factor fibres.  If so the implication is a theorem and it
   should be a named conjunct of the endpoint, not an unstated identification;
2. it is not established, in which case the endpoint refutes a *weaker*
   statement than Problem XXII and must not be advertised as XXII.

Until one of those is written down, the endpoint's name is a stronger claim
than its type.

### Verdict

**CONDITIONAL-ON-COMPILATION and CLAIM-UNMATCHED.**  Source-unconditional (no
literature package, no named residue reachable from the statement, the
common-zero input discharged by a proved Borsuk–Ulam), but (a) the entire
chain, including the 196-module vendored port it rests on, is orphan and has
never been elaborated, and (b) the conclusion does not state the factoriality
hypothesis of the problem it is named for.

The residue named in the campaign brief — `CommonZeroProperty` — is **not**
the live gap: `Topology/TautologicalCommonZero.CommonZeroProperty` and
`Topology/TautologicalAntipodal.AntipodalObstruction` are a *separate,
still-open* formulation used by `Analysis/ChernCommonZeroBridge`, and the
assembly that reaches `negativeSolutionToProblemXXII` goes through
`STW22AntipodalBlockData.ComplexOddMapCommonZero` instead, which is proved.
Of the `Tautological*` family only the rank-one case is proved
(`TautologicalLineWinding.hasCommonZero_one_one`); `AntipodalObstruction`
itself is unproved, and `not_antipodalObstruction_succ` shows only that its
rank bound is sharp — it refutes the `card κ ≤ N + 1` relaxation, **not**
`AntipodalObstruction`.  That distinction is easy to misread from the name and
is recorded here so nobody reports the residue as refuted.

---

## Target 3 — STW Problem LIX: are all unital simple C\*-algebras `K₁`-injective?  **No.**

### Endpoint

**None.**  There is no Lean declaration.

### Statement closure

Not applicable.

### Axiom report

Not applicable.

### Compilation status

Baseline search for Lean carrying this target — modules named for `K1`,
`K1Injective`, `CP^d`, clutching, or `stw59` — returns nothing outside
`research/`.  The proof exists only as prose, in
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`
and its neighbours.

### Verdict

**NOT-YET-STATED.**  Six lanes (`lix-design`, `lix-spaces`, `lix-clutching`,
`lix-obstruction`, `lix-limit`, `ktheory-k1`) are building it from zero.  The
first thing this file will want from them is the named `Prop` that *is* the
problem — `∀ A, [unital] → [simple] → K₁-injective` — stated before anything
is proved about it, so that the endpoint can be checked against a statement
nobody wrote after the fact.

---

## Ways a green could be lying here, and where each is checked

| failure mode | where it bites in this campaign | check |
|---|---|---|
| `#audit` reads oleans, not source | every `#audit_closed_axioms` in an orphan module | job count must move on a real change; `remote-build.sh <Module>` by name |
| a gate that certifies nothing | `check_ledger_unconditional` (136), `check_non_mf_unconditional` (36) | counts recorded above; a drop is the signal, not the exit code |
| orphan module never compiled | **235 modules**, including all of targets 2 and the port | orphan list snapshotted above; re-run and diff |
| lexical `sorry`/`axiom` | new campaign modules | 7 known `sorry`s, all in `NonMF/TheoremCAssembly.lean`, off all three paths |
| import cycle invisible to a probe | the 196-module port being rewired by two lanes | parse `import` lines of the campaign modules, check acyclic |
| residue closed by restating it | a lane replacing a named `Prop` by a definition that unfolds to it | statement-closure column above, per target |
| endpoint drops the problem's hypothesis | **target 2: "factorial" is absent** | flagged as Problem 2B |

---

# Wave log

Each entry is a re-run of the same sweep, so the numbers are comparable.  What
matters in a row is the **count**, not the exit code.

## Sweep 2, 2026-09-05 (first landings)

`scripts/check_import_regression.py` is now **RED (exit 1)** with 7 new
orphans.  It was green at baseline.  The gate's own words: *"present at working
tree but outside the import closure, and it was not an orphan at
`origin/main~`; nothing compiles it, and it fails the Source scan for every
certificate."*  The 236 pre-existing orphans are tolerated; the 7 new ones are
not.

```
GroupApproximation.AlgTop.ChernSeries
GroupApproximation.AlgTop.CochainLeibniz
GroupApproximation.AlgTop.ComplexProjectiveBasic
GroupApproximation.Analysis.LIXProjectiveSpaceModel
GroupApproximation.Manuscript.NinetyNineProblems.ProblemXWitness
GroupApproximation.Topology.AntipodalObstructionFromOddDegree
GroupApproximation.Topology.OddMapNormalization
```

This is the campaign's design — lanes are forbidden from editing the root, so
every new module arrives unwired — but the consequence has to be stated plainly
rather than tolerated silently: **none of these seven has been elaborated, so
every `#audit_closed_axioms` line inside them is inert.**  The root import for
each has to land, and the lead's script is the only thing that can land it.
Until then, "the build is green" continues to say nothing about any of this
wave's work.

Other counts unchanged: 36 / 136 / 3263, `check_manuscript_claims` still green
with the same 15 line-number warnings, and the lexical scan still shows the
same 7 `sorry`s in `Manuscript/NonMF/TheoremCAssembly.lean` and nothing new.
(The scan also reports `scripts/Audit/Plants.lean:28 axiom plantedAxiom : True`
— that is the audit's own calibration plant and is supposed to be there.)

`ProblemX` closure re-measured: **485 project modules, acyclic, zero orphans.**
Target 1 remains the only fully-wired target.

### Target 2: `CommonZeroProperty` is discharged, and the discharge is honest

`GroupApproximation/Topology/AntipodalObstructionFromOddDegree.lean` now proves

```lean
theorem commonZeroProperty_unconditional : TautologicalCommonZero.CommonZeroProperty :=
  TautologicalAntipodal.commonZeroProperty_of_antipodalObstruction antipodalObstruction
```

I checked this against the restated-residue failure mode, because a bridge from
one common-zero statement to another is exactly the shape a restatement hides
in.  It is not a restatement.  The intermediate
`OddMapNormalization.SphereComplexCommonZero` is the *sphere* form — an odd map
out of `↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)` — whereas
`AntipodalObstruction` is about `ℂ^{N+1} ∖ {0}`, and
`antipodalObstruction_of_sphereCommonZero` does the real work between them:
`realToComplex` pairs the `2N+2` real coordinates into `N+1` complex ones,
`eq_zero_of_realToComplex_eq_zero` proves that pairing injective (which is what
keeps the composite inside the punctured set, so `ContinuousOn.comp_continuous`
applies), `realToComplex_neg` carries oddness across, and the arithmetic is
`2 * Nat.card κ ≤ 2N ≤ 2N + 1 = d` — tight, as the module says.  The
`SphereOddDegree.Sphere d` of the vendored port is `abbrev`-equal to that same
subtype, so feeding `complexOddMapCommonZero` in is a retyping and not a
transport.

Note what this means for the campaign brief: the two routes to the topological
input — the Chern one through `CommonZeroProperty` and the operator-algebraic
one through `ComplexOddMapCommonZero` — now **rest on the same theorem**,
`SphereOddDegree.complexOddMapCommonZero`.  There is no longer an independent
second opinion on that input.  Everything about target 2's topology reduces to
whether the 169-module vendored port compiles and is sound.

### Target 2: the endpoint was refactored into the right shape

`STW22NegativeSolution.negativeSolutionToProblemXXII` is now
`negativeSolutionToProblemXXII_of_borsukUlam.{v} complexOddMapCommonZero_unconditional`,
with the conditional theorem living in the new
`GroupApproximation/Analysis/STW22ConditionalNegativeSolution.lean`.  That file
carries `#audit_axioms` on the four theorems that take the Borsuk–Ulam
hypothesis and `#audit_closed_axioms` only on `antipodalCanonicalExtension_injective`,
which does not.  That is the correct discipline — `#audit_closed_axioms`
rejects a leading binder, so putting it on a conditional theorem would fail,
and putting `#audit_axioms` on the applied endpoint would under-check it.  The
applied endpoint keeps `#audit_closed_axioms`.  No objection.

**Problem 2B is unaffected.**  Factoriality is still absent from the endpoint's
conclusion, and no `Factorial` or `TraciallyComplete` definition exists.  Split
into a conditional and an applied form is orthogonal to it.

### Target 1: strengthened, and the strengthening is orphan

`GroupApproximation/Manuscript/NinetyNineProblems/ProblemXWitness.lean` adds

```lean
theorem exists_tracialState_isAmenableTrace_not_isQuasidiagonalTrace :
    ∃ τ : TracialState (MaximalGroupCStar MarkedGroup),
      Quasidiagonal.IsAmenableTrace (fun a ↦ τ a) ∧
        ¬ Quasidiagonal.IsQuasidiagonalTrace (fun a ↦ τ a)
```

This is a genuine improvement on `not_problemX1Statement`: the refutation in
existential form, with the trace bundled so that tracialness is part of the
witness rather than an assumption about it, and with
`literalCanonicalTrace_isAmenableTrace` writing out the class instead of
hiding it behind `LiteralFactorizationProperty`.  Its three
`#audit_closed_axioms` lines are the right ones.

But the module is a **new orphan**, so those three lines are inert, while the
nine in `ProblemX.lean` are live.  Target 1's grade therefore does not move:
the wired part is what it was.  This module is first in the queue for a root
import.

### Target 3: first modules, and two models of the same space

Four LIX modules landed, all orphan: `AlgTop/ComplexProjectiveBasic.lean`,
`AlgTop/ChernSeries.lean`, `AlgTop/CochainLeibniz.lean`,
`Analysis/LIXProjectiveSpaceModel.lean`.  No endpoint yet, so the verdict
stays NOT-YET-STATED.

**Duplication, flagged to `lix-design`.**  `AlgTop.IsLineProj`
(`qᴴ = q ∧ q * q = q ∧ q.trace = 1`, with `CP d` as its subtype) and
`STW59.IsProj` (`qᴴ = q ∧ q * q = q`, trace-one carried as a hypothesis per
lemma, with `unitVectors`/`rankOne`/`eq_rankOne_of_trace_one`) are two models
of the same space in two namespaces.  They do not collide, so no gate catches
them, and the repository's duplicate detector is already known to miss
cross-vocabulary duplicates of exactly this kind.  Raised by hand before more
is built on each.

## Sweep 3, 2026-09-05 — target 3 gets an architecture, and it is conditional by design

Orphan count 248 (+13 on baseline, still −0 wired).  New since sweep 2:
`AlgTop.ChernNewtonSquareZero`, `AlgTop.ChernParityCoefficient`,
`AlgTop.SingularCohomology`, `Analysis.CStarUnitaryComponent`,
`Analysis.SequentialGroupColimit`, `Analysis.STW22ConditionalNegativeSolution`.
Other counts unchanged (36 / 136 / 3263); `check_import_regression` still red.

**Duplicate-declaration pre-flight, run over all eight new campaign modules**
(the wiring hazard where a module that nobody compiles re-declares a name the
corpus already has, and turns main red the moment the lead wires it): I indexed
58 437 qualified names across 4 301 files and checked each new module's
declarations against it.  **Zero collisions.**  All eight are safe to wire on
this axis.  This does not say they compile.

### Target 3 — the architect's own verdict is CONDITIONAL, and it should stay that way

`research/artifacts/stw59-lean-route-design-2026-09-05.md` (commit `d6f438fff`)
settles target 3's shape, and it does not meet the campaign's stated goal.  Its
verdict, quoted: *"There is no unconditional Lean route to the parity
obstruction at feasible cost."*  Two of the manuscript's three deep topological
inputs are removed — `K₁(A) = 0` is off the critical path (`[v] = 0` is
witnessed directly by `diag(v,1)` in `U₀(M₂A)`), and stable triviality of
`diag(u,1)` becomes free once `u` is defined by hemisphere comparison of the
explicit frames of `F(x) = 1 − x xᴴ` rather than taken from Bott's
`π₄(U(3)) = 0` — and what is left is **one** named `Prop`:

```lean
/-- Twisted cancellation failure (manuscript Lemma 2). -/
def TwistedCancellationFailure : Prop
```

— over `S⁵ × ∏_j CP^{d_j}`, `F ⊕ p_H` is not Murray–von Neumann equivalent to
`1² ⊕ p_H` in the matrix algebra over `C(·, ℂ)`, for any finite list of
dimensions.  Discharging it needs Chern classes with Whitney sum, the Euler
class as a signed transverse-zero count, `K⁰(∏CP^{d_j})`, Künneth, and Chern
character integrality — none of which exist in Mathlib at pin `81a5d257`.

The design note polices itself correctly and this lane endorses that, in its
own words: `exists_simple_unital_not_k1Injective (h : TwistedCancellationFailure)`
*"is a REDUCTION, not an endpoint … must not be registered as a closed endpoint
for STW LIX, must not appear in the endpoint/audit roster as such, and must not
be cited in the manuscript as answering Problem LIX in Lean."*  That is
standing rule 3 applied to the lane's own work before anyone asked, and it is
the right call.

**Verdict for target 3: CONDITIONAL-ON-`TwistedCancellationFailure`.**  The
campaign's user order was "fully unconditionally, no literature inputs"; on the
architect's own analysis LIX will not meet it, and the honest output is *"LIX
reduces to one sentence about two explicit projections"*, not *"LIX is closed"*.
This lane will refuse a green grade for LIX while that `Prop` is undischarged,
and will say so in the final paragraph regardless of what else lands.

### Pre-registered checks for `TwistedCancellationFailure` when it lands

Recorded now, before the statement exists, so the check cannot be fitted to it
afterwards.  A residue `Prop` fails honestly only if it is *neither* vacuous
*nor* provable by a triviality, and a negative statement about Murray–von
Neumann equivalence has a specific way of going wrong:

1. **Rank/trace parity.**  MvN-equivalent projections have equal pointwise
   rank.  `F(x) = 1 − x xᴴ` over `S⁵ ⊂ ℂ³` has rank 2 at every point and so
   does `1²`, so the statement is *not* trivially true.  If the landed
   statement compares `F ⊕ p_H` against `1³ ⊕ p_H`, or otherwise mismatches
   ranks, it becomes true by a two-line trace argument and the residue has been
   "discharged" by a triviality that has nothing to do with Lemma 2.  Check the
   ranks on both sides before believing any proof of it.
2. **Quantifier direction.**  Lemma 2 must be *"for every finite `d` and every
   `w`, no equivalence"*, not *"there exists a `d` with no equivalence"*.  The
   second is weaker and would not support the limit argument.
3. **Non-vacuity of the consumer.**  `exists_simple_unital_not_k1Injective`
   must not be the only thing that ever mentions the `Prop`; if nothing
   inhabits `IsSimpleCStar A ∧ ¬ K1Injective A` for any `A` even given the
   hypothesis, the reduction is an implication with an uninhabited conclusion.
4. **`K1Injective` must be Mathlib-shaped.**  If the endpoint's notion of
   `K₁`-injectivity is a definition the counterexample's own construction
   introduces, the statement is written in the proof's vocabulary and is not
   auditable from outside.  It must be stated over the unitary group and its
   connected component, not over a predicate invented for this file.

Explicitly out of scope per the design note, and this lane will treat any of
them appearing in a LIX module as scope drift to report: `K₁(A) = 0`,
`π₄(U(3)) = 0`, `π₄(U(2)) = ℤ/2`, Steenrod squares, cup-`i` products,
simplicial `CP²`, and any general theory of inductive limits.

### Target 1 — the quarantine gate now exists

Commit `365a823a5` adds `NinetyNineProblems.not_problemX1Statement`,
`literalFactorizationProperty` and
`literalCanonicalTrace_hyperlinear_not_quasidiagonal` to `zeroInputEndpoints`
in `scripts/Audit.lean`.  This is the single most valuable thing landed in the
campaign so far: it closes the hole this file recorded at baseline, where
`ProblemX.lean`'s own `#audit_closed_axioms` gated the axiom closure and the
telescope while **nothing** gated the literature quarantine — and
`TikuisisWhiteWinterInput`, `AmenableNuclearInput` and `AmenableUCTInput` all
sit three imports away in `Analysis/TikuisisWhiteWinterCore`.

The grade does not move to "machine-checked" yet.  `scripts/Audit.lean` walks
**oleans**, so the gate is only as good as the run behind it, and the commit
message's specific numbers (21 corpus constants in the closure of
`not_problemX1Statement`; none of the thirty roster packages reached) are
either a run's output or a reading's, which are different claims.  I have asked
`brown-x1-verify` for the log tag and job count.  Until that comes back the row
stays **UNCONDITIONAL (stated + closed), source-read**.

A consequence worth flagging for whoever next edits `TikuisisWhiteWinterCore`:
the quarantine walk fails the run *at the seeded name*, so a future change that
routes `IsAmenableTrace` or `IsQuasidiagonalTrace` through a typed input will
turn the audit red at Problem X rather than at the module that caused it.
