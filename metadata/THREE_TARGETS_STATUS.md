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

## Sweep 4, 2026-09-05 — 22 new orphans, none wired; X(1) non-vacuity verified

Orphan count **257** (+22 on baseline, still **−0 wired**).  Gate counts
unchanged (36 / 136 / 3263); `check_import_regression` still red; lexical scan
still the same 7 `sorry`s in `NonMF/TheoremCAssembly.lean` plus the audit's own
`Plants.lean` calibration axiom.

The wave's whole output so far is unbuilt.  Twenty-two modules, none of them
elaborated by anything, every `#audit` line in them inert.  That is the
campaign's design, but it means the honest answer to "is target 3 formalized"
is currently "there is source for it".

**Duplicate-declaration pre-flight, re-run over all 25 new orphan modules
against 58 894 indexed qualified names: zero collisions.**  Note on the
instrument, because a verification lane's own tools can lie too: the first run
of this check reported a collision on `GroupApproximation.AlgTop.homology`
across `SingularCohomology.lean:267` and `CupProduct.lean:304,311`.  That was
my regex, not the corpus — the identifier class stopped at ASCII, so
`homologyπ_classCycleRepr`, `homologyπ_cupHomologyLeft` and
`homologyπ_cupHomologyRight` all truncated to `homology` at the `π`.  Fixed to
accept the full Lean identifier alphabet and re-run; the clean result above is
from the fixed instrument.

### Target 1 — the non-vacuity check, independently verified

`c7a3db69d` extends the X(1) driver to print `isQuasidiagonalTrace_complex`,
`isAmenableTrace_of_isQuasidiagonalTrace` and `ucpContractive`, on the ground
that `¬ IsQuasidiagonalTrace` refutes Brown's question only if the class can be
inhabited at all — *"a transcription no trace satisfies would make the half
free"*.  That is precisely the failure mode this lane was asked to watch for,
caught by the lane being audited before the auditor asked.

Verified here independently: `Analysis/QuasidiagonalTraceProperties.lean:549`
proves `isQuasidiagonalTrace_complex : IsQuasidiagonalTrace (fun z : ℂ ↦ z)`,
and `Analysis/TikuisisWhiteWinterCore.lean:160` derives the amenable side from
it.  Both classes named in the X(1) statement are inhabited, so neither half of
`IsAmenableTrace τ ∧ ¬ IsQuasidiagonalTrace τ` is free.

The same commit also states plainly what this lane needed to know: *"The
corpus-wide audit needs a fully built `.lake` and the tree currently has an
unbuilt module."*  So the quarantine gate added in `365a823a5` has **not yet
run**.  Target 1's row stays UNCONDITIONAL (stated + closed), source-read.

### Target 3 — the Wu route contradicts the design note's own exclusion list

`4caed940d` routes the parity obstruction through Wu's formula mod 2: two
instances of the Wu relation for mod-2 Chern classes (`Sq² c₂ = c₁c₂ + c₃`,
`Sq⁴ c₃ = c₂c₃ + c₁c₄ + c₅`) give manuscript Lemma 3 outright for `Y = pt` and
`Y = ℂP²`, deleting K-theory, Bott periodicity, the Chern character and
integral Künneth from the ingredient list and downgrading the Euler class to a
mod-2 count.  That is a real reduction in the residue's cost.

It also needs **Steenrod squares**, which `stw59-lean-route-design-2026-09-05.md`
lists under *"Explicitly NOT needed — do not build, and do not let a lane drift
into them"*.  The two documents are now in direct conflict about the same
residue, and somebody has to own which is the campaign's route; this lane
records the conflict rather than resolving it, since the architecture is
`lix-design`'s call.  Either way the verdict does not move: the commit's own
last line is *"the general stage of the mod-2 induction is open"*, and `Y = ℂP²`
is explicitly *"a milestone and not the target"*.  **Target 3 remains
CONDITIONAL.**

What has actually landed for target 3 is upstream algebra, not the obstruction:
`AlgTop.ChernParityCoefficient.two_dvd_chernCoefficient` and
`AlgTop.ChernNewtonSquareZero.chern_eq_of_squareZero` are lemmas about
multinomial coefficients and Newton's identities over a commutative ring —
necessary for the parity calculation, nowhere near sufficient for it, and
carrying no topology at all.  Recorded so that a later reading of "the Chern
parity modules are done" is not mistaken for progress on the residue.

One thing landed for target 3 is exactly right, and it is worth naming:
`Analysis/CStarUnitaryComponent.lean` builds `unitaryComponentOne` as
`Subgroup.pathComponentOne (unitary A)` over Mathlib's own `unitary` and
`Mathlib.Analysis.CStarAlgebra.Unitary.Connected`, with `UnitaryClass A` as the
quotient.  That satisfies pre-registered check 4 — the endpoint's notion of
`K₁`-injectivity will be stated in Mathlib vocabulary and not in a predicate
the counterexample invents for itself, which is the difference between a
statement an outside reader can check and one they cannot.

### Machine state, recorded because it can manufacture a false green

At sweep 4 the data volume was **100% full — 121 MiB free of 230 GiB**, and a
tool call failed with `ENOSPC` mid-sweep.  A full disk is the purest
false-green generator there is: writes fail, logs truncate, and a step that
never ran can look like a step that passed.  Any build, audit run or gate
result produced around this timestamp should be re-run rather than trusted.
Largest consumers at the time: `/private/tmp/claude-501` at 2.1 GiB, of which
1.7 GiB is this session's shared scratchpad — a 227 MiB `flt` git pack and a
92 MiB `mathlib_all.txt` belonging to other lanes, which this lane did not
touch.

## Sweep 5, 2026-09-05 — Problem 2B, located exactly

The factoriality gap now has a precise address.  It is not that nobody thought
about factoriality; it is that the argument for it lives in **one parenthetical
sentence of prose**, in a research artifact, and has never been formalized or
stated.

`research/artifacts/stw22-trace-problem-counterexample-audit-2026-08-31.md`,
lines 275–278, immediately after deriving `T(A) ⊊ T(M)`:

> *"Since the uniform tracial completion with its designated compact trace face
> is factorial in the tracially-complete sense (and here the extreme designated
> fibres are the matrix factors `M_(s+1)` and the scalar fibre at infinity), the
> example also refutes the equivalent factorial-tracially-complete
> formulation."*

That is the whole of it.  A `since`-clause with a parenthesis.  Everything else
in the XXII chain — the gauge, the completion, the corona state, the strict
inclusion — is formalized down to the kernel, and the one hypothesis that makes
the result an answer to *Problem XXII* rather than to a weaker question is
carried by that sentence.  There is still no `Factorial` and no
`TraciallyComplete` in any Lean module (re-checked: the only `factorial` hits in
the corpus are the arithmetic function and `Analysis/GroupVonNeumannAlgebra`,
neither related).

The mathematical claim is plausible — matrix algebras and `ℂ` are factors, so
fibres over the extreme boundary being `M_{s+1}` and the scalar fibre at
infinity is the right shape — and this lane is not disputing it.  The point is
narrower and it is the campaign's whole subject: **the endpoint's name promises
Problem XXII and its type does not deliver it**, and the missing step is
recorded nowhere a gate can see.  A reader of `negativeSolutionToProblemXXII`
gets ten conjuncts, none of which is factoriality, and no pointer to the prose
that would supply it.

What would close it, in decreasing order of what this lane would accept:

1. a Lean definition of factoriality for the pair, a theorem that the antipodal
   pair satisfies it, and that theorem as a **named conjunct** of the endpoint;
2. failing that, a `Prop` stating it and the endpoint restated as an implication
   from it — conditional, honest, and gateable;
3. failing both, the declaration renamed so that it does not claim Problem XXII,
   with the prose sentence quoted in its docstring as the step that is missing.

Silently keeping the name is the one option that is not available, because it is
exactly the badge-claim-strength defect this repository exists to catch.

## Sweep 6, 2026-09-05 — target 3's `K₁`-injectivity is stated correctly

Orphan count **274** (+39 on baseline, still **−0 wired**).  Gate counts
unchanged (36 / 136); `check_import_regression` still red; lexical scan
unchanged at 13 hits, of which 8 are real (the 7 `sorry`s in
`NonMF/TheoremCAssembly.lean` and `scripts/Audit/Plants.lean`'s deliberate
calibration axiom) and 5 are the words inside docstrings.  **No new `sorry`.**

### Pre-registered check 4: passed

`Analysis/CStarKOne.lean` states the target-3 endpoint's vocabulary in exactly
the shape this lane asked for before it existed:

```lean
abbrev KOne : Type u := (kOneTower A).Colim          -- colim U(Mₙ(A))/U₀(Mₙ(A)) along u ↦ diag(u,1)
def kappa : UnitaryClass A →* KOne A                 -- U(A)/U₀(A) → K₁(A)
def K1Injective : Prop := Function.Injective (kappa A)
```

`UnitaryClass A` is `unitary A ⧸ unitaryComponentOne A` and
`unitaryComponentOne` is `Subgroup.pathComponentOne (unitary A)` over Mathlib's
own `unitary` — so `K1Injective` is the textbook statement over the textbook
objects, not a predicate the counterexample invented for itself.  An outside
reader can check that this is Problem LIX.  That was check 4 and it is met.

### Pre-registered check 3 now has a concrete shape

`Analysis/CStarKOneInjectivityCriterion.not_k1Injective_of_exists_witness`
reduces `¬ K1Injective A` to

```lean
∃ u : unitary A, u ∉ unitaryComponentOne A ∧
  diagOne u ∈ unitaryComponentOne (CStarMat 2 A)
```

— a unitary not null-homotopic in `U(A)` whose block sum `diag(u,1)` *is*
null-homotopic in `U(M₂(A))`.  That is the standard criterion and it is not
cheap: both clauses are about the same `u`, and the whole difficulty of the
counterexample is producing one.  It is also the design note's "Removal 1"
made good — `K₁(A) = 0` never appears, because
`kappa_mk_eq_kOneIota_two` shows the class of `u` in `K₁` is read at level two
of the tower, so `diag(u,1) ∈ U₀(M₂A)` kills it directly.  No Bott
periodicity, no Morita invariance.

So the LIX chain is being built in the right vocabulary, with the right
criterion, and against a residue the lane has itself refused to call closed.
The verdict is unchanged and will stay unchanged until
`TwistedCancellationFailure` is inhabited: **CONDITIONAL**.

### Instrument note

This lane's sweep script lives in the session scratchpad, and another process
cleaned that directory mid-campaign, so sweep 6 was run inline instead.  Worth
recording only because it is the same class of failure the lane exists to
catch: a check that silently does not run looks exactly like a check that
passed.  The counts above are from a run that produced output, not from an
exit code.

## Sweep 7, 2026-09-05 — the port is green, and target 3's mandate changed

Two things moved that change grades, one up and one sideways.

### The Borsuk–Ulam port compiles, and its endpoints are closed

`55ef7702b` reports **build tag 64648: the whole odd-degree closure compiles
with zero errors**, firing `oddMapFixesTopClass_unconditional_closed`,
`rpCohomology_dimension_vanishing_closed` and `borsuk_ulam_closed`, each on
`[propext, Classical.choice, Quot.sound]`.  That is the first real green in
this campaign.  It means target 2's topological input is not merely
source-unconditional but machine-checked: `borsuk_ulam` is a theorem of this
repository at v4.32.

The same commit retracts three docstring headers in `Final/` that asserted an
unconditional odd-degree theorem *could not be produced honestly*, that
`OddMapFixesTopClass n` had no unconditional constructor, and that the missing
`rpCohomology` vanishing was Branch-3 mathematics absent from the project.  A
build refuted all three.  The route the headers did not consider is
`rpCohomology_topPlusOne_isZero_direct`, which gets `H^{n+1}(RPⁿ; F₂) = 0` by
Kronecker duality from the Mayer–Vietoris homology vanishing rather than by the
excision/good-pair computation the headers called absent — so
`RPnCellularCochainStructure` is never needed and the whole cellular stack
drops out of the closure.

Retracting a recorded impossibility claim that a build refuted is the right
response and is recorded here as such.  **Verified independently:** the commit
says *"No declaration is touched"*, and the diff is docstrings only — the one
line in it that starts with the word `theorem` is prose inside a docstring.
Three files, +50/−6, no declaration and no `#audit` line changed.

Still to confirm: the commit names three `_closed` endpoints, and the one this
campaign actually consumes is a fourth, `complexOddMapCommonZero_closed`, which
is the sink of the 199-module port.  A probe of
`GroupApproximation.Analysis.STW22NegativeSolution` is in flight from this lane
and will settle it, together with whether
`#audit_closed_axioms negativeSolutionToProblemXXII` fires.

### Target 3: the residue was withdrawn, and the grade moves sideways, not up

`f125c1846` (LIX design revision 2) changes the mandate to *"build the missing
foundations"* and **withdraws revision 1's residue ledger**:
`TwistedCancellationFailure : Prop` and
`not_k1Injective_of_twistedCancellationFailure` are gone, and `lix-obstruction`
is to prove the statement rather than name it.  Four scoping results shrink the
foundation stack: no Steenrod squares or Wu formula (the integral route covers
`q = 3`, and the note records exactly where the mod-2 route dies — `Sq^{2k}
c_i(δ) = C(i−1,k) c_{i+k}(δ)` reaches `c₃` from `c₂` but cannot reach `c₄`, and
for `Y = ℂP¹` the value `γ₁ = 1/6` satisfies every mod-2 constraint while making
`c₄(δ)` odd); K-theory collapses to one lemma (KT-min); all K-theory is
C\*-algebraic so Serre–Swan is deleted; and no Poincaré duality.  The earlier
Wu/Steenrod conflict this file recorded at sweep 4 is therefore resolved — in
favour of dropping the mod-2 route, with a stated reason.

**The endpoint discipline in revision 2 is correct and this lane endorses it**:
*"under the new mandate there is no residue `Prop` to hypothesise on, so the
endpoint is simply unlanded, and must not be registered in the endpoint/audit
roster or cited in the manuscript."*  There is no conditional theorem wearing a
clean axiom report, which is the outcome that matters.

But the grade does not improve.  **Target 3 moves from CONDITIONAL-on-one-named-
`Prop` to NOT-YET-STATED**, and its success now rests on the two items the note
itself names as the only places the campaign can fail: **Bott periodicity, which
has never been formalized in Lean** (narrowed to `ch(K̃(S^{2n})) = ℤ`, a real
reduction but still the deepest item), and **Leray–Hirsch / the projective
bundle formula** for `H^*(P(E))` free over `H^*(X)`.  Everything else is
declared not at risk, and reads that way — but it is 4000–6000 lines of
grinding *plus* two hard theorems.

One recommendation this lane will keep making: **do not let
`TwistedCancellationFailure` be deleted without being written down somewhere.**
It is the fallback statement.  If Bott stalls, the honest output reverts to
revision 1's — "LIX reduces to one sentence about two explicit projections" —
and that sentence should still exist when it is needed.  A withdrawn residue
that nobody can quote is worse to audit than a named one.

## Sweep 8, 2026-09-05 — Problem 2B gets its vocabulary, but not yet its theorem

`e09ad4f4d` lands `GroupApproximation/Analysis/TraciallyCompleteCStar.lean`,
552 lines, in direct response to Problem 2B.  The definitions are faithful and
this lane has no complaint about any of them:

```lean
structure IsTraciallyCompletePair (X : Set (TracialState A)) : Prop where   -- CCEGSTW Def 3.4
  nonempty : X.Nonempty
  isCompact : IsCompact X
  isConvex : IsConvexTraceSet X
  faithful : IsFaithfulTraceSet X
  unitBallComplete : UnitBallUniformTwoComplete X

structure IsFactorialTraciallyCompletePair (X : Set (TracialState A)) : Prop where  -- Def 3.13
  toIsTraciallyCompletePair : IsTraciallyCompletePair X
  isClosed : IsClosed X
  isFace : IsFaceTraceSet X
```

Three details are right in the way that distinguishes a transcription from a
paraphrase.  `IsFaceTraceSet`'s second field quantifies over a **proper**
convex combination (`0 < t < 1`, not `0 ≤ t ≤ 1`), which is the real face
condition and not the weakening a hurried reading produces.  The paper's
implicit nonemptiness is made an explicit field rather than inherited.  And
both forms of Question 1.1 are present — `AllTracesUniformTwoContinuous` and
`DesignatedTracesAreAllTraces` — with
`allTracesUniformTwoContinuous_iff_designatedTracesAreAllTraces` connecting
them under the CCEGSTW Proposition 3.15 hypothesis.

**Problem 2B is nevertheless still open, and the distinction is the campaign's
whole subject.**  Defining factoriality and instantiating it are different
acts.  Grepping both `STW22NegativeSolution.lean` and
`STW22ConditionalNegativeSolution.lean` for `IsFactorialTraciallyCompletePair`
and `AllTracesUniformTwoContinuous` returns nothing: the endpoint is unchanged,
its ten conjuncts still do not include factoriality, and its name still
promises more than its type delivers.  What is needed is a theorem
`IsFactorialTraciallyCompletePair (the antipodal designated trace set)` **and
that theorem as a named conjunct of the endpoint**.

Of the six fields to discharge, `isCompact`, `isConvex` and `isClosed` look
free from what is already proved (`antipodalWeakStarTraceSimplex` is nonempty
and Bauer).  `faithful` and `unitBallComplete` are substance.  **`isFace` is
the one to look at first**, because a closed face is genuinely stronger than a
compact convex subset, and the prose sentence this lane located at sweep 5
does not argue it — it argues that the extreme *fibres* are factors, which is a
different statement, equivalent only through CCEGSTW's own proposition and not
by inspection.

`TraciallyCompleteCStar` is itself a new orphan (orphan count now **275**), so
its 552 lines have not been elaborated.  It does join the port-free batch of
`metadata/CAMPAIGN_WIRING_PREFLIGHT.md` — its imports are
`UniformTracialGNSTwoGauge` and `TracialStateWeakStarTopology`, the latter
already at position 32 — so it can be built without waiting on the port.

### Roster integrity, checked

Exactly one commit has touched `scripts/Audit.lean` or
`metadata/LITERATURE_QUARANTINE.md` since the campaign began (`365a823a5`), and
it is purely additive: three names appended to `zeroInputEndpoints`, no
`literaturePackages` entry removed, no roster line deleted.  The quarantine's
own rule — an entry is retired only by proving it, in the same commit that
deletes the line — has not been tested, because nothing has been retired.

### Probe in flight

`scripts/remote-build.sh GroupApproximation.Analysis.STW22NegativeSolution`,
log tag **18285**, launched by this lane; currently queued on the fleet build
lock.  It is the decisive probe for target 2: it pulls the port and the
operator-algebra chain together and fires
`#audit_closed_axioms negativeSolutionToProblemXXII`.  The number to read from
it is the **job count**, not the verdict.

## Sweep 9, 2026-09-05 — `autoImplicit` is on across the whole corpus

This is the largest structural finding of the audit and it is not specific to
the three targets.

```
files under GroupApproximation/ :                      4331
files containing `set_option autoImplicit false` :        0
files containing `set_option relaxedAutoImplicit false`:  0
lakefile.toml `moreLeanArgs` :        ["-DwarningAsError=true"]   -- and nothing else
```

Lean's default is `autoImplicit := true`.  Mathlib turns it off in its own
lakefile; that setting does not reach this project's library.  So **every
declaration in this repository is elaborated with automatic implicit binding
switched on**, and an identifier that is not in scope does not fail — it
becomes a fresh auto-bound implicit variable.

Why this matters for a campaign about unconditionality, and in which direction.
An auto-bound name in a *conclusion* usually makes the theorem unprovable, so
it fails loudly.  An auto-bound name in a **hypothesis** makes the theorem
*weaker* and it compiles silently: `theorem foo (h : IsLineProj q) : …`, with
`IsLineProj` undefined, elaborates as `∀ {IsLineProj : _ → Prop}, IsLineProj q
→ …` — an assumption about an arbitrary predicate, which is a far weaker
hypothesis than intended and can be discharged by nonsense.  Hypotheses are
exactly where this campaign keeps its residues.

**This is not hypothetical here.**  `1a012c0c0` records that `IsLineProj`
occurred four times repo-wide — `AlgTop/ComplexProjectiveHyperplane.lean:39,40,69`
and `AlgTop/ComplexProjectiveChart.lean:49` — and **was defined nowhere**, and
says in as many words: *"No gate caught it because the lakefile does not set
`autoImplicit := false`."*  Verified here: `IsLineProj` no longer occurs
anywhere in the corpus, so that instance has been repaired, but it was live,
and it was found by a lane reading source rather than by any gate.

The same commit records a second defect of the same family that no gate could
see: `Analysis/FiniteCStarMurrayVonNeumann.lean:99` and
`AlgTop/BundleCalculusProjection.lean:68` defined
`∃ v, star v * v = p ∧ v * star v = q` **character for character** under the
same typeclasses, in different namespaces, with no import between them.  That
is the cross-vocabulary duplicate this file flagged at sweep 2 in its `CP^d`
form, now confirmed in a second place and arbitrated (`MurrayVonNeumannEquiv`
survives as the older name with six consumers; `BundleCalculusProjection`
re-homes onto it, and `Analysis/ProjectionMvNEquivalence.lean` and
`Analysis/CornerCStarAlgebra.lean` are withdrawn).  Note the consequence for
the campaign's ledger: the three analytic lemmas being re-homed *are* the
design note's (L1)(L2)(L3), so L0's analytic floor turns out to have been
already done — the plan was written against Mathlib greps that were never
repeated against this repository.

**Recommendation, for whoever owns the lakefile** — not this lane, and not a
change to make mid-wave:

* at minimum, `set_option autoImplicit false` at the head of every new
  campaign module.  It costs one line and it converts a silent weakening into
  a build error;
* at best, `autoImplicit := false` project-wide in `lakefile.toml`, taken as
  its own piece of work with its own build, since 4331 files have never been
  elaborated under it and some will need real binders added.

Until one of those happens, "it compiles" in this repository means less than a
reader assumes, and this file's verdicts should be read with that discount
applied — including its own green for the Borsuk–Ulam port.

### Fleet state, recorded because it is why nothing is verified yet

**22 concurrent `remote-build.sh` processes** against one serialized fleet
mutex, with five targets duplicated: `STW22NegativeSolution` ×2,
`LIXProjectiveSpaceModel` ×4, `ProblemXWitness` ×2, `MappingTorusParity` ×2,
`ComplexProjectiveHyperplane` ×2.  This lane's probe (log tag 18285) has been
at `waiting on fleet build lock` for a quarter of an hour and the counter runs
to 180.  The program note's own rule is not to oversubscribe the compute nodes.
Two lanes are also still redirecting build output to the same shared path
`scratchpad/probe1.log`, which with 22 concurrent builds makes reading another
lane's result a near certainty — `remote-build.sh` tags its remote log per
invocation and the local redirect undoes that.

---

# The honest paragraph per target

Written to be read on its own, and updated as the wave lands.  State as of
2026-09-05, sweep 9.

## Problem X(1) — is every amenable trace quasidiagonal?  No.

**This one is proved, and it is the only one of the three that is.**
`GroupApproximation.NinetyNineProblems.not_problemX1Statement : ¬ ProblemX1Statement.{1}`
refutes Brown's question at the universe where it lives, and `ProblemX.lean` is
inside the root import closure, so an ordinary build elaborates it and runs its
nine `#audit_axioms`/`#audit_closed_axioms` lines — the only target of which
that is true.  The statement quantifies over nothing but Brown's two
definitions, transcribed as structures with no hypothesis fields differing in
exactly one clause, and reaches no entry of the literature quarantine; in
particular it does not reach `TikuisisWhiteWinterInput`, which is the one a
reader should suspect, since X(1) is the converse of that theorem.  Neither
half is free: `IsQuasidiagonalTrace` is inhabited
(`isQuasidiagonalTrace_complex`, the identity trace on `ℂ`) and so is
`IsAmenableTrace`, so `amenable ∧ ¬ quasidiagonal` is a real conjunction rather
than a vacuous one.  The witness is a concrete finite presentation on eight
generators, not a group handed over by a citation.  **What is not yet done:**
until this campaign, nothing gated the *literature quarantine* at this endpoint
— `#audit_closed_axioms` gates the axiom closure and the outer telescope, and
the quarantine walk is seeded elsewhere.  Three names were added to
`zeroInputEndpoints` on 2026-09-05, which fixes that, but the corpus audit that
runs the walk **has not been executed**, because it needs a fully built `.lake`
and the tree has unbuilt modules.  So the correct reading today is: proved,
machine-checked for axioms, and awaiting one audit run for the citation check.
**Remaining input: none identified.**

## Problem XXII — the trace problem for factorial tracially complete C\*-algebras.  No.

**The mathematics looks complete; the formalization is not, in two separate
ways, and the second is the one that matters.**  The topological input is
genuinely machine-checked: build tag 64648 compiled the whole odd-degree
closure with zero errors and fired `borsuk_ulam_closed` on
`propext / Classical.choice / Quot.sound`, and the complex-coordinate form the
counterexample consumes follows from it by realification.  That is a real
theorem of this repository, not a citation — and it also discharges
`CommonZeroProperty`, which the campaign's own brief still lists as the open
residue.  Against that: **the operator-algebra half does not compile.**  This lane
probed it (log tag 18285) and the build fails: nine identical instance
failures for `∀ (n : ℕ), Nonempty (TracialState (AntipodalCounterexampleBlock
n))` poison `negativeSolutionToProblemXXII_of_borsukUlam` and three neighbours
with `sorryAx`, with no `sorry` in the source.  One theorem in the file *is*
clean — `not_everyAntipodalCompletionTraceIsContinuousExtension_of_borsukUlam`,
which is the substance of the negative answer — so the core is real and the
assembly around it is red.  Nothing had ever run those `#audit` lines, because
the module has been orphan since it was written.  And **the endpoint does not state the problem's
hypothesis.**  Problem XXII asks about *factorial* tracially complete pairs; the
endpoint's ten conjuncts assert unitality, separability, nuclearity, Type I, a
gauge identity, a nonempty Bauer trace simplex, a compact metrizable boundary,
and injectivity-but-not-surjectivity of the canonical extension — and not
factoriality.  The argument for factoriality exists in exactly one parenthetical
sentence of prose in a research artifact.  CCEGSTW Definitions 3.4 and 3.13 have
now been written in Lean, faithfully, but nothing yet proves the antipodal pair
satisfies them and the endpoint does not mention them.  **Update, sweep 14: the statement gap is closed.**
`Analysis/STW22AntipodalFactorialPair.lean` now proves
`antipodalFactorialNegativeSolutionToProblemXXII_of_borsukUlam`, whose
conclusion is `IsFactorialTraciallyCompletePair antipodalDesignatedTraces ∧
antipodalDesignatedTraces = Set.range (canonicalExtension …) ∧ ¬
AllTracesUniformTwoContinuous … ∧ ¬ DesignatedTracesAreAllTraces …` — the
problem's hypothesis, both forms of Question 1.1 refuted, and `X` pinned so no
substitution is possible.  **Remaining input: a build, and three pieces of
bookkeeping** — the `private theorem` at
`STW22AntipodalBaseCoordinateMeasures.lean:29` that should be an `instance`
(nine synthesis failures and four `sorryAx` poisonings downstream), an `#audit`
line on the new module (it has none), and the one-line unconditional
application of `complexOddMapCommonZero_unconditional`.  None of it is a
citation and none of it is mathematics.

## Problem LIX — are all unital simple C\*-algebras K₁-injective?  No.

**Nothing is proved.  There is no endpoint, and there is not yet a statement.**
Target 3 began this campaign with zero Lean and it still has none that concludes
anything about Problem LIX.  What exists is a plan, now in its third revision,
and the elementary floor beneath it: `K1Injective` stated correctly over
Mathlib's `unitary` and `Subgroup.pathComponentOne` (so an outside reader can
check it *is* Problem LIX), the standard refutation criterion, the
Murray–von Neumann calculus, the projection model of `ℂP^d`, the clutching and
tautological-section lemmas.  All of it is orphan and none of it has been
compiled.  The plan's own verdict is the thing to read: revision 1 concluded
there is **no unconditional route to the parity obstruction at feasible cost**
and reduced the whole problem to one named `Prop`; revision 2 withdrew that
`Prop` under a changed mandate and aims instead at building the missing
foundations, and names the only two places it can fail — **Bott periodicity,
which has never been formalized in Lean**, and Leray–Hirsch for the projective
bundle formula.  Both are library-scale theorems.  The elementary remainder is
4000–6000 lines the plan itself calls grinding rather than research.  **Remaining
input: two open formalization projects, either of which stalling stalls the
target.**  The campaign's honest output for LIX today is a reduction, not an
answer, and the reduction's own statement — revision 1's
`TwistedCancellationFailure`, Murray–von Neumann inequivalence of two explicit
projections — has been withdrawn rather than kept, which this lane has
recommended reversing so the fallback still exists in writing if the gamble
does not come in.

## The discount that applies to all three

`autoImplicit` is on across all 4331 files (see sweep 9).  An identifier that is
not in scope becomes an auto-bound implicit rather than an error, and in a
*hypothesis* that silently weakens the statement.  One live instance was found
and repaired during this campaign, by a lane reading source and not by any
gate.  Every "it compiles" above should be read with that discount until
`autoImplicit := false` is set, including the green given to the Borsuk–Ulam
port.

---

## Sweep 10, 2026-09-05 — the first probe of the XXII endpoint: RED

`scripts/remote-build.sh GroupApproximation.Analysis.STW22NegativeSolution`,
log tag **18285**, launched by this lane and queued about forty minutes behind
the 22-deep fleet lock.

```
error: build failed
Some required targets logged failures:
- GroupApproximation.Analysis.STW22ConditionalNegativeSolution
```

**Cause: one instance, missing nine times.**  At
`STW22ConditionalNegativeSolution.lean` lines 56:4, 62:24, 65:5, 84:27, 87:4,
95:24, 97:27, 127:26 and 129:29, identically:

```
failed to synthesize instance of type class
  ∀ (n : ℕ), Nonempty (TracialState (AntipodalCounterexampleBlock n))
```

**Consequence: the poisoning pattern, with no `sorry` in the source.**  The
file's own four audit lines report:

| declaration | axiom closure |
|---|---|
| `antipodalBaseTracialTwoSize_eq_completionGauge` | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `antipodalCanonicalExtension_injective` | `sorryAx` |
| `antipodal_trace_space_strict_inclusion_of_borsukUlam` | `sorryAx` |
| `negativeSolutionToProblemXXII_of_borsukUlam` | `sorryAx` |
| `not_everyAntipodalCompletionTraceIsContinuousExtension_of_borsukUlam` | **clean** — `[propext, Classical.choice, Quot.sound]` |

So the endpoint named "negative solution to STW Problem XXII" has been on main,
described in commit messages as unconditional, **not typechecking** — while the
one theorem carrying the actual content is machine-checked.  The gate that
catches this was written correctly and sat in the file the whole time; it had
never been run, because the module is orphan.  That is the baseline finding of
this file with a casualty attached.

No job count is recorded for this probe: the build failed before completing, so
there is no "Build completed successfully (N jobs)" line.  A green claim for
this module must come with one.

**What this changes in the grades.**  Target 2's paragraph above is amended
from "written and unbuilt" to "written and red".  Nothing else moves: the
topological input is still genuinely machine-checked (build tag 64648), the
core implication is still clean, and the factoriality gap is still separately
open — a compiling endpoint that omits factoriality would still not be Problem
XXII.

**What it changes in the recommendation.**  The port-free batch of
`metadata/CAMPAIGN_WIRING_PREFLIGHT.md` should be wired.  Forty-five modules
build without the Borsuk–Ulam port, this one among them; wired when written,
this would have been caught the same hour instead of surviving on main.  The
campaign has produced 281 orphan modules and the first one anybody compiled
failed.  There is no reason to assume the rest are better.

## Sweep 11, 2026-09-05 — the face condition is proved; the LIX plan changes its risks again

### Target 2: Problem 2B moves, and the part that moved is the hard part

`cf75ca5b9` lands `Analysis/STW22FactorialCore.lean`, 375 lines, and proves the
condition this file singled out at sweep 8 as the one to look at first:

```lean
theorem isFaceTraceSet_designatedTraces …          -- the face condition
theorem isClosed_designatedTraces …
theorem isCompact_designatedTraces …
theorem isConvexTraceSet_designatedTraces …
theorem designatedTraces_nonempty …
theorem designatedTraces_eq_range …                -- X = range canonicalExtension
theorem mem_designatedTraces_iff_isCompletionUniformTwoContinuous …  -- CCEGSTW Prop 3.15
```

The argument is short for the right reason: CCEGSTW Proposition 3.23(iv) makes
factoriality of the completion equivalent to `X` being a face of `T(A)`, and
here `X` is all of `T(A)`, which is a face of itself.  A closed face was
genuinely stronger than the compact convexity already available, and it is now
a theorem rather than a parenthesis in a research note.  Credit where it is
due — that is a real answer to a finding, delivered in about an hour.

**Problem 2B is still open, and what is left is bookkeeping plus two clauses.**

1. `IsFactorialTraciallyCompletePair` is **never instantiated**.
   `STW22FactorialCore.lean` imports `TraciallyCompleteCStar` but neither that
   name nor `IsTraciallyCompletePair` occurs in it.  Five of the structure's
   fields exist as separate theorems; nothing has the type that *is* CCEGSTW
   Definition 3.13.
2. Two fields of Definition 3.4 are **not proved at all**: `IsFaithfulTraceSet`
   and `UnitBallUniformTwoComplete`.  Neither name occurs in the new file.
   These are what make the pair *tracially complete* rather than a C\*-algebra
   with a distinguished face.
3. The endpoint still does not mention factoriality.  Grepping
   `STW22NegativeSolution.lean` and `STW22ConditionalNegativeSolution.lean` for
   `Factorial` returns nothing.

And the 375 new lines have never been elaborated, in a file whose consumer is
currently `sorryAx`-poisoned (sweep 10).

### Target 3: the plan's "only two ways to fail" has now changed three times

| revision | route | stated risks |
|---|---|---|
| rev 1 | integral Chern / K-theory | *"no unconditional route at feasible cost"*; one residue `Prop` |
| rev 2 | integral, K-theory collapsed to (KT-min) | Bott periodicity; Leray–Hirsch |
| rev 3 | **mod-2 Wu** | Wu for a virtual class; the tower assembly; **Steenrod squares** |

`bd6fc788c` closes the mod-2 parity for every stage of the tower and takes Bott
and Leray–Hirsch off the path entirely.  The argument is careful and it
reconciles its own earlier refutation rather than quietly dropping it: revision
2 had a counterexample at `Y = ℂP¹` with `γ₁ = 1/6`, and rev 3 explains that
`d = 1` is **odd** there while the surviving term is `b₁` with `1 ≡ 1 (mod 4)`,
so both statements stand — mod 2 cannot prove Lemma 3 for general `Y`, and can
for this tower.  That reconciliation is the mark of a plan being reasoned about
rather than rewritten.

**Two things to hold them to, recorded here so they cannot be dropped
silently.**

* **`every d_j is even` is now a load-bearing side condition** — the commit
  says so outright, *"the hypothesis a lane may not drop"*.  Step 1 needs it
  (`(1+h_j)^{d_j} = (1+h_j²)^{d_j/2}` by one Frobenius), and rev 2's
  counterexample lives exactly where it fails.  Any LIX statement that
  quantifies over dimensions without it is refuted, not merely weaker.
* **Steenrod squares are back**, having been on rev 1's *"do not let a lane
  drift into them"* list and off rev 2's route.  This file recorded that
  conflict at sweep 4; it is now resolved in favour of building them, which is
  a decision, not an oversight — but it is the third answer to the same
  question in one afternoon.

`TwistedCancellationFailure` has been **restored as a markdown-only fallback,
explicitly at this lane's recommendation**.  That was the right call: it costs
nothing and it means the reduction statement still exists in writing if the
foundations do not land.

**The verdict does not move, and the reason is now sharper.**  Target 3 has no
compiled Lean, no endpoint, and a plan whose two stated failure modes have been
replaced twice in a few hours.  Each revision has been better-argued than the
last and this lane has no criticism of the work — but a plan that is still
discovering what its risks are is not evidence that the risks are small, and it
is not a basis for grading anything green.  **NOT-YET-STATED.**

### Fleet

23 concurrent `remote-build.sh` processes.  `f2a8c3a59` records a probe finding
real breakage — *"repair two Mathlib names that block the whole LIX chain"* —
which is the wiring-and-probing loop working as it should.

## Sweep 12, 2026-09-05 — the root import file was broken by the wiring script

**`scripts/check.py --list-orphans` jumped from 281 to 2744.**  Not because
2463 modules were unwired: because `GroupApproximation.lean` stopped being a
valid Lean file.

`scripts/wire_orphans.py` appended the first wired orphan **after the module
docstring**:

```
3309  /-!
      … 60 lines of module docstring …
3368  -/
3369  -- === wired orphans (scripts/wire_orphans.py) ===
3370  import GroupApproximation.Manuscript.NinetyNineProblems.ProblemXWitness
```

In Lean 4 `import` must precede every other command, module docstring included,
so an `import` there is a syntax error and **nothing builds**.  The other 3263
root imports sit above line 1002 and are fine.  Caught as a working-tree change
before it was committed, so it had not yet reached main; reported to the lead
immediately, and not repaired by this lane — lanes do not edit the root.

Two things worth drawing from it.

First, the orphan count is a *gate reading*, not a fact about the corpus, and
this is what it looks like when the instrument breaks instead of the subject.
A 2744 in that column would have been read by any lane as catastrophic
unwiring.  It was one line in the wrong place.

Second, **wiring `ProblemXWitness` was correct** — it is this file's own
recommendation and the module is fine.  What failed is the insertion point in
the script, and it will fail identically for the next 44 imports of the
port-free batch.  Fixing `wire_orphans.py` to insert rather than append is
prerequisite to the wiring campaign, not an argument against it.

### Two smaller findings from the same pass

**One dangling project import, corpus-wide.**
`GroupApproximation.AlgTop.MappingTorusParity` imports
`GroupApproximation.AlgTop.ChernNewtonSquareZero`, which no longer exists on
disk — renamed into the `ChernNewtonIdentity` / `ChernNewtonDischarge` family.
Both modules are orphan so nothing breaks today, but the corpus was clean on
this axis at `3a4b44ae3`, and a dangling import inside a module that later gets
wired takes the root build down rather than reddening one file.

**Audit-gate coverage on the new work is thin.**  About forty of the campaign's
modules carry **no `#audit` line at all**: every `AlgTop.*` module
(`ChernSeries`, `ChernNewtonIdentity`, `ChernPowerSums`, `CupProduct`,
`CupAssoc`, `SingularCohomology`, `ComplexProjective*`, `MappingTorus*`,
`EulerLocalModel`, `BundleCalculus*`, …), `Analysis.CStarKOne`,
`CStarKOneInjectivityCriterion`, `CStarUnitaryComponent`,
`CStarMatrixBlockInclusion`, `SequentialGroupColimit`, and the whole `LIX*`
family.  A module with no audit line has no axiom gate even after it compiles,
so wiring it buys a typecheck and nothing else.  The exceptions —
`ProblemXWitness`, `STW22ConditionalNegativeSolution`, and the
`SphereOddDegree` `_closed` endpoints — are precisely the modules that have
caught something.  That is not a coincidence and it is the argument for putting
a `#audit_closed_axioms` on each layer's public result as it lands, rather than
at the end.

## Sweep 13, 2026-09-05 — correcting sweep 12, and the orphan gate now reads untracked debris

**Correction to sweep 12.**  Two claims were made there; one holds and one does
not, and the one that does not changes what the number means.

*Holds.*  `GroupApproximation.lean` really was broken.  `git diff` showed the
`ProblemXWitness` import appended after the module docstring, which is a syntax
error in Lean 4.  It has since been repaired — the import now sits at line 3308
and the docstring begins at 3310 — so the root parses again.

*Does not hold.*  The orphan count going 281 → 2744 was **not** caused by that
break.  The cause is that a **2344-module vendored FLT tree** now sits at
`GroupApproximation/ThirdParty/FLT/`.  It is deliberately untracked and
`.gitignore`d — the ignore rule records that it was assessed on 2026-09-05 and
found to contain no algebraic topology this campaign needs, and exists so the
snapshot sweep cannot commit it and the remote-build rsync does not carry it —
but `scripts/check.py --list-orphans` walks the **filesystem**, not the index,
so it counts every one of those files as a corpus orphan.

The corpus is 6711 `.lean` files on disk, 2344 of them untracked FLT.  Filtering
that tree out:

```
orphans reported by the gate :  2632
orphans in ThirdParty.FLT    :  2344   (untracked, gitignored, not part of the corpus)
real orphan count            :   287   (was 281 one sweep earlier)
```

So nothing catastrophic happened to the wiring; the campaign's orphan trend is
unchanged.  What happened is that **the gate started measuring something else**,
and it did so silently, with exit code 0 and a well-formed list.  Any lane
reading `2632` in the next few hours will draw a false conclusion, and this file
would have drawn one too had the root break not sent me looking.

Two durable points from this.

* **The orphan gate cannot distinguish a tracked module from local debris.**
  Any untracked `.lean` under `GroupApproximation/` inflates it.  Until
  `check.py` filters by `git ls-files`, the number to quote is
  `--list-orphans` minus anything under an ignored path, and this file will
  quote it that way from here.  `tmp/nk06.lean`, `tmp/names.lean`,
  `tmp/names2.lean` and `tmp/diag2.lean` are also loose in the tree.
* **A gate can break in the direction of alarm as well as reassurance.**  This
  file has spent twelve sweeps on gates that pass when they should fail.  This
  is the other kind: a gate that failed loudly, for a reason that had nothing
  to do with what it was measuring, and would have had a lane rewiring
  something that was never broken.

## Sweep 14, 2026-09-05 — Problem 2B is closed at the statement level

`Analysis/STW22AntipodalFactorialPair.lean:112`:

```lean
theorem antipodalFactorialNegativeSolutionToProblemXXII_of_borsukUlam
    (hBU : ComplexOddMapCommonZero) :
    IsFactorialTraciallyCompletePair antipodalDesignatedTraces ∧
      antipodalDesignatedTraces =
        Set.range (canonicalExtension antipodalAllTracesGauge_isCoordinateNormComparison) ∧
      ¬ AllTracesUniformTwoContinuous antipodalDesignatedTraces ∧
      ¬ DesignatedTracesAreAllTraces antipodalDesignatedTraces
```

**That is Problem XXII.**  The first conjunct is the hypothesis the endpoint
was missing at baseline; the third and fourth refute both of CCEGSTW Question
1.1's forms; the second pins what `X` is, so a reader cannot be handed a
different trace set than the one the factoriality claim is about.  The module's
own docstring names the finding it closes — *"This is the conjunction that
`STW22NegativeSolution` was missing: the first component is the hypothesis of
the problem, and without it the remaining components refute a strictly weaker
statement."*

The route there is worth recording because each step was a real discharge and
not a weakening: `STW22FactorialCore` proved the face condition from CCEGSTW
Prop 3.23(iv) with `X = T(A)`; `STW22TraciallyCompletePair` assembled
Definition 3.4 and Definition 3.13 at `designatedTraces hr`; `16d6705bd`
**deleted** the faithfulness hypothesis rather than assuming it, on the ground
that the coordinate norm comparison `r n * q n z ≥ ‖z‖` already forces a
gauge-null element to vanish coordinatewise; `STW22AntipodalFactorialPair`
instantiated the whole thing at the antipodal pair.

**Four things still stand between this and a verified target 2**, and none of
them is mathematics:

1. **The build error is unfixed.**  `STW22AntipodalBaseCoordinateMeasures.lean:29`
   still reads `private theorem antipodalCounterexampleBlock_nonemptyTraceFamily`,
   so sweep 10's nine instance failures and four `sorryAx` poisonings stand.
   Everything above has been written against a compiler that has not seen it.
2. **`STW22AntipodalFactorialPair.lean` carries no `#audit` line at all.**  The
   new endpoint therefore has no axiom gate, in a file whose immediate
   neighbour is currently poisoned.  It needs `#audit_axioms` (the theorem has
   a leading binder, so not `_closed`).
3. **There is no unconditional form.**  The only occurrence of
   `antipodalFactorialNegativeSolutionToProblemXXII` in the corpus is its own
   declaration; `complexOddMapCommonZero_unconditional` is a theorem, so the
   application is one line, and *that* is the declaration that should carry
   `#audit_closed_axioms` and be the one cited.
4. **`negativeSolutionToProblemXXII` still holds the name.**  It is now the
   weaker of two theorems while the stronger one has the accurate content.
   Leaving the better name on the weaker statement is the baseline defect
   relocated, not repaired.

**Target 2's verdict, restated:** the topological input is machine-checked, the
statement is now the problem, and what remains is one `private` keyword, one
audit line, one application, and a green build.

## Sweep 15, 2026-09-05 — a commit describing 2,344 modules that are not in the repository

`2851ec220` is titled *"thirdparty: vendor a generic 2,344-module slice of
Anthropic's FLT formalization"* and its message asserts *"1123 theorems, 1123
proof modules, 97 definition files, no sorry/axiom/unsafe"*, plus `INDEX.md`,
`ATTRIBUTION.md` and `NOTICE`.

What `git ls-files` shows under that path:

```
GroupApproximation/ThirdParty/FLT.lean                                        (1222 lines, aggregator)
GroupApproximation/ThirdParty/FLT/Definitions/Def_Mathlib_Algebra_IsDirectLimit.lean
GroupApproximation/ThirdParty/FLT/UPSTREAM.md
```

Three files.  One `.lean` module of the claimed 1220.  `INDEX.md`,
`ATTRIBUTION.md` and `NOTICE` are absent from git **and** from disk.  The
`.gitignore` still carries `GroupApproximation/ThirdParty/FLT/**` with exactly
those three exceptions, under a comment stating the tree is ignored *"so the
snapshot sweep cannot commit it"* and was *"found to contain no algebraic
topology this campaign needs"* — a rationale now standing against a commit that
vendors it as useful.

**The measurable hazard.**  `ThirdParty/FLT.lean` is committed with 1220
`import` lines, of which **1219 name modules that exist neither in git nor on
disk** (checked both).  The FLT directory on this machine is down to one
`.lean` file; the other 2343 are gone.  So a committed file on main cannot
compile anywhere, by anyone.  It is orphan, so nothing is red today — and it is
one root import from taking the build down.  The corpus had exactly **one**
dangling project import at sweep 12; it now has **1220**.

**The audit problem, which is the one that belongs to this lane.**  The commit
asserts "no sorry/axiom/unsafe" and "1123 theorems" about code that is not in
the repository.  Neither claim is checkable by anybody — not by this lane, not
by CI, not by a referee.  That is worse than an unproved lemma: an unproved
lemma can be pointed at.  A trust assertion about absent code is the exact
shape this file exists to refuse, and it is recorded here in those terms.

Three outcomes are fine and the current one is not: land the 1220 modules
(with the `NOTICE` and `ATTRIBUTION` files, which Apache-2.0 §4(d) requires be
retained on redistribution); or revert `FLT.lean` and `UPSTREAM.md` and keep
the assessment in `notes/`, where a prose claim belongs; or leave the tree
ignored as it was.  An aggregator on main importing 1219 files that do not
exist, described by a message asserting properties of them, is the worst of
the available states.

None of this touches the three targets — no FLT module is in any target's
import closure — and this lane has changed nothing.  It is recorded because
the corpus's trust surface is what this file is for, and because a later
reader finding `ThirdParty/FLT.lean` on main deserves to know what it is.

---

## Sweep 16, 2026-09-05 — mandate change, two self-corrections, and X(1) becomes a machine result

### Vocabulary change: CONDITIONAL-ON-X is now a failure state

The user's instruction is now *"we need literally all of it"*.  A named-`Prop`
residue is no longer an acceptable terminal state for any target.  This file
keeps recording residues with the same precision — that does not change — but
**CONDITIONAL-ON-X is from here a defect tracked to closure, not a verdict a
target may end on.**  The three verdicts available at the end are
UNCONDITIONAL, or a named open obligation, or NOT-YET-STATED.  Nothing is
"done" while it carries one.

### VOID window (ENOSPC), 2026-09-05

Between roughly **16:35 and 17:05 local**, the data volume ran under 1 GiB free
and hit 0; one of this lane's tool calls died with `ENOSPC`.  Cause: a 1.8 GiB
shallow clone of `anthropics/fermats-last-theorem` in the shared scratchpad,
since deleted (`fe8a55d82`); a second idle duplicate was reclaimed later.

**Every build, `--audit` run, and gate result produced inside that window is
VOID — neither red nor green.**  On a full disk `remote-build.sh` can fail on
the *sync* leg, which reads as a build failure and is not one, and a log can
truncate mid-write.  Anything from that window must be re-run, not believed and
not disbelieved.  Known casualty: the lead's first `ProblemXWitness` probe died
without writing a log.

### Self-correction 1 — this lane's XXII probe was stale, by five minutes

Sweep 10 recorded `STW22ConditionalNegativeSolution` failing with nine
`∀ (n : ℕ), Nonempty (TracialState (AntipodalCounterexampleBlock n))` synthesis
failures and four `sorryAx` poisonings.  **That result is superseded.**  The
probe's source sync ran at **16:12:55**; `d14e7b91b` — *"name the antipodal
nonempty-trace family so the conditional core elaborates"* — landed at
**16:18:02**, five minutes later, and `instNonemptyTracialStateAntipodalFamily`
now sits at `STW22ConditionalNegativeSolution.lean:66`.  Verified here, both
the instance and the two timestamps.

The finding was true of the tree it was run against and is the reason the fix
exists; it is **not** true of the tree today, and this file will not carry it
as a live defect.  The lead's probe (tag `lead-xxii`) is the re-run and will
report the job count.  This lane is not duplicating it.

Recorded because the staleness rule this file has been applying to other lanes
applies to it first: *a probe certifies the source it synced, not the source
that exists when you read the log.*  Mine did not, and I did not notice —
`xxii-factoriality` did.

### Self-correction 2 — the concurrent-build count was 3× too high

Sweep 11 reported "22 concurrent `remote-build.sh` processes" with five
duplicated targets.  Wrong instrument.  `pgrep -f remote-build.sh` matches the
`/bin/zsh -c source …snapshot…` wrapper that every tool call spawns, because
the wrapper's command line *contains* the string; and for a batched invocation
it matches once per target name inside the quoted argument.  Filtering wrappers
leaves **7 real invocations**, two of them `--sync-only`.  There was no
`LIXProjectiveSpaceModel ×4` and no `ProblemXWitness ×2`.

Corrected predicate, published so no other lane repeats it:

```sh
# wrong: counts wrapper shells and batched target names
pgrep -f "remote-build.sh"
# right: match the command, not the whole line
ps -eo command= | grep -E '^(bash )?scripts/remote-build\.sh'
```

Same family as this file's earlier `homologyπ` regex truncation (sweep 4).
Two instrument errors in sixteen sweeps, both in this lane's own tools, both
found by someone else reading the number.  **A verification lane's instruments
need the same scepticism as the corpus**, and this file's numbers should be
read with that applied.

### Target 1 is now a machine result

`brown-x1-verify` ran `scripts/ProblemXVerify.lean` on acn112.  At
`not_problemX1Statement`: leading binder **false**, axioms
`[propext, Classical.choice, Quot.sound]`, statement closure **27974**
constants of which **21** are in `GroupApproximation` — `FiniteModel` and its
four fields, `finiteModelDecidableEq`, `finiteModelFintype`, `TracialState` and
its two fields, `hsNorm`, `hsNormSq`, `normTrace`, `ProblemX1Statement`,
`Quasidiagonal.{AmenableTraceModel, IsAmenableTrace, IsCompletelyPositiveOnMatrices,
IsQuasidiagonalTrace, QuasidiagonalTraceModel}` and the two `.mk`s.
**Literature packages named by the statement: none.**  That matches this file's
hand read at sweep 1 exactly, name for name.

The filter is **not vacuous**: `TikuisisWhiteWinterInput`, `AmenableNuclearInput`
and `AmenableUCTInput` all exist inside `ProblemX`'s import closure and are
simply not reached.  A gate that could not have failed would have proved
nothing; this one could have.

`ProblemX.lean` itself is green at current source (tag **61312**, 3940 jobs),
printing the axiom line for `not_problemX1Statement`.  **One honest caveat, from
the lane that ran it**: `--run` execs `lake env lean` and has *no* job count, so
3940 belongs to the module build and not to the driver; and there is no
moved-count baseline against which to prove tag 61312 re-elaborated rather than
replayed.  The test — touch `ProblemX.lean`, rebuild, watch the count move off
3940 — has not been run.  So target 1's row is: **statement closure machine-verified;
module green; replay not yet excluded.**

**Two traps that lane found, both worth more than the result.**

1. **A `def X : Prop` on `zeroInputEndpoints` checks nothing.**
   `statementConstants` reads a declaration's *type*, and the type of
   `def LiteralFactorizationProperty : Prop` is `Prop` — closure size **0**.
   Not clean: *nothing asked*.  The theorem `literalFactorizationProperty` has
   closure 48892, of which 263 in `GroupApproximation`, and zero roster
   packages — that is the walk that means something.  This is why `365a823a5`
   seeds the **theorem** and not the `Prop`.  Generalized: **any `def _ : Prop`
   listed as a quarantine root is an inert entry.**  Belongs in
   `metadata/LITERATURE_QUARANTINE.md`; this lane does not own that file and
   has flagged it rather than edited it.
2. **`KirchbergKazhdanQuasidiagonalInput`**
   (`NinetyNineProblems/KazhdanQuasidiagonalTraces.lean:107`, Brown Lemma
   4.1.11 / Kirchberg) is an unproved literature package that is **not** on
   `literaturePackages`.  Today it is always an explicit leading hypothesis, so
   nothing advertises it — but the roster would not catch it if that changed.
   It cannot be resolved until `scripts/Audit.lean` can run.

**And the audit still cannot run at all**: `remote-build.sh --audit` fails on a
missing `GGT/HullSCLemma49Correction.olean`.  So the quarantine gate added at
`365a823a5` remains unfired corpus-wide; what has fired is the standalone
driver, which is a different and narrower instrument.

### Target 3: grade held open, not lowered

`lix-obstruction`'s mod-2 Wu route removes every one of the five library-scale
inputs this file listed at sweep 3 — no K-theory, no Bott periodicity, no Chern
character, no integral Künneth, no Chern-character integrality.  The lead
checked the arithmetic independently: the Wu instance producing the top class
carries coefficient `r − 2`, usable exactly when `r` is odd; `lix-design`'s
`ℂP¹` counterexample has `r = 4` (dead) and `lix-obstruction`'s `ℂP²` has
`r = 5` (live), and **every tower stage has `r = 2^{i+1} + 1`, odd**.

So this file withdraws the quotation of revision 1's *"no unconditional Lean
route to the parity obstruction at feasible cost"* as the campaign's position.
It was the position when written and is not now.

**The verdict does not change and the reason moves.**  Target 3 is incomplete
because of **the general tower stage**, not because of missing K-theory:
`lix-obstruction` has closed `Y = pt` and `Y = ℂP²`; the induction needs some
`i ≥ 1` with `binom(k + 2 − i, i)` odd, which **fails for certain `k`, first at
`k = 1`**.  Also recorded, as a correction the lanes made to the lead: `Y = ℂP²`
alone does **not** suffice, because the tower needs Corollary 4 at every stage
and the doubling `r_{i+1} = 2 r_i` is forced by multiplicity matching.  The one
genuinely new foundation is Steenrod squares up to Cartan — below Bott, and on
a base (`SingularCohomology`, `CupProduct`, `CohomologyCupProduct`,
`CochainCupLeibniz`, `MayerVietoris`) that already exists here.

The sweep-3 pre-registered rank check **stands and now applies to the Wu route
too**: `F = 1 − x xᴴ` over `S⁵` has rank 2, so `1²` is the hard comparison and
`1³` is two lines from the trace.

### The CP^d model question, resolved

Sweep 2 flagged two projection models of `ℂP^d`.  Current state, checked
directly: `AlgTop/ComplexProjectiveBasic.lean` line 1 is
`import GroupApproximation.Analysis.LIXProjectiveSpaceModel`, it defines **no
type**, and `IsLineProj` has **zero occurrences repo-wide**.  The surviving
model is `GroupApproximation.STW59.cpSet d = {q | IsStarProjection q ∧ q.trace = 1}`
over **Mathlib's** `IsStarProjection`, with `abbrev CP d := ↥(cpSet d)`;
`AlgTop.CPn` is its lemma layer.  One model, and it is the program note's
model on the nose.  Nothing to merge.

What the flag did surface was worse than a duplicate and is now fixed:
`IsLineProj` was used in four places (`ComplexProjectiveHyperplane.lean:39,40,69`,
`ComplexProjectiveChart.lean:49`) and **defined nowhere**, invisible because
`autoImplicit` is on (sweep 9).

### Foundation lanes now in scope

Seven lanes are building what Mathlib lacks, all for the target-3 obstruction,
all producing orphan modules.  Added to this file's inventory:

| lane | modules |
|---|---|
| `found-bundle-calculus` | `AlgTop/BundleCalculus*.lean` |
| `found-cohomology-ring` | `AlgTop/{SingularCohomology,CupProduct,Spheres,Kunneth}.lean` |
| `found-cpn-cohomology` | `AlgTop/ComplexProjective*.lean` |
| `found-chern-classes` | `AlgTop/Chern*.lean` |
| `found-ktheory-bott` | `KTheory/*.lean` → repointed to Steenrod squares |
| `found-euler-class` | `AlgTop/Euler*.lean` → mod-2 only |
| `found-mapping-torus-parity` | `AlgTop/MappingTorusParity.lean` → Wu's formula |

The instantiation check the lead asked for is now a standing column: **for each
foundation theorem a target-3 endpoint depends on, does the campaign actually
apply it to the concrete `H_i`, `E_i`, `F`?**  A Chern-class API nobody can
instantiate is not progress.  Nothing to report on it yet — no target-3
endpoint exists to depend on anything.

## Sweep 17, 2026-09-05 — the sphere-model fork, and no duplicate declarations

Answering the three things the lead asked this lane to watch in the foundation
half of the campaign.

### (1) Model collisions — one found, and it is `S⁵`

**`S⁵` exists twice, in incompatible types, with nothing bridging them.**

| | type | carries |
|---|---|---|
| `STW59.sphereFive` (`Analysis/LIXBlockProjections.lean:117`) | `Set (Fin 3 → ℂ)`, `:= unitVectors (Fin 3)` — its own docstring says "the **plain** product space" | `hopfCol` (:249), the block projections, hence `F(x) = 1 − x xᴴ` |
| `SphereOddDegree.Sphere n` (`SphereOddDegree/Basic.lean:19`) | `↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)` | `borsuk_ulam`, the odd-degree theorem, **and the whole `AlgTop` cohomology stack** |

The second row is the one that makes this urgent.  Checked by import: every
foundation module that will compute the parity obstruction —
`AlgTop/{CupProduct, CupAssoc, CrossProduct, SingularCohomology,
SingularChainFree, CochainLeibniz, OddDegreeOfHomeomorphism}` — imports
`SphereOddDegree`.  **No `LIX*` module imports it at all.**  So the mod-2
cohomology will be computed about `Sphere 5` in `EuclideanSpace ℝ (Fin 6)`,
while the projections it is supposed to be computing the Chern classes *of*
live over `↥sphereFive` in `Fin 3 → ℂ`.

`EuclideanSpace ℝ (Fin 6)` is `PiLp 2` — a different type from `Fin 6 → ℝ`,
which is different again from `Fin 3 → ℂ`.

**No bridge exists.**  Grepped every `LIX*` and `AlgTop/*` module for a
homeomorphism or `≃ₜ` relating them: nothing.  The nearest thing in the tree is
`Topology/OddMapNormalization.realToComplex`
(`EuclideanSpace ℝ (Fin (2n+2)) → (Fin (n+1) → ℂ)`, proved continuous and
injective), which is not stated as a homeomorphism of spheres and is not on any
LIX import path.

This is the expensive kind of fork rather than a dead end.  The spaces really
are homeomorphic — finite dimension, equivalent norms,
`unitVectors (Fin 3) = {x | ∑ ‖x i‖² = 1}` is exactly the ℓ² unit sphere — so it
is provable.  But it is **not definitional**, so both halves keep compiling
green while being about different spaces, and the mismatch surfaces only when
someone applies Wu's formula to `F`: the latest possible moment and the most
expensive.  Reported to `lix-design` by name, with the cheap fix (land
`↥STW59.sphereFive ≃ₜ SphereOddDegree.Sphere 5` now; Mathlib's
`PiLp.continuousLinearEquiv` gives the norm half and `realToComplex` the
realification half).

### (2) Statements that assume what they prove — nothing to report yet

The instantiation column stays empty for a reason worth stating: **no target-3
endpoint exists**, so no foundation theorem is yet depended on by anything.
`grep ProblemLIX` over the corpus returns nothing.  `lix-design` has accepted
that the named `Prop` that *is* Problem LIX lands first, before anything is
proved about it, over Mathlib's `unitary` and `Subgroup.pathComponentOne` plus a
generic `KOne` with no mention of the counterexample.  This lane will audit it
against exactly that when it appears; until then the check has no subject.

The sphere fork above is the first concrete instance of the shape the check is
aimed at: a foundation API that cannot, as things stand, be applied to the
campaign's concrete objects.

### (3) Duplicate declarations — none in the foundation directories

Indexed **59459 qualified names across 4352 files** (excluding the untracked
FLT tree), with block-comment tracking so docstring prose is not mistaken for
declarations.  **Zero exact collisions in `AlgTop/`, `KTheory/`, `Topology/` or
`Analysis/LIX*`.**  Eight repo-wide, all in `GGT/` and `Higman/`, and all eight
are `private`/public pairs — Lean mangles private names per module, so they do
not clash.  Checked each rather than reporting the raw count.

**Instrument note, the third this campaign.**  The first run of this scan
reported dozens of collisions on words like `is`, `of`, `and` and `as`: the
declaration regex was matching *prose inside docstrings* whose continuation
lines happen to begin with `theorem`, `class` or `def`.  Fixed by tracking
`/- … -/` depth.  Three instrument errors in seventeen sweeps — the `homologyπ`
truncation, the `pgrep` wrapper over-count, and this — and in each case the raw
number looked like a finding.  **The rule this lane now applies to itself: no
count leaves this file without a spot-check of the individual rows behind it.**

## Sweep 18, 2026-09-05 — this lane passed a vacuous guard; the lane caught it

### Self-correction 3, and the worst one

At sweep 14 this file audited `xxii-factoriality`'s four guards and passed all
four.  **Guard 4 was vacuous and this lane endorsed it in writing** — the
words used were *"this is the conjunct I would have asked for if you had not
written it."*

The conjunct was `antipodalDesignatedTraces = Set.range (canonicalExtension …)`.
But `STW22DesignatedTraces.lean:47` reads

```lean
abbrev antipodalDesignatedTraces : Set (TracialState AntipodalCompletionAlgebra) :=
  Set.range (canonicalExtension antipodalAllTracesGauge_isCoordinateNormComparison)
```

so the conjunct is `rfl`.  It certified **nothing**.  It was there to stop
"X is a face" being satisfied by a conveniently chosen `X`, and it could not
have, because it was true by definition of `X`.

`xxii-assembly` found it, not this lane, and replaced it (`fb2907ed1`) with the
conjunct that has content — CCEGSTW Proposition 3.15:

```lean
∀ σ : TracialState AntipodalCompletionAlgebra,
  σ ∈ antipodalDesignatedTraces ↔ IsUniformTwoContinuousOn antipodalDesignatedTraces σ
```

That one is a two-sided theorem: forward is that every canonical extension is
2-continuous, backward is that every 2-continuous trace *is* a canonical
extension by density — and it is exactly what makes "not all traces are
2-continuous" and "`X` is not all of `T(M)`" two readings of one failure.

**This is the failure mode the lane was explicitly assigned to catch** — *"a
conjunct that unfolds to something trivially true is worse than an absent
one"* — and it walked past it on the first reading.  The lesson is specific
and now standing: **a conjunct of the form `X = <definition of X>` is `rfl`;
check every equational conjunct against the `def`/`abbrev` of its own left-hand
side before crediting it.**  An `abbrev` makes this invisible at the use site,
because the reader sees a name and not its unfolding.

Four self-corrections in eighteen sweeps: `homologyπ` regex truncation, the
`pgrep` wrapper over-count, the docstring-prose match, and this one.  The first
three were instruments; this one was judgement, and it is the one that matters,
because a verification lane that certifies a vacuous guard has done worse than
not looking.

### The FLT aggregator is gone

Sweep 15's finding is resolved.  `GroupApproximation/ThirdParty/FLT.lean` — the
file committed with 1220 imports of which 1219 named modules that existed
nowhere — **no longer exists**.  Tracked under that path now: two files, the
single `Def_Mathlib_Algebra_IsDirectLimit.lean` and `UPSTREAM.md`
(`fe45e99f8`, "keep the generic FLT slice packed, with a statement catalogue").

Corpus-wide structural state, re-measured across 4360 project modules on disk:

```
modules with dangling project imports :  0      (was 1220)
import cycles                         :  0
```

Both clean.  The 1219-dangling-import window on main lasted roughly one hour.

### Standing counts

Orphans excluding the untracked FLT tree: **305**.  Gates unchanged at 36 and
136.  Real concurrent builds, using the corrected predicate: **1**.

## Sweep 19, 2026-09-05 — the fork is one space wide, and the K-theory layer passes

### Narrowing sweep 17: `S⁴` was never forked

`lix-design` supplied a fact this file's report omitted, and it changes the
framing rather than the finding.  In the same file, one line above `sphereFive`:

```lean
abbrev sphereFour : Set (EuclideanSpace ℝ (Fin 5)) := Metric.sphere 0 1     -- :114
abbrev sphereFive : Set (Fin 3 → ℂ)               := unitVectors (Fin 3)    -- :117
```

and `SphereOddDegree.Sphere n := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)`.
Checked directly: `Fin (4+1)` reduces to `Fin 5`, so **`↥sphereFour` is
definitionally `Sphere 4`**.

So `lix-spaces` did **not** adopt a rival sphere convention.  `S⁴` is already on
the cohomology model; only `S⁵` diverged, and it diverged for a substantive
reason — `F(x) = 1 − x xᴴ` needs `x` to be a complex vector.  Sweep 17's finding
stands; its framing was one space too wide, and the corrected version is that
this is a one-space bridge problem, not a two-model architecture.

### Ruling accepted, and the invariant that makes it auditable

`lix-design` rules **bridge, do not unify**, and the reasoning is right for a
reason worth recording: cohomology is a homotopy functor, so every cohomology
fact transports across a homeomorphism for free, whereas `1 − x xᴴ` transports
across nothing and would need rewriting at every use site.  Bridging puts one
conversion at a handful of joins; unifying puts one at every occurrence of `F`,
`hopfCol` and every block projection, permanently.

The bridge is also cheaper than this file costed it.  `realToComplex`
(`Topology/OddMapNormalization.lean:80`) is already the right map at `n = 2`
— `EuclideanSpace ℝ (Fin 6) → (Fin 3 → ℂ)` — with continuity and injectivity
proved.  What is missing is (a) `∑ i, ‖realToComplex 2 x i‖² = ‖x‖²`, which is
`Complex.sq_abs` plus a reindex over the even/odd pair and is exactly the
equation `unitVectors (Fin 3)` is defined by; (b) surjectivity, immediate from
(a); (c) the homeomorphism, which needs **no inverse construction** —
`Continuous.homeoOfEquivCompactToT2`, with `sphereFive.instCompactSpace`
(`LIXBlockProjections.lean:119`) already in the tree.

**The auditable invariant, now a standing row in this file.**  A bridge alone
only defers the failure mode: both halves still compile green about different
spaces until someone remembers to transport.  The discipline that closes it is

> every cohomology fact consumed on the C\*-side must be **stated over
> `sphereFive`**, obtained once from its `Sphere 5` counterpart through the
> bridge; `Topology/SphereModelBridge.lean` must be the **only** LIX-side
> module importing `SphereOddDegree`.

**Baseline, measured now: the invariant HOLDS.**  Zero modules among
`Analysis/LIX*`, `Analysis/CStarKOne*` and `KTheory/*` import `SphereOddDegree`.
The bridge itself does not exist yet — no `Topology/SphereModelBridge.lean`, no
`sphereFiveHomeoSphere` anywhere in the corpus.  A second LIX-side importer
appearing is the signal that someone is transporting ad hoc, and this file will
flag it by name.

### The K-theory layer passes the genericity check — the first layer that does

The instantiation column asked whether a foundation API can actually be applied
to the campaign's concrete objects.  Its dual is whether the API has been
contaminated *by* them.  `lix-design` raised the worry that `KOne` may already
be shaped by the counterexample.  Measured, across every declaration in
`Analysis/{CStarKOne, CStarKOneInjectivityCriterion, CStarUnitaryComponent,
SequentialGroupColimit}.lean` and `KTheory/{Basic, BlockMoves, Functorial,
MatrixProjection}.lean`, searching for `sphereFive`, `sphereFour`, `hopfCol`,
`stageRank`, `LIX`, `antipodal`, `cpSet`, `CP`, `STW59`:

**Zero counterexample-specific names in any declaration.**  The single textual
hit is a docstring line in `CStarKOneInjectivityCriterion.lean:18` — *"This is
the load-bearing reduction for STW Problem LIX"* — which is prose, not a
dependency.  The import graph corroborates it: `CStarUnitaryComponent` and
`SequentialGroupColimit` import **only Mathlib**, and the `KTheory/*` chain
reaches nothing outside itself and `FiniteCStarMurrayVonNeumann`.

So `K1Injective`, `KOne`, `kappa` and the refutation criterion are generic
statements about an arbitrary unital C\*-algebra, exactly as
`metadata/THREE_TARGETS_STATUS.md`'s pre-registered check 4 required, and the
worry is unfounded.  Recorded as a pass because this file has spent nineteen
sweeps recording failures and a layer that is clean deserves the same
precision.

**`ProblemLIX` still does not exist.**  `grep` over the corpus returns nothing.
It is a gating requirement on `ktheory-k1`, and target 3 stays NOT-YET-STATED
until it lands — over Mathlib's `unitary` and `Subgroup.pathComponentOne` plus
a generic `KOne`, before anything is proved about it.

## Sweep 20, 2026-09-05 — the instantiation check gets its first data point

### `found-chern-classes` ran the instantiation check on itself, and it is a partial pass

`01efd56ad` lands `AlgTop/ChernPolynomialModel.lean`, which instantiates the
whole Chern layer at `MvPolynomial ι ℤ` with `X j` playing `h_j`, and checks
that (2.1) and the above-the-rank vanishing come out:

```lean
def bundleH : TotalChern (MvPolynomial ι ℤ)
theorem chernClass_bundleH_top …
theorem chernClass_bundleH_eq_zero {k : ℕ} (hk : (∑ j ∈ s, d j) < k) …
theorem trivial_mul_bundleH …
```

Its own commit message is exactly right about what it is: *"Proves nothing new;
nothing should import it"* — a smoke test done **before** the join rather than
at it, *"so that the cohomology lane does not discover an interface problem only
at the moment it has a ring to offer."*  That is the discipline this file has
been asking for, applied by a lane to itself without being asked.

**It is a partial pass and the distinction matters.**  `MvPolynomial ι ℤ` is a
*proxy* ring, not the campaign's object.  What this establishes is that
`TotalChern`'s abstract `CommRing` interface is usable at some commutative ring
and that (2.1) survives contact with a real one — genuinely worth knowing, and
the cheapest possible way to know it.  What it does **not** establish is that
the API applies to the cohomology ring of `∏_j ℂP^{d_j}`, which does not exist
yet.  The instantiation column therefore reads, for `found-chern-classes`:
**interface verified at a proxy; not yet instantiated at the campaign's
objects.**  That is the first non-empty entry in that column, and it is the
right shape for an entry this early.

### A cross-vocabulary duplicate, found and recorded by its own lane

`60f8f857e` records that `isUnit_natCast_pos`
(`AlgTop/ChernNewtonDischarge.lean:40`) and `isUnit_natCast_of_pos`
(`AlgTop/ChernNewtonSquareZero.lean:128`) are the same five-line fact under two
names, kept apart deliberately so the live (2.7) module does not import the
superseded one that exists only for `MappingTorusParity`'s import — with a
stated collapse condition.

Worth recording for what it says about this file's own instrument: **the exact
qualified-name scan of sweep 17 could not have found this**, because the names
differ.  It is the same cross-vocabulary class as the `MurrayVonNeumannEquiv` /
`BundleCalculus.MvNEquiv` pair (sweep 9) and the `CP^d` pair (sweep 2), and in
all three cases a human reading found it and the name index did not.  A
duplicate declared under two names is invisible to every mechanical check this
lane has; the only defence is a lane recording its own, which is what happened
here.

### Two prose overclaims retracted by their own lanes

`9e64b59ee` ("do not claim in prose what the file does not prove") and
`38a2bd415` ("correct a false claim in the hlow docstring").  Both are lanes
correcting docstrings that asserted more than the file establishes.  Recorded
because `metadata/LITERATURE_QUARANTINE.md`'s standing hazard is a claim that no
gate reads — a docstring is exactly that, and two were wrong.

### Standing rows

| row | state |
|---|---|
| orphans (excl. untracked FLT) | 308 |
| dangling project imports | 0 |
| import cycles | 0 |
| gates | 36 / 136 unchanged |
| LIX-side modules importing `SphereOddDegree` | **0** — invariant holds |
| `Topology/SphereModelBridge.lean` | does not exist |
| `ProblemLIX` | does not exist |
| real concurrent builds | 1 |

## Sweep 21, 2026-09-05 — what actually blocks `ProblemLIX`, and the trap inside it

`lix-design` reports that no simplicity predicate exists.  Verified
independently rather than accepted, since it is a claim about what was checked:
searching `def|abbrev|structure|class` against `*[Ss]imple` across
`GroupApproximation/` and `STW/` (excluding untracked FLT) returns only
`IsPurelyInfiniteSimpleUnitalRing` (manuscript-local, `Ring`, not C\*),
`PropositionSimple := IsSimpleGroup H`, the Choquet/Bauer **simplex** family,
and simplicial-set names (`awCastAssocSimplex`).  **Nothing in the corpus states
simplicity of a C\*-algebra.**  Confirmed.

So `ProblemLIX` is blocked on one small generic definition — and
`lix-design`'s point about ordering is right and is this file's own standing
concern: **`IsSimpleCStar` landing after `lix-limit` proves simplicity of the
specific limit is the same failure mode as an endpoint landing after the
refutation.**  It is now a tracked row.

### The trap in that definition, which is not the one being watched

Mathlib at the pin has `IsSimpleRing` and `IsSimpleOrder`.  **Neither is the
right notion**, and reaching for one is the obvious shortcut.  A C\*-algebra is
simple when it has no nontrivial **closed** two-sided ideal; `IsSimpleRing` asks
for no nontrivial *algebraic* two-sided ideal, which is strictly stronger.

The direction of the error is worth being precise about, because it is the
opposite of the usual one.  `ProblemLIX = ∀ A, IsSimple A → K1Injective A`, so
strengthening `IsSimple` makes the hypothesis harder to satisfy and therefore
makes **`¬ ProblemLIX` harder to prove**, not easier.  **This severity claim was wrong and is corrected at sweep 23**: for a *unital*
C\*-algebra the two notions coincide, so `IsSimpleRing` is not stronger here and
cannot produce an undischargeable endpoint.  The general reasoning above holds;
the instance it was applied to does not.  The recommendation — quantify over
closed ideals — survives for different reasons, given at sweep 23.

### Two statement-shape facts, verified at source

Both `lix-design` claims check out, and both belong in the endpoint's docstring
rather than in an agent message.

1. **The order binders are forced by Mathlib, not chosen.**
   `CStarKOne.lean:35` is
   `variable (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]`,
   and at the pin every `CStarMatrix` instance requires
   `[PartialOrder A] [StarOrderedRing A]`, so `CStarMat n A` cannot be formed
   without them.  `ProblemLIX` must therefore quantify over them.
   That *looks* like quantifying over a choice of order, which would weaken
   `¬ ProblemLIX`.  It does not, and the reason is checkable at the pin:
   `Mathlib/Algebra/Order/Star/Basic.lean:79` defines
   `class StarOrderedRing … : Prop where le_iff : ∀ x y, x ≤ y ↔ ∃ p ∈ AddSubmonoid.closure (Set.range fun s => star s * s), y = x + p`
   — the order relation is *characterised* by the star structure, so any two
   `PartialOrder A` instances satisfying it have the same `≤`.  The argument
   holds.  **It should still be landed as a lemma rather than argued**, because
   Lean's elaborator does not know it: `K1Injective A` at two propositionally
   equal instances is two distinct terms, and a reader cannot see that the
   quantification is harmless.
2. **`KOne : Type u` is universe-polymorphic** (`CStarKOne.lean:32,65`), so
   quantifying `ProblemLIX` over `Type` is genuinely weaker than over `Type u`.
   `Type` is the right choice — the witness is a concrete separable algebra
   built from matrices over `C(X, ℂ)`, so it lives in `Type 0`, and it is what
   STW means.  Compare target 1, where `.{1}` is *forced* structurally
   (`MaximalGroupCStar` raises the level).  Here it is a free choice, and a free
   choice belongs in the docstring, not in whichever line the author typed
   first.

### Standing rows added

| row | state |
|---|---|
| `IsSimpleCStar` exists | **no** — blocks `ProblemLIX` |
| …defined over **closed** ideals (not `IsSimpleRing`) | pending |
| …landed **before** `lix-limit`'s simplicity theorem | pending |
| order-independence of `K1Injective` landed as a lemma | pending |
| universe choice recorded in the `ProblemLIX` docstring | pending |

## Sweep 22, 2026-09-05 — a stale RED is now propagating, and it is this lane's

### My superseded finding is being quoted as current fact

`665401966` ("instantiate the factorial pair at the antipodal gauge,
independent of the red chain") justifies itself with:

> *"STW22ConditionalNegativeSolution is currently red (nine instance-synthesis
> failures poisoning four declarations with sorryAx)"*

That is sweep 10's result, and sweep 16 recorded it as **superseded**.
`instNonemptyTracialStateAntipodalFamily` sits at
`STW22ConditionalNegativeSolution.lean:66` — verified again just now — and it
was added at 16:18:02 precisely to fix those nine failures.  **No probe has run
against that module since.**  So the module is not known red; it is **not
known**, and the last measurement predates the fix.

This is the mirror of the failure this file exists to catch.  Nineteen sweeps
have been about a stale GREEN being trusted; this is a stale **RED** being
trusted, propagating out of this lane's own report into another lane's design
justification.  A stale red is cheaper — it causes wasted work rather than a
false claim — but it is the same defect, and this file published it.

**The architectural decision it produced is right anyway**, which is worth
saying separately so the correction is not read as an objection: stating the
factoriality half against `antipodalAllTracesGauge` directly, so it depends only
on the coordinate norm comparison and not on the conditional-core chain, is
better decoupling regardless of whether that chain is red. The premise is stale;
the conclusion is sound.

**Standing rule tightened, applying to this file first:** a probe result carries
the timestamp of its *source sync*, and it stops being evidence the moment a
commit touches its closure.  Sweep 10's entry now reads RED (16:12:55 sources,
superseded 16:18:02) rather than RED.

### A green claim without a job count

`5d0760709` — *"SequentialGroupColimit and CStarMatrixBlockInclusion are green.
Probe round 3: both build clean"* — carries no job count.  The campaign rule,
which this lane asked for and the lead adopted, is that a green claim reports
the terminal `Build completed successfully (N jobs)` line, because a count that
does not move on a real change means the probe replayed a stale olean rather
than rebuilding.  Round 3 following two rounds of real fixes makes a genuine
rebuild very likely — this is a bookkeeping gap, not a suspected false green —
but the number is the evidence and it was not recorded.

### Standing rows

| row | state |
|---|---|
| orphans (excl. untracked FLT) | 309 |
| dangling project imports / cycles | 0 / 0 |
| `Analysis/LIX*` or `KTheory/*` importing `SphereOddDegree` | **0** — invariant holds |
| `Topology/SphereModelBridge.lean` | does not exist |
| `ProblemLIX` | does not exist |
| `IsSimpleCStar` | does not exist |
| `STW22ConditionalNegativeSolution` | **unknown** — last probe predates its fix |

## Sweep 23, 2026-09-05 — correcting sweep 21's severity claim

`lix-design` challenged sweep 21's claim that stating `ProblemLIX` with
`IsSimpleRing` would produce **an endpoint nobody can ever discharge**.  They
are right and I checked their argument at the pin rather than accepting it.

**The general reasoning stands; the instance does not.**  It is true that
`ProblemLIX = ∀ A, IsSimple A → K1Injective A` inverts the usual direction, so a
*stronger* `IsSimple` makes `¬ ProblemLIX` harder rather than vacuous.  What is
false is the premise that `IsSimpleRing` is stronger **for the algebras
`ProblemLIX` quantifies over**.

Verified at `81a5d257`:

* `Mathlib/RingTheory/SimpleRing/Defs.lean:27` —
  `class IsSimpleRing (R) [NonUnitalNonAssocRing R] : Prop where simple : IsSimpleOrder (TwoSidedIdeal R)`.
  Algebraic two-sided ideals, no closure condition.  Sweep 21 was right about
  that much.
* `Mathlib/Analysis/CStarAlgebra/Classes.lean:38` —
  `class CStarAlgebra (A) extends NormedRing A, StarRing A, CompleteSpace A, CStarRing A, …`.
  **`NormedRing` is unital**, so every algebra `ProblemLIX` ranges over is unital.
* `Mathlib/Analysis/Normed/Ring/Units.lean:84,88` —
  `nonunits.subset_compl_ball : nonunits R ⊆ (Metric.ball (1 : R) 1)ᶜ` and
  `nonunits.isClosed`, under `variable [NormedRing R] [HasSummableGeomSeries R]`.
* and the side condition is free: `Mathlib/Analysis/SpecificLimits/Normed.lean:279`
  gives `instance [NormedRing R] [CompleteSpace R] : HasSummableGeomSeries R`,
  which a `CStarAlgebra` satisfies automatically.  I checked this specifically,
  because "it is a short lemma" is the kind of claim that fails on a missing
  instance.

So the argument goes through: a proper two-sided ideal `J` of a unital Banach
algebra contains no unit, hence `J ⊆ nonunits`, which is closed and misses `1`;
so `closure J` is a proper *closed* two-sided ideal, C\*-simplicity kills it, and
`J = 0`.  With the converse trivial, **C\*-simple ⟺ `IsSimpleRing` for a unital
C\*-algebra.**  My `K(H)` intuition — C\*-simple with the finite-rank operators as
a dense proper ideal — is correct and is exactly the *non-unital* case, which is
why the general statement was true and its application here was not.

**The recommendation is unchanged and the reasons are better.**  Define
`IsSimpleCStar` by **closed** two-sided ideals, because:

1. **Fidelity.**  STW Problem LIX means C\*-simple.  An endpoint stated with
   `IsSimpleRing` is not *visibly* the problem STW asked, and a referee would
   have to know the equivalence to see that it is.  An endpoint should say what
   the problem says.
2. **A theorem smuggled into a definition.**  The equivalence needs unitality.
   Stating the endpoint with `IsSimpleRing` makes it silently depend on a lemma
   nobody has written — and `lix-limit` will prove the *closed*-ideal statement
   anyway, since the manuscript's positive-cutdown argument (Lemma 5) produces
   closed ideals.  So the bridge lemma is needed either way; the only choice is
   whether it is discovered now or at the join.

And land the bridge explicitly:

```lean
theorem isSimpleCStar_iff_isSimpleRing (A) [CStarAlgebra A] [Nontrivial A] :
    IsSimpleCStar A ↔ IsSimpleRing A
```

so that a later reader wondering whether the campaign picked a weak notion can
see that it did not.

**Tracked row amended** from *"would be unprovable"* to **"wrong notion to
state; the equivalence must be landed rather than assumed"**.

Fifth correction to this lane's own output in twenty-three sweeps, and the first
that was a **severity** error rather than an instrument or a missed check: the
finding was real, the recommendation was right, and the reason attached to it
was wrong in a way that would have misdirected whoever acted on it.  Worth
separating, because a correct recommendation resting on a false reason is the
harder kind to catch — nobody re-examines advice they are already following.

## Sweep 24, 2026-09-05 — the LIX residue is cancelled; a look-alike endpoint appears

### Target 3's residue is gone, and the verdict vocabulary changes with it

`lix-obstruction` reports that the mandate amendment cancelled their third task:
there will be **no `TwistedCancellationFailure`** from that lane, and Lemma 2 is
being assembled as a theorem.  So target 3 has no named `Prop` to be
conditional on, no `zeroInputEndpoints` question, and the CONDITIONAL-ON row is
retired rather than closed.  **Verdict unchanged: NOT-YET-STATED**, and now for
the plainest possible reason — the statement does not exist.

### Pre-registered check 1 passes, and the arithmetic is verified here

The rank check registered at sweep 3, before any of this existed:

* `F(x) = 1 − x xᴴ` for `x` a unit vector in `ℂ³` is `1₃` minus the rank-one
  projection onto `ℂx`, so `trace F = 3 − 1 = 2` and its pointwise rank is 2;
* `1²` has rank 2;
* `p_H` for `H = ⊕_j L_j^{⊕ d_j}` has rank `m = Σ_j d_j`.

So `F ⊕ p_H` and `1² ⊕ p_H` both have pointwise rank `2 + m` **at every
point**.  The ranks match exactly, the statement is not refutable from the
trace, and it is the genuinely hard one.  **Check 1 passes.**

The hazard it was registered against is real and narrower than expected:
`lix-obstruction` notes the manuscript's `V` is `1³ ⊕ H` while the comparison
bundle is `1² ⊕ H`, so **a 3-versus-2 slip is one character wide**, and they
will state both ranks explicitly wherever Lemma 2 appears.  The rank bookkeeping
already exists in source — `LIXBlockProjections.lean:225,239` prove
`trace H_i = ∑_{j<i} r_j` (i.e. `rank H_i = r_i − 2`) and `rank E_i = r_i`
in untruncated form — which is the right way to hold it.

### A look-alike endpoint, in a module named for the endpoint

`Analysis/LIXEndpointStatement.lean:91`:

```lean
theorem exists_cstarAlgebra_not_k1Inj {P : Type u → Prop} (hP : P A)
    (h : ∃ u : unitary A, u ∉ unitaryComponentOne A ∧
      diagOne u ∈ unitaryComponentOne (CStarMat 2 A)) :
    ∃ (B : Type u) (_ : CStarAlgebra B), P B ∧ ¬ K1Inj B :=
  ⟨A, inst, hP, not_k1Inj_of_witness h⟩
```

`P` is a **free variable**.  The theorem is true for every `P` because it
repackages its own hypothesis `hP`; it says nothing whatever about simplicity,
and it is the most endpoint-shaped declaration in the corpus for target 3.

**The declaration is not the defect and its docstring is honest** — it says
outright that substituting `lix-limit`'s conjunction of simplicity, separability
and nontriviality for `P` "turns this into the STW LIX endpoint", and even gives
the one-line direct term.  As an assembly schema it is fine.

**The hazard is the surroundings.**  A theorem of the shape
`∃ B, CStarAlgebra B ∧ P B ∧ ¬ K1Inj B`, living in a file called
`LIXEndpointStatement.lean`, at a moment when `ProblemLIX` **does not exist**
and `IsSimpleCStar` **does not exist**, is one citation away from being reported
as "LIX is stated in Lean".  This file records it now so that citation cannot
happen quietly: **`exists_cstarAlgebra_not_k1Inj` is not an endpoint and must
not be cited as one until `P` is instantiated at a proved simplicity
predicate.**  It is the same shape as the `rfl`-true conjunct of sweep 18 —
something that certifies nothing while looking exactly like the thing that
would.

### `K1Inj` is not a gratuitous rename — it is the order fix

`LIXEndpointStatement.lean:67` defines `K1Inj A := K1Injective A` with
`k1Inj_iff` as `Iff.rfl`, which reads at first like the cross-vocabulary
duplication this file has flagged three times.  It is not.  The two `local
instance`s above it supply `CStarAlgebra.spectralOrder` and
`CStarAlgebra.spectralOrderedRing`, so `K1Inj` is `K1Injective` **with the
canonical spectral order pinned** — the predicate then depends on nothing but
the C\*-structure.

That directly addresses sweep 21's tracked concern about `ProblemLIX`
quantifying over `[PartialOrder A] [StarOrderedRing A]`: stated over `K1Inj`
there is no order quantification left to justify.  Tracked row *"order-
independence of `K1Injective` landed as a lemma"* is **superseded** — pinning
beats proving invariance, and the endpoint should be stated over `K1Inj`.

### The simplicity ownership gap is narrower than reported

`lix-obstruction` raised §5 simplicity as an unowned ownership gap.  Measured:
`Analysis/LIXSimplicity.lean` exists, 270 lines, and works over the **right**
notion — `{I : Ideal B} [I.IsTwoSided] (hI : IsClosed (I : Set B))` — with
`posCut`, `IsFull`, `exists_ge_mem_ideal_of_nonneg` and
`eq_top_of_stagewise_full`, which is the positive-cutdown argument.  So the
general theorem *is* being built, over closed ideals, exactly as sweep 23
recommended.

What is missing is narrower and still real: **a named `IsSimpleCStar`
predicate, and the application of `eq_top_of_stagewise_full` to the specific
limit algebra.**  Without the second, the chain is still an implication into an
uninhabited conclusion, which is pre-registered check 3.

### Two modules asked to be probed, both unverified

`Analysis/LIXObstructionComplementUnitary.lean` (234 lines, imports **Mathlib
only**, the sole proof of the polar-decomposition step in the tree) and
`Analysis/LIXObstructionLowPowerSums.lean` (109 lines, imports only
`AlgTop/ChernPowerSums`).  **Neither contains a single `#audit` line** — which
their own lane volunteered — so there is nothing to be misled by and equally
nothing that would show they compile.  Both are recorded as UNVERIFIED, and
their lane has been saying so in every report, which is the right conduct and
is noted as such.

## Sweep 25, 2026-09-05 — target 3's open mathematics is now one named step

### The crux, named

`532e29eb5` narrows target 3 to a single open step, and it is worth recording
precisely because it is the first time this campaign has been able to name one:

> *"The chain has steps 1–3 and 7; **step 6, the bridge from one transverse zero
> to a nonzero top class, is the only open mathematics in target 3.**"*

The decomposition given makes Poincaré duality drop out rather than be proved:
`N` has one top cell, so `N ∖ {pt}` retracts to the `(2r−1)`-skeleton and
`H^{2r}` of it vanishes; the localization map is therefore surjective, and a
surjection `F₂ → F₂` is an isomorphism.  What remains is the mod-2 local degree
of an invertible linear map — not a Thom isomorphism.  The reasoning is sound as
stated: one top cell gives the retraction, and surjectivity between
one-dimensional `F₂` spaces is invertibility.

**The distinction this file must keep visible: that is a paper result, not a
Lean one.**  `532e29eb5` is a `research:` commit.  Steps 1–3 and 7 are done on
paper; **zero of the chain is compiled**, and target 3's three tracked
deliverables are all still absent — `ProblemLIX`, `IsSimpleCStar` (and
`isSimpleCStar_iff_isSimpleRing`), and `Topology/SphereModelBridge.lean` with
`sphereFiveHomeoSphere`.  A campaign that can name its one open step is in a far
better position than one that cannot, and it is still NOT-YET-STATED.

The same commit independently flags the simplicity ownership gap this file
escalated at sweep 24 — *"nobody owns the unconditional simplicity of the
inductive limit, without which the whole chain is an implication into an
uninhabited conclusion"* — reaching the same conclusion from the other
direction, which is corroboration rather than an echo.

### Second consecutive green claim without a job count

`fa86fdb1a` — *"Probe round 4: SequentialGroupColimit, CStarMatrixBlockInclusion
and CStarUnitaryComponent all build"* — again carries no job count, after
`5d0760709` did the same and after this lane asked for it with the reason.

As before, this is **not** a suspected false green: round 4 followed real fixes
(the `noncomputable` cascade below `CStarMatrix.instCStarAlgebra`, and a
`simp only` that applied `mul_smul_comm` before `add_mul` could distribute), and
each round has found genuine errors, which is probing working.  But two in a row
makes it a fleet convention gap rather than an oversight, and it is escalated as
such rather than asked of the lane a third time.  **The count is the only thing
that distinguishes a rebuild from a replay**, and without it a downstream reader
has to re-run the build to learn what the builder already knew.

### Standing rows

| row | state |
|---|---|
| `ProblemLIX` | absent |
| `IsSimpleCStar` / `isSimpleCStar_iff_isSimpleRing` | absent |
| `Topology/SphereModelBridge.lean` / `sphereFiveHomeoSphere` | absent |
| `Analysis/LIX*` or `KTheory/*` importing `SphereOddDegree` | **0** — invariant holds |
| orphans (excl. untracked FLT) | 315 |
| target 3 open mathematics | **one step**, on paper: step 6, transverse zero → nonzero top class |
| target 3 compiled | none |
