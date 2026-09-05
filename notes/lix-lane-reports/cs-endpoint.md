# cs-endpoint

Owns `Analysis/CStarKOne.lean`, `Analysis/CStarKOneInjectivityCriterion.lean`,
`Analysis/CStarKOneWhitehead.lean`, `Analysis/CStarSymmetryComponent.lean`,
`Analysis/LIXEndpointStatement.lean`,
`Manuscript/NinetyNineProblems/ProblemLIX.lean`.

## 1. GREEN

**`Build completed successfully (2999 jobs)`**, probe round 7, targets

```
GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIX
GroupApproximation.Analysis.CStarKOne
GroupApproximation.Analysis.CStarSymmetryComponent
GroupApproximation.Analysis.CStarKOneInjectivityCriterion
GroupApproximation.Analysis.LIXEndpointStatement
GroupApproximation.Analysis.CStarKOneWhitehead
```

**All six modules of this lane are green**, including the endpoint.  The log
ends

```
✔ [2998/2999] Built GroupApproximation.Analysis.CStarSimple (10s)
ℹ [2999/2999] Built GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIX (10s)
Build completed successfully (2999 jobs).
```

and the three `#audit_axioms` lines each report exactly the classical three:

```
'ProblemLIX' depends on axioms: [propext, Classical.choice, Quot.sound]
'exists_simple_unital_not_k1Inj_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'not_problemLIX_of_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Per-module `Built` evidence, so that no green here rests on a replay:

| module | genuinely built in |
|---|---|
| `Analysis/CStarKOne` | round 3 (job ≤ 2993 of 2996; not among the two `✖`) |
| `Analysis/CStarSymmetryComponent` | round 3, same |
| `Analysis/CStarKOneInjectivityCriterion` | round 4, `✔ Built … (15s)` |
| `Analysis/CStarKOneWhitehead` | round 4, `✔ Built … (18s)` |
| `Analysis/LIXEndpointStatement` | rounds 4 and 6, `✔ Built … (9.4s / 9.1s)` |
| `Manuscript/…/ProblemLIX` | round 7, `ℹ Built … (10s)` |

Rounds 5 and 6 each gave `2996 jobs` for the five `Analysis/` modules, before
and after a real docstring edit, so that count is stable across an edit rather
than one measurement replayed.

**Root wiring**: the lead has `GroupApproximation.lean:3311–3320` carrying all
five `Analysis/` modules plus `CStarMatrixBlockInclusion`,
`CStarUnitaryComponent` and `SequentialGroupColimit`.  `CStarSimple` and
`ProblemLIX` are now green and can be added.

### The two verifications the brief asked for

**Genericity, argued structurally rather than by grep.**  The entire import
closure of `Analysis/LIXEndpointStatement` is six modules —
`SequentialGroupColimit`, `CStarUnitaryComponent`, `CStarMatrixBlockInclusion`,
`CStarKOne`, `CStarKOneInjectivityCriterion` and itself — and not one is
counterexample-specific.  So `KOne`, `kappa`, `K1Injective`, `K1Inj`,
`not_k1Inj_of_witness`, `diagOne` and `HasK1InjWitness` *cannot* mention the
counterexample: there is nothing in scope to mention.  Three of the six —
`SequentialGroupColimit`, `CStarUnitaryComponent`, `CStarMatrixBlockInclusion`
— have no project imports at all, counted with
`grep -c '^import GroupApproximation'` rather than recalled.

The weaker name check was run as well and also passes: with docstrings and
comments stripped, no declaration in those six modules contains any of `LIX`,
`CP`, `Sph`, `cpSet`, `Eproj`, `Hproj`, `Clutch`, `Chern`, `STW`, `manuscript`
or `counterexample`.

**`K1Inj` does pin the order.**  `LIXEndpointStatement.lean:63,66` supply
`CStarAlgebra.spectralOrder` and `CStarAlgebra.spectralOrderedRing` as `local
instance`s, and no global instance can produce a `PartialOrder` for an
arbitrary `CStarAlgebra`, so those are the only candidates and `K1Inj A`
depends on nothing but `[CStarAlgebra A]`.  Because they are `local`, they do
not leak into downstream instance search.

## 2. AUTHORED, UNVERIFIED

Nothing.  Every module this lane owns is green.

What is *absent* rather than unverified is the counterexample itself.
`Manuscript/NinetyNineProblems/ProblemLIX.lean` carries three declarations and
no claim that `ProblemLIX` is false:

* `ProblemLIX` — the statement, landed before anything was proved about it, as
  the route design's §C.7 requires.

  ```lean
  def ProblemLIX : Prop :=
    ∀ (A : Type) [CStarAlgebra A], Nontrivial A → IsSimpleCStar A → K1Inj A
  ```

* `exists_simple_unital_not_k1Inj_of` — one algebra plus its nontriviality, its
  `IsSimpleCStar` and its `HasK1InjWitness` gives the existential.
* `not_problemLIX_of_exists` — the existential to the negation of the printed
  universal, with no excluded middle in between.

All three carry `#audit_axioms` rather than `#audit_closed_axioms`, because
each has a leading input.  Between them no mathematics is left, only an
application: when the algebra exists, `exists_simple_unital_not_k1Inj` and
`not_problemLIX` are two lines and two `#audit_closed_axioms` lines.

## 3. NEEDS

### From `cs-simplicity`, the definition — **DISCHARGED**

Landed at `Analysis/CStarSimple.lean:77` with every constraint met:

```lean
def IsSimpleCStar (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ I : Ideal A, I.IsTwoSided → IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤
```

`[CStarAlgebra A]` and nothing more, so the endpoint quantifies over no order;
closed two-sided ideals rather than `IsSimpleRing`, with
`isSimpleCStar_iff_isSimpleRing` beside it; no nontriviality conjunct, so
`ProblemLIX`'s separate `Nontrivial A →` is not redundant; universe-polymorphic.
The assembly never unfolds it.

### From `cs-simplicity`, the file being green — **DISCHARGED**

`Analysis/CStarSimple.lean` was red for a while with three errors; `6f6e545f6`
fixed them and it builds.  The two diagnoses are kept in TRAPS because both are
general.

### From `cs-limit`, the algebra — **BLOCKING**

`Analysis/LIXLimitTower.lean`, `LIXLimitCompletion.lean` and
`LIXLimitMatrixTransport.lean` have landed;
`Limit := UniformSpace.Completion Colim` is the right shape and
`Analysis/CStarCompletion.lean:198` should supply its `CStarAlgebra` instance.
What I still need is a concrete algebra rather than the generic tower:

```lean
def LIXLimit : Type                       -- Type 0, not Type u
instance : CStarAlgebra LIXLimit
instance : Nontrivial LIXLimit
theorem lixLimit_hasK1InjWitness : HasK1InjWitness LIXLimit
```

`Type 0` is load-bearing: `KOne` is universe-polymorphic, so `ProblemLIX`
quantified over `Type` is genuinely weaker than over `Type u`, and a universe
slip there would silently weaken the endpoint.  **Checked, and it is fine**:
`cs-stages`' `Analysis/LIXStageAlgebra.lean:130` declares
`abbrev StageAlgebra (i : ℕ) : Type`, annotated `Type` rather than `Type*`, and
neither the colimit nor `UniformSpace.Completion` raises the level.

`HasK1InjWitness` is landed and green in `Analysis/LIXEndpointStatement.lean`:

```lean
def HasK1InjWitness (A : Type u) [CStarAlgebra A] : Prop :=
  ∃ u : unitary A, u ∉ unitaryComponentOne A ∧
    diagOne u ∈ unitaryComponentOne (CStarMat 2 A)
```

Its *statement* needs only `[CStarAlgebra A]` — the order instances live in the
definition's body — so it can be stated anywhere.  Its *proof* has to produce a
membership at those instances, which a term-mode `exact` reaches across and a
`rw` does not.  See TRAPS.

### From `cs-simplicity`, the second item — **BLOCKING**

```lean
theorem lixLimit_isSimpleCStar : IsSimpleCStar LIXLimit
```

## 3b. ROOT WIRING PROPOSAL (this lane does not touch the root)

Computed from the actual `import` lines by
`notes/lix-lane-reports/cs-endpoint-wiring.py`, which walks
`GroupApproximation/`, reads each module's leading `import GroupApproximation.…`
block, runs a coloured DFS over the whole project graph, and post-orders the
closure of the named targets.

* **Cycles in the whole `GroupApproximation/` import graph: 0**, checked
  transitively rather than at neighbours — a probe is blind to cycles because
  `lake` only builds the DAG it can reach.  No module imports the root, so the
  wiring itself cannot create one.
* **Dangling project imports: 0.**
* **Duplicate declarations: 0.**  147 top-level declarations across the nine
  modules below, checked as fully qualified names against every other `.lean`
  file in the tree.

The list, dependencies first.  Twelve lines, not thirteen: the comparison is
against the root's **transitive** closure, so `Meta/AxiomGuard` is absent — the
root already reaches it through `Manuscript/NinetyNineProblems/ProblemX` at
root line 2157.  Comparing against the root's direct imports over-reports.

```
import GroupApproximation.Analysis.SequentialGroupColimit      -- wired
import GroupApproximation.Analysis.CStarUnitaryComponent       -- wired
import GroupApproximation.Analysis.CStarMatrixBlockInclusion   -- wired
import GroupApproximation.Analysis.CStarKOne                   -- wired
import GroupApproximation.Analysis.CStarKOneInjectivityCriterion -- wired
import GroupApproximation.Analysis.LIXEndpointStatement        -- wired
import GroupApproximation.Analysis.CStarSimple                 -- GREEN, wire it
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIX -- GREEN, wire it
import GroupApproximation.Analysis.CStarSymmetryComponent      -- wired
import GroupApproximation.KTheory.MatrixProjection             -- wired
import GroupApproximation.KTheory.BlockMoves                   -- wired
import GroupApproximation.Analysis.CStarKOneWhitehead          -- wired
```

Ten of the twelve are already in the root at lines 3311 to 3320.  The two
outstanding are `CStarSimple` and `ProblemLIX`, in that order, and both are
green as of round 7.
`CStarKOneWhitehead` is the Whitehead lemma, that `K₁` is abelian; nothing in
the endpoint chain needs it, since `not_k1Inj_of_hasWitness` never uses
commutativity.

## 4a. INTEGRATION REVIEW (Sonnet continuation, 19:4x EDT)

Per the lead's brief for the Sonnet continuation of this lane: read the four C*-lanes'
current files directly on disk (not only their reports — `cs-stages` and `cs-clutching` had
no report file at all yet) and checked whether their exported signatures actually compose
into `HasK1InjWitness A`, `IsSimpleCStar A`, `Nontrivial A` for one concrete `A`.

**Finding: a single bottleneck, on `cs-stages`.**  Nothing in `LIXCornerAlgebra.lean`,
`LIXStageAlgebra.lean`, `LIXConnectingMapPoints.lean` or `LIXBlockProjections.lean` defines
the connecting map `φ_i : StageAlgebra i →⋆ₐ[ℂ] StageAlgebra (i+1)` (§1.2 item 2 of the
program note) or `Nontrivial (StageAlgebra 0)`, even though the pieces to build it already
exist: `LIXConnectingMapPoints.lean`'s `stagePoint i` (the dense point `x_i`) and
`LIXBlockProjections.lean:574`'s `Eproj_succ`, which gives the exact block shape
(`Eproj (i+1)` reindexed `= fromBlocks (pullMat (baseProj i) (Eproj i)) 0 0 (newBlock i)`) that
a twisted point evaluation has to fill the new block of. Sent `cs-stages-s` the concrete
construction route (message id `fdcbf3fb`).

This one gap is what blocks all three other C*-lanes at once, confirmed by reading their
current files rather than inferring from reports:
* `cs-limit-s`: generic tower/limit/matrix-transport/separable machinery is green (2999 jobs,
  unchanged since the snapshot) and exactly matches its report; the only thing it cannot do
  yet is instantiate `LIXLimit` concretely, because `CStarTower.ofInjective` needs `connect`/
  `connect_injective` as arguments. Nothing else to fix there (msg `2a2b23da`).
* `cs-clutching-s`: `LIXClutching.lean`/`LIXObstructionComplementUnitary.lean` untouched since
  16:3x (predate this run); `LIXGeneratorUnitary.lean` has the `su2`/Hopf-suspension building
  blocks but no concrete generator unitary `u` realized at the stage-algebra level yet, and no
  `LIXLemmaSix*.lean` exists — Lemma 6 needs `connect` to even state `v_i := φ_{0,i}(u)`.
  Corollary 4 and the `hdiag` half of the witness may be gettable now, independent of
  `connect` (msg `8537196e`).
* `cs-simplicity-s`: confirmed green at 2961 jobs (`a2cecadc6`, matches disk exactly);
  `StagewiseFullTower`/`isFullIn_of_isFull_map`/`isClosed_range` are correctly generic and
  ready. Its `full_stage` field also needs `connect` for the point-evaluation-summand
  argument, on top of needing `cs-limit`'s concrete `lixStage` (msg `d6f40934`).

No change to this lane's own six files; all still green at 2999 jobs. The two closed
theorems (`exists_simple_unital_not_k1Inj`, `not_problemLIX`) remain gated on
`HasK1InjWitness LIXLimit` and `IsSimpleCStar LIXLimit`, neither of which exists yet. Will
add them and probe the moment both peer lanes report those two names green.

## 4. TRAPS

* **Duplicate-declaration scan for the root wiring: clean.**  147 top-level
  declarations across the nine modules of the wiring proposal, checked as fully
  qualified names against every other `.lean` file in `GroupApproximation/`.
  Zero cross-module duplicates and zero internal ones.  Worth running because
  wiring an orphan into the root is exactly when a duplicate name first becomes
  a build error rather than a dormant one.
* **Two `instSpectralPartialOrder` declarations now exist and they do not
  collide.**  `Analysis/LIXEndpointStatement.lean:63` declares
  `GroupApproximation.instSpectralPartialOrder`;
  `Analysis/LIXLimitMatrixTransport.lean:36` (owned by `cs-limit`) declares
  `GroupApproximation.LIX.instSpectralPartialOrder`.  Different namespaces, so
  the root can import both.  Both are `local instance`, so neither leaks a
  `PartialOrder B` for every `CStarAlgebra B` into downstream instance search —
  which would have been much worse than a name clash.

  What survives is narrower: the two are definitionally equal but not the same
  term, so a `diagOne u` built under one is not syntactically the `diagOne u`
  of the other.  `HasK1InjWitness A`'s *statement* is unaffected, because it
  takes only `[CStarAlgebra A]` and the order sits inside the definition's
  body; only a `rw` aimed across the seam would fail, and a term-mode `exact`
  will not.
* **The first `ccprobe.sh` run on a fresh clone always fails, and it exits 0.**
  On a fresh clone the rsync itemizes the whole tree as changed, so the
  script's `$RM` accumulates four artifact paths per module for ~1300 modules
  and the remote command line exceeds `ARG_MAX`:

  ```
     cloned in 746s
  ==> changed since last sync:   (1300 files)
  ==> lake build …
  ccprobe.sh: line 40: /Users/user/msi-node/msi: Argument list too long
  [exited with code 0]
  ```

  No build runs, no `Build completed successfully` line appears, and the exit
  status is **zero** — so a lane checking only the exit code sees a pass.
  The rerun then failed differently: `$CHANGED` carries newlines and was
  interpolated into a double-quoted remote command, where a newline ends the
  `for` list, so any sync touching more than one module died with
  `syntax error near unexpected token`.  In a shared checkout with thirteen
  lanes writing, every sync touches more than one module.

  **Both are fixed upstream.**  The lead's `ccprobe.sh` now ships the changed
  list as a file (`cc-changed.txt`) and clears artifacts remotely from it,
  syncs by content (`rsync -c`), and exits non-zero unless the log contains
  `Build completed successfully`.  Recorded because the two failure modes cost
  a clone cycle each and because the first one is invisible to an exit-code
  check.
* **The clone is the bottleneck, not the build.**  Nine lanes ran `cp -al` of
  the same 25 GB tree at once; this lane's took 746 s and round 1 cost about
  35 minutes wall clock.
* **`CStarMat` is a type synonym with its own `Mul` and `Star`, and `rw` cannot
  cross it.**  `CStarMat n A` is `CStarMatrix (Fin n) (Fin n) A`, a plain `def`
  over `Matrix` (`Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:44`), but
  `CStarMatrix.instStar` is its own `⟨conjTranspose⟩` and the `Mul` comes
  through a bespoke `HMul` instance, both only *definitionally* equal to
  `Matrix`'s.  `Matrix.instOne`, by contrast, is shared verbatim
  (`inferInstanceAs`).  So every `rw [star_blockSum]` and
  `rw [blockSum_mul_blockSum]` in `CStarKOneWhitehead` failed with

  ```
  Did not find an occurrence of the pattern star (blockSum ?p ?q)
  Note: The target expression is not type-correct under the `instances`
  transparency level
  ```

  while the neighbouring `blockSumU_mul`, written in term mode as
  `Subtype.ext (blockSum_mul_blockSum _ _ _ _)`, compiled without complaint.
  That is the whole rule: **`exact` checks definitional equality at default
  transparency and crosses the synonym; `rw` matches instances syntactically
  and does not.**  The fix is not a coercion but a placement decision — state
  the arithmetic at `Matrix`, where its lemmas live, and cross the synonym once,
  by application, at the point where the `unitary (CStarMat _ A)` element is
  built.  A `show` at the `Matrix` type does not help either: the mixed
  application `permMat A e * blockSum p q` then asks for
  `HMul (CStarMat (n+n) A) (Matrix (Fin (n+n)) (Fin (n+n)) A) ?m`, which
  instance search cannot find for exactly the same reason.
* **The brief's error list is stale.**  `fa86fdb1a` ("noncomputable K_1 and a
  hand-rolled expansion") already carries a `noncomputable section` in
  `CStarKOne.lean`, so the five "consider marking it as noncomputable" lines
  and the two `CStarSymmetryComponent` lines quoted in the brief were measured
  before it.  Measured again before editing rather than fixed blind.
* **`#audit_closed_axioms` and `¬ P`.**  `auditClosedAxiomsOf`
  (`Meta/AxiomGuard.lean:83`) rejects a declaration whose elaborated type
  `isForall`.  `¬ ProblemLIX` is stored as `Not ProblemLIX`, an application,
  not a `.forallE`, so it passes — `ProblemX.lean:287` is the precedent.  A
  statement written as `ProblemLIX → False` would *not* pass.
