# cs-endpoint

Owns `Analysis/CStarKOne.lean`, `Analysis/CStarKOneInjectivityCriterion.lean`,
`Analysis/CStarKOneWhitehead.lean`, `Analysis/CStarSymmetryComponent.lean`,
`Analysis/LIXEndpointStatement.lean`,
`Manuscript/NinetyNineProblems/ProblemLIX.lean`.

## 1. GREEN

**`Build completed successfully (2996 jobs)`**, probe round 6, with a genuine
`✔ Built GroupApproximation.Analysis.LIXEndpointStatement (9.1s)` in the same
log — a build, not a `Replayed`. Targets:

```
GroupApproximation.Analysis.CStarKOne
GroupApproximation.Analysis.CStarSymmetryComponent
GroupApproximation.Analysis.CStarKOneInjectivityCriterion
GroupApproximation.Analysis.LIXEndpointStatement
GroupApproximation.Analysis.CStarKOneWhitehead
```

All five of the lane's `Analysis/` modules.  Round 5 gave the same count; round
6 repeats it after a docstring rewrite, so the count is stable across a real
edit rather than a replay of one measurement.  Per-module `Built` evidence:

| module | first genuinely built |
|---|---|
| `Analysis/CStarKOne` | round 3 (job ≤ 2993 of 2996; not among the two `✖`) |
| `Analysis/CStarSymmetryComponent` | round 3, same |
| `Analysis/CStarKOneInjectivityCriterion` | round 4, `✔ Built … (15s)` |
| `Analysis/CStarKOneWhitehead` | round 4, `✔ Built … (18s)` |
| `Analysis/LIXEndpointStatement` | rounds 4 and 6, `✔ Built … (9.4s / 9.1s)` |

**Root wiring done by the lead** at `GroupApproximation.lean:3311–3320`: all
five, plus `CStarMatrixBlockInclusion`, `CStarUnitaryComponent` and
`SequentialGroupColimit`.  `CStarSimple` and `ProblemLIX` are not wired, which
is correct — the first is red.

**Genericity, argued structurally rather than by grep.**  The whole import
closure of `Analysis/LIXEndpointStatement` is six modules —
`SequentialGroupColimit`, `CStarUnitaryComponent`, `CStarMatrixBlockInclusion`,
`CStarKOne`, `CStarKOneInjectivityCriterion` and itself — and not one of them
is counterexample-specific.  So `KOne`, `kappa`, `K1Injective`, `K1Inj`,
`not_k1Inj_of_witness`, `diagOne` and `HasK1InjWitness` *cannot* mention the
counterexample: there is nothing in scope to mention.  That is stronger than
the name check, which was also run and also passes —

**reading the code with docstrings and comments stripped,** `KOne`, `kappa`, `K1Injective`, `K1Inj`, `not_k1Inj_of_witness`,
`diagOne`, `HasK1InjWitness` and every other declaration in
`Analysis/{CStarKOne, CStarKOneInjectivityCriterion, LIXEndpointStatement,
CStarUnitaryComponent, SequentialGroupColimit, CStarMatrixBlockInclusion}`
contain **zero** occurrences of the counterexample's vocabulary
(`LIX`, `CP`, `Sph`, `cpSet`, `Eproj`, `Hproj`, `Clutch`, `Chern`, `STW`,
`manuscript`, `counterexample`).  **Three** of the six —
`SequentialGroupColimit`, `CStarUnitaryComponent`, `CStarMatrixBlockInclusion`
— have zero project imports at all, counted with
`grep -c '^import GroupApproximation'` rather than from memory.  And
`K1Inj` does pin the order: `LIXEndpointStatement.lean:63,66` supply
`CStarAlgebra.spectralOrder` and `CStarAlgebra.spectralOrderedRing` as
`local instance`s, so `K1Inj A` depends on nothing but `[CStarAlgebra A]`.

## 2. AUTHORED, UNVERIFIED

* `Analysis/CStarKOneInjectivityCriterion.lean` — round-3 fix applied:
  `coe_diagOne_apply` needed the `omit [PartialOrder A] [StarOrderedRing A] in`
  that its neighbour `coe_diagOne` already had.
* `Analysis/CStarKOneWhitehead.lean` — round-3 fixes applied, see TRAPS for the
  `CStarMat` / `Matrix` seam.
* `Analysis/LIXEndpointStatement.lean` — `HasK1InjWitness` and
  `not_k1Inj_of_hasWitness` added.
* `Manuscript/NinetyNineProblems/ProblemLIX.lean` — **landed**, three
  declarations, each with an `#audit_axioms` line:
  * `ProblemLIX`, the statement, landed before anything is proved about it
    (route design §C.7);
  * `exists_simple_unital_not_k1Inj_of`, the assembly against hypotheses — one
    algebra plus its nontriviality, simplicity and `HasK1InjWitness` gives the
    existential;
  * `not_problemLIX_of_exists`, the existential to the negation of the printed
    universal.

  Between them there is no mathematics left, only an application, so the join
  is two lines.  Nothing in the file asserts `ProblemLIX` is false: all three
  carry `#audit_axioms` rather than `#audit_closed_axioms`, because each has a
  leading input.  Not yet compiled — it imports `Analysis/CStarSimple`, which
  is red.

`cs-simplicity`'s `Analysis/CStarSimple.lean` landed with exactly the shape
asked for below — `[CStarAlgebra A]` only, closed two-sided ideals, no
nontriviality conjunct, universe-polymorphic — so the first NEEDS item is
**discharged**.

## 3. NEEDS

### From `cs-simplicity` — one definition — **DISCHARGED**

Landed as `Analysis/CStarSimple.lean:77`

```lean
def IsSimpleCStar (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ I : Ideal A, I.IsTwoSided → IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤
```

with `isSimpleCStar_iff_isSimpleRing` beside it.  All four constraints below
are met.  Kept in the report because they are the reasons the endpoint reads
the way it does, not merely a request:

1. **Instance arguments: `[CStarAlgebra A]` and nothing more.**  In particular
   *not* `[PartialOrder A] [StarOrderedRing A]`.  `ProblemLIX` is stated over
   `K1Inj`, which has the spectral order baked into its body precisely so the
   endpoint quantifies over no order; a simplicity predicate carrying order
   instances would put the quantification straight back and undo sweep 24's
   fix.  `[Nontrivial A]` as an instance argument is also unwanted — see 3.
2. **Closed two-sided ideals**, not `IsSimpleRing` (`metadata/THREE_TARGETS_STATUS.md`
   sweep 23).  The equivalence is true for unital algebras and should be landed
   as `isSimpleCStar_iff_isSimpleRing`, but the endpoint must *say* what STW
   asked.
3. **Nontriviality is not a conjunct.**  The endpoint reads
   `Nontrivial A → IsSimpleCStar A → K1Inj A`, so `Nontrivial` is a separate
   hypothesis.  If `IsSimpleCStar` swallowed it, `ProblemLIX` would be
   redundant in a way a referee has to unfold a definition to see.
4. Universe-polymorphic (`Type u` / `Type*`); `ProblemLIX` instantiates at
   `Type 0`.

Nothing else is needed from this lane by me: the assembly never unfolds
`IsSimpleCStar`.

### From `cs-limit` — the algebra — **STILL OPEN**

`Analysis/LIXLimitTower.lean` has landed and carries the general machinery:
`CStarTower`, `Colim`, `iota`, `iota_injective`, and `instNontrivial` from
`Nontrivial (A 0)`.  What it does not yet carry is a **`CStarAlgebra` instance**
— `Colim` is a `NormedRing` and a `CStarRing`, but nothing supplies
`CompleteSpace`, so it is not a `CStarAlgebra` and cannot be the endpoint's
algebra.  The completion is the remaining gap on this side.

```lean
-- GroupApproximation/Analysis/LIXLimit*.lean
def LIXLimit : Type                       -- or whatever the limit algebra is called
instance : CStarAlgebra LIXLimit
instance : Nontrivial LIXLimit
theorem lixLimit_hasK1InjWitness : HasK1InjWitness LIXLimit
```

`HasK1InjWitness` is being landed by me in `Analysis/LIXEndpointStatement.lean`
as

```lean
def HasK1InjWitness (A : Type u) [CStarAlgebra A] : Prop :=
  ∃ u : unitary A, u ∉ unitaryComponentOne A ∧
    diagOne u ∈ unitaryComponentOne (CStarMat 2 A)
```

**Target that name rather than writing the existential out.**  `diagOne` and
`CStarMat 2 A` only elaborate under `[PartialOrder A] [StarOrderedRing A]`, and
`LIXEndpointStatement` fixes those to `CStarAlgebra.spectralOrder` /
`CStarAlgebra.spectralOrderedRing` through two `local instance`s.  A hypothesis
written out under a *differently named* pair of local instances is a different
term, and joining the two then costs a transport lemma.  Re-register the same
declarations instead:

```lean
attribute [local instance] GroupApproximation.instSpectralPartialOrder
                           GroupApproximation.instSpectralStarOrderedRing
```

### From `cs-simplicity` (second item) — still open

```lean
theorem lixLimit_isSimpleCStar : IsSimpleCStar LIXLimit
```

## 3b. ROOT WIRING PROPOSAL (for the lead; this lane does not touch the root)

Computed from the actual `import` lines, not from memory, by
`notes/lix-lane-reports/cs-endpoint-wiring.py` (walks `GroupApproximation/`, reads the
leading `import GroupApproximation.…` block of every module, does a coloured
DFS over the whole project graph, then a post-order over the closure of the
named targets).

* **Dangling project imports: 0.**  Every `import GroupApproximation.X` in the
  tree has a source file behind it.
* **Cycles in the whole `GroupApproximation/` import graph: 0**, checked
  transitively (grey-node DFS), not by looking at neighbours — a probe is blind
  to cycles because `lake` builds a DAG of what it can reach.
* The root imports **none** of the ten modules below yet.

Append in this order (dependencies first).  Twelve lines, not thirteen: the
comparison is against the root's **transitive** closure, so `Meta/AxiomGuard`
is not listed — the root already reaches it through
`Manuscript/NinetyNineProblems/ProblemX` (root line 2157).  Comparing against
the root's direct import list alone over-reports.

```
import GroupApproximation.Analysis.SequentialGroupColimit
import GroupApproximation.Analysis.CStarUnitaryComponent
import GroupApproximation.Analysis.CStarMatrixBlockInclusion
import GroupApproximation.Analysis.CStarKOne
import GroupApproximation.Analysis.CStarKOneInjectivityCriterion
import GroupApproximation.Analysis.LIXEndpointStatement
import GroupApproximation.Analysis.CStarSimple
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIX
import GroupApproximation.Analysis.CStarSymmetryComponent
import GroupApproximation.KTheory.MatrixProjection
import GroupApproximation.KTheory.BlockMoves
import GroupApproximation.Analysis.CStarKOneWhitehead
```

Lines 1 to 6 are green as of round 5 and can be wired now.  Lines 7 and 8 wait
on `Analysis/CStarSimple` going green.  Lines 9 to 12 are the Whitehead lemma
and its `KTheory` dependencies, also green as of round 5, and can be wired now
or last.

`CStarKOneWhitehead` is the Whitehead lemma (`K₁` is abelian).  Nothing in the
endpoint chain needs it — `not_k1Inj_of_hasWitness` never uses commutativity —
so it can be wired separately.

## 4. TRAPS

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
