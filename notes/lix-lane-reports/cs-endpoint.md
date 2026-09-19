# cs-endpoint

Owns `Analysis/CStarKOne.lean`, `Analysis/CStarKOneInjectivityCriterion.lean`,
`Analysis/CStarKOneWhitehead.lean`, `Analysis/CStarSymmetryComponent.lean`,
`Analysis/LIXEndpointStatement.lean`,
`Manuscript/NinetyNineProblems/ProblemLIX.lean`.

## 1. GREEN

**`Build completed successfully (8698 jobs)`**, with
`ℹ Built GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIX (27s)` and
all six `#audit_axioms` lines reporting exactly
`[propext, Classical.choice, Quot.sound]`.

Everything this lane owns is green:

| module | job count |
|---|---|
| `Manuscript/NinetyNineProblems/ProblemLIX` | 8698 |
| `Analysis/LIXLemmaTwoProp` | 8671 |
| `Analysis/{CStarKOne, CStarSymmetryComponent, CStarKOneInjectivityCriterion, LIXEndpointStatement, CStarKOneWhitehead}` | 2996, twice, before and after a real edit |

Per-module `Built` evidence, so that no green rests on a replay: `CStarKOne` and
`CStarSymmetryComponent` in round 3 below the two `✖`; the criterion and
Whitehead in round 4 at `✔ Built … (15s / 18s)`; `LIXEndpointStatement` in
rounds 4 and 6 at `(9.4s / 9.1s)`; `LIXLemmaTwoProp` at `(20s)`; `ProblemLIX`
in rounds 7, 8 and the last at `(10s / 7.5s / 27s)`.

### LEMMA 2 IS THE SOLE HYPOTHESIS

`Manuscript/NinetyNineProblems/ProblemLIX.lean` at `df4f0b872`,
**`Build completed successfully (8723 jobs)`**, `PROBE GREEN`, zero occurrences
of `sorryAx` or an allowlist violation.  The count rose from 8706 with the new
import, which is what identifies the build as this change rather than a replay.

```lean
theorem not_problemLIX_of_lemmaTwo (h : LIX.LemmaTwoHolds) : ¬ ProblemLIX

theorem not_problemLIX_of_lemmaTwoInput
    (h : ∀ j : ℕ, CharClass.LemmaTwoInput (LIX.lixDD j)) : ¬ ProblemLIX
```

plus the separable variants of each.  `cs-clutching`'s
`LIX.lixLimit_hasK1InjWitness_of` discharged the witness, so **the entire
C⋆-side is a theorem**: stage algebras, connecting maps, inductive limit,
simplicity, separability, Lemma 6, Corollary 4, the `K₁` witness, and the
reduction of the printed problem to a single unitary.

The second form states the hypothesis unfolded, as `cc-thom`'s Step C and
`cc-wu`'s Step D at every stage.  So the distance from STW's printed question
to Lean is **three obligations in one lane behind one ladder**: the Thom class
datum and the nonvanishing of the relative Euler class on the odd side, and the
Chern splitting on the even side.

**Everything here is `#audit_axioms`, deliberately.**  `LemmaTwoHolds` is a
leading input, so `#audit_closed_axioms` would reject every one of them *by
design*.  Nothing in this file may advertise itself as closed while the
topology is unproved, and the lead's instruction to land the closed gate when
the witness arrived was one step early — the witness discharges the witness,
not Lemma 2.

**The closed file is written and held outside the working tree**, as
`scratchpad/cs-endpoint/closed_endpoint.patch.py`, not as an uncommitted edit.
The endpoint is root-wired, so an uncommitted edit here is one sweep away from
taking `main` down; held as a script it applies in one move and cannot land
early.  It carries `not_problemLIX`, `exists_simple_unital_not_k1Inj` and the
separable strengthening, all under `#audit_closed_axioms`.

`cc-lix-odd` has confirmed the target, and both halves were checked by them
against `origin/main` rather than assumed — the file path is free tree-wide and
the bare declaration name has no hits, so neither collides when it lands:

```lean
import GroupApproximation.CharClass.LemmaTwoClosed
theorem GroupApproximation.CharClass.lemmaTwoHolds : LIX.LemmaTwoHolds
```

It does not exist yet; what exists is `lemmaTwoHolds_of`, which still takes the
two-step input.  **They are deliberately not creating the module early** with
the three inputs as hypotheses to stabilise my import path, and their reason is
worth keeping: a *present* name with the wrong shape fails somewhere else and
reads as the consumer's bug, whereas an *absent* name fails immediately and
unmistakably.  So a failed run of the held patch means "not yet", never
"wrong".

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
What I still need is a concrete algebra rather than the generic tower.  **Superseded
2026-09-05 ~19:5x by `cs-limit-s`/`cs-simplicity-s`**: there is no separate `LIXLimit`
alias any more.  The canonical concrete tower is

```lean
def STW59.tower : LIX.CStarTower STW59.StageAlgebra :=
  LIX.CStarTower.ofInjective STW59.connect STW59.connect_injective
```

and the algebra this endpoint quantifies over is `STW59.tower.Limit` directly (`Type 0`,
since `StageAlgebra : ℕ → Type` is annotated `Type` not `Type*`, checked against
`Analysis/LIXStageAlgebra.lean:130`).  `[Nontrivial STW59.tower.Limit]` is free from
`[Nontrivial (StageAlgebra 0)]` via `CStarTower.instNontrivialLimit` (cs-limit, already
green).  What still needs to land:

```lean
theorem lixLimit_hasK1InjWitness : HasK1InjWitness STW59.tower.Limit
```

a direct application of `cs-limit`'s already-green `T.exists_unitary_witness` /
`hasK1InjWitness_limit` once `cs-clutching` supplies `u : unitary (StageAlgebra 0)`,
`hstage`, `hdiag` at `k = 0` (see `notes/lix-lane-reports/cs-limit.md` §3).

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

**Superseded 2026-09-05 ~19:5x**: `cs-simplicity` built a sharper bridge than a
stage-exposure API (`CStarTower.stagewiseFullTower` / `CStarTower.isSimpleCStar_limit`,
`Analysis/LIXSimplicityInstance.lean`, green at 2988 jobs) that consumes `cs-limit`'s raw
`CStarTower` plus a fullness hypothesis stated **entirely in finite-stage language** — no
stage-exposure names (`lixStage`, `lixStage_full`) are needed from `cs-limit` any more.
The one thing outstanding is still on `cs-stages`, now in its exact final form:

```lean
namespace STW59
def connect (i : ℕ) : StageAlgebra i →⋆ₐ[ℂ] StageAlgebra (i + 1)
theorem connect_injective (i : ℕ) : Function.Injective (connect i)
instance : Nontrivial (StageAlgebra 0)
theorem fullness (k : ℕ) (a : StageAlgebra k) (h0 : 0 ≤ a) (hne : a ≠ 0) :
    ∃ j, k ≤ j ∧ GroupApproximation.LIX.IsFull (STW59.tower.climb j k a)
```

(`0 ≤ a` under whatever `StarOrderedRing (StageAlgebra k)` instance the stage lane
installs — `cs-simplicity`'s new `nonneg_iff_of_injective` makes the choice irrelevant).
Then the whole instantiation is one line:

```lean
theorem STW59.isSimpleCStar : LIX.IsSimpleCStar STW59.tower.Limit :=
  STW59.tower.isSimpleCStar_limit STW59.fullness
```

Full authoritative recipe in `notes/lix-lane-reports/cs-simplicity.md` §3.

### Separability: taken, as a separate theorem, after `connect`

`cs-limit` has `CStarTower.separableSpace_limit`, conditional on
`∀ n, SeparableSpace (A n)`, and the program note §0 calls separability a bonus
conjunct if cheap.  Decision: **take it, but not by changing the specified
signature.**

`exists_simple_unital_not_k1Inj` lands exactly as the lead specified,

```lean
∃ (A : Type) (_inst : CStarAlgebra A), Nontrivial A ∧ IsSimpleCStar A ∧ ¬ K1Inj A
```

because that is what `not_problemLIX_of_exists` consumes and what the endpoint's
audit trail is written against.  Separability goes in a second, strictly
stronger statement beside it.  A referee reading the answer to Problem LIX then
sees the problem's own hypotheses and nothing else, and a reader who wants to
know the counterexample is separable finds it as a named fact rather than as a
conjunct that is not part of the question.

It is worth having: STW cite Villadsen for simple *separable* unital nuclear
examples defeating the surjectivity analogue, so the separable class is where
the question lives, and a counterexample needing nonseparability would be a
weaker answer.

Sequencing: cs-stages must not be asked for the per-stage `SeparableSpace`
instance until `connect` is green.  If it is not cheap, it is dropped; nothing
depends on it.

### The universe risk is retired, in Lean rather than in prose

`cs-limit` closed the one thing this lane could not check by reading.
`Analysis/LIXLimitCompletion.lean` now ends with three green `example`s: that
`Type`-valued stages give a `Type`-valued limit, that `CStarAlgebra` of the
limit really resolves through `CStarCompletion.completionCStarAlgebra`, and
that `Nontrivial` of the limit follows from `Nontrivial (A 0)` alone.

### INTERFACE SPECIFICATION for `cs-stages` and `cs-clutching` (2026-09-05 ~19:5x)

Read off the three consumers, all of which are green, so that the join costs
nothing.  Sent to `cs-stages-s` and `cs-clutching-s` by name.

**`connect`, from `CStarTower.ofInjective` (`Analysis/LIXLimitTower.lean:59`).**

```lean
def connect : ∀ n : ℕ, StageAlgebra n →⋆ₐ[ℂ] StageAlgebra (n + 1)
theorem connect_injective : ∀ n, Function.Injective (connect n)
```

Successor-indexed, and a **unital** `StarAlgHom` — not `→⋆ₙₐ[ℂ]`, not a `k ≤ i`
family, not a bare function with separate lemmas.  No norm or isometry lemma is
wanted: `ofInjective` discharges `norm_succHom` from injectivity through
`NonUnitalStarAlgHom.norm_map`.

**Nontriviality**: `instance : Nontrivial (StageAlgebra 0)` and nothing about
later stages, because `CStarTower.instNontrivialLimit`
(`Analysis/LIXLimitCompletion.lean:119`) asks only for `Nontrivial (A 0)`.

**Fullness, from `CStarTower.isSimpleCStar_limit`
(`Analysis/LIXSimplicityInstance.lean:195`).**  Match the binder shape exactly:

```lean
theorem fullness (k : ℕ) (a : StageAlgebra k) : 0 ≤ a → a ≠ 0 →
    ∃ j, k ≤ j ∧ GroupApproximation.LIX.IsFull (tower.climb j k a)
```

It is `T.climb j k a`, the raw recursion at `LIXLimitTower.lean:69`, not
`climbHom` and not a hand-rolled composite; `climbHom_apply` makes them `rfl`,
but stating it at `climb` keeps it syntactically matching.  `IsFull` is the
concrete finite-sum form at `LIXSimplicity.lean:183`, with no ideal-generation
API in it.

**The order instances nobody owns.**  `isSimpleCStar_limit` asks for
`[∀ n, PartialOrder (A n)]`, `[∀ n, StarOrderedRing (A n)]` and the same two on
`T.Limit`.  None is a global instance and none can be, so a lane must install
them locally from `CStarAlgebra.spectralOrder`.  Recommended owner:
`cs-stages`, because `0 ≤ a` in the fullness statement is already relative to
that choice.

**Lemma 6, from `hasK1InjWitness_limit` (`Analysis/LIXLimitWitness.lean:47`).**
The hypothesis is

```lean
hstage : ∀ (j : ℕ) (hj : k ≤ j),
  unitaryHom (T.climbHom hj) u ∉ unitaryComponentOne (A j)
```

— about the **tower's** iterated map, with `hj` an explicit argument, not about
`w_j` and not about a hand-rolled `φ_{k,j}`.  Corollary 4 composed with Lemma 6
gives it, but only if Lemma 6 is stated over `T.climb` from the start; a
hand-rolled composite is propositionally equal and not syntactically so, and
the join then costs a transport lemma plus its induction.

`hdiag : diagOne u ∈ unitaryComponentOne (CStarMat 2 (A k))` lives at stage `k`,
not at the limit, and **must be produced in term mode**.
`LIXLimitWitness.lean` works under `GroupApproximation.LIX.instSpectral*` while
`HasK1InjWitness`'s body was elaborated under `GroupApproximation.instSpectral*`;
both unfold to `CStarAlgebra.spectralOrder`, so `exact` crosses them and `rw`
does not.  See TRAPS.

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
import GroupApproximation.Analysis.CStarSimple                 -- wired (1b4a37c25)
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIX -- wired (1b4a37c25)
import GroupApproximation.Analysis.CStarSymmetryComponent      -- wired
import GroupApproximation.KTheory.MatrixProjection             -- wired
import GroupApproximation.KTheory.BlockMoves                   -- wired
import GroupApproximation.Analysis.CStarKOneWhitehead          -- wired
```

**All twelve now wired.**  The lead landed `CStarSimple` and `ProblemLIX` at
`GroupApproximation.lean:3321-3322` in `1b4a37c25` ("root: wire IsSimpleCStar
and the ProblemLIX statement (green at 2999 jobs)").  This root-wiring
proposal is now fully discharged; nothing left for the lead to add here.
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

## 3c. THE CONCRETE ASSEMBLY IS GREEN

`Build completed successfully (3019 jobs)`, with
`ℹ Built GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIX (9.4s)`.
`Manuscript/NinetyNineProblems/ProblemLIX.lean` now imports
`Analysis/LIXLimitSimple` and carries

```lean
theorem exists_simple_unital_not_k1Inj_of_limit
    (hsimp : IsSimpleCStar LIX.LIXLimit) (hwit : HasK1InjWitness LIX.LIXLimit) :
    ∃ (A : Type) (_inst : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleCStar A ∧ ¬ K1Inj A :=
  exists_simple_unital_not_k1Inj_of LIX.LIXLimit inferInstance hsimp hwit
```

`CStarAlgebra LIX.LIXLimit` and `Nontrivial LIX.LIXLimit` are resolved by
`inferInstance` at the endpoint rather than asserted, so the plumbing between
the construction and the endpoint is **proved**, not assumed.  All four
`#audit_axioms` lines report exactly `[propext, Classical.choice, Quot.sound]`.

**Neither hypothesis mentions an order**, and that is the design paying for
itself.  `IsSimpleCStar` takes `[CStarAlgebra A]` alone and `HasK1InjWitness`
keeps the spectral order inside its body, so `cs-limit`'s module can work under
`GroupApproximation.LIX.instSpectral*` and this one under
`GroupApproximation.instSpectral*` with no transport lemma and no agreement
about which `PartialOrder` term either wrote.

**Sequencing note that was briefly load-bearing.**  This edit was written, then
*parked outside the tree* for half an hour, because `ProblemLIX` is root-wired
and `cs-limit`'s `LIXLimitAlgebra` was red and flagged
*"AUTHORED, UNVERIFIED - do not wire yet"* in its own commit message.  Landing
the import then would have taken `main` down through the lead's periodic sweep,
not merely left a red orphan.  The rule: **once a module is root-wired, an
import is a commitment of the root build, and an in-flight peer module may not
be imported until it is green.**

**What is left in the whole chain**: two hypotheses, neither mine.

```lean
-- cs-stages
theorem STW59.fullness : ∀ (k : ℕ) (a : STW59.StageAlgebra k), a ≠ 0 →
  ∃ j, k ≤ j ∧ LIX.IsFull (LIX.lixTower.climb j k a)

-- cs-clutching, for some k and some u : unitary (STW59.StageAlgebra k)
hstage : ∀ (j : ℕ) (hj : k ≤ j),
  unitaryHom (LIX.lixTower.climbHom hj) u ∉ unitaryComponentOne (STW59.StageAlgebra j)
hdiag  : diagOne u ∈ unitaryComponentOne (CStarMat 2 (STW59.StageAlgebra k))
```

Then this lane's remaining work is exactly:

```lean
theorem exists_simple_unital_not_k1Inj : … :=
  exists_simple_unital_not_k1Inj_of_limit
    (LIX.lixLimit_isSimpleCStar STW59.fullness)
    (LIX.lixLimit_hasK1InjWitness u hstage hdiag)

theorem not_problemLIX : ¬ ProblemLIX :=
  not_problemLIX_of_exists exists_simple_unital_not_k1Inj
```

plus two `#audit_closed_axioms` lines.

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
* **A *wrong* instance winning at default priority looks exactly like a missing
  one.**  `STW59.StageAlgebra i` is a subtype of `C(X_i, CStarMatrix ι ι ℂ)`,
  and `CStarMatrix.instPartialOrder` gives that ambient a **pointwise** order
  which reaches the subtype through `Subtype.partialOrder`.  So
  `PartialOrder (STW59.StageAlgebra k)` synthesizes silently, to the wrong
  order; `StarOrderedRing` then fails and `CStarMat 2 (STW59.StageAlgebra k)`
  is not a `CStarAlgebra`.  The reported error is

  ```
  failed to synthesize CStarAlgebra (CStarMat 2 (STW59.StageAlgebra k))
  ```

  which reads as an absent instance and is caused by a present one.  Found by
  `cs-limit`; four of their six errors.  The fix is a **priority**, not a new
  instance:

  ```lean
  attribute [local instance 100000] GroupApproximation.LIX.instSpectralPartialOrder
                                    GroupApproximation.LIX.instSpectralStarOrderedRing
  ```

  Plain `attribute [local instance]` loses to `Subtype.partialOrder`.  Keeping
  the same two constants means no transport lemma anywhere.  My own diagnosis
  of this file pointed at elaboration order and a synthesis budget, and both
  were wrong.
* **A probe log and a `sed` of the same path can be about different bytes**, and
  I drew a false conclusion from exactly that.  `ccprobe.sh` rsyncs the whole
  shared working tree at the *start* of the run, uncommitted peer edits
  included.  I launched a probe, then read `LIXLimitAlgebra.lean` off disk and
  saw four diagnostic `example`s at lines 46 to 49 that were absent from the
  error list, and inferred that they had *passed* — which would have meant the
  instance was found in one position and not another.  They had not passed.
  `cs-limit` added them after the sync, so the built bytes never contained
  them, and the file I read was not the file that was compiled.  Verified after
  the fact: `git show 3079cad5e:…` has no such lines, `git show 6b56f0491:…`
  does.

  Two rules out of this.  **Reconstruct the built version before reasoning
  about which lines did or did not error** — `git show <commit>:<path>`, not a
  read of the working tree.  And **absence from an error list is not evidence
  of success**; it is equally evidence that the line was not there.

  The same aliasing bites in the other direction: `cs-limit` saw
  `LIXConnectingMap` build, fail at `:222` with byte-identical content at the
  same commit, then build again.  Re-run before reporting a bug in someone
  else's module.
* **"Light import closure" measured in project modules hides the Mathlib
  weight.**  `CharClass/LemmaTwoStatement`'s closure is 13 *project* modules
  and contains no cohomology, relative, Steenrod, Thom, projective-space or
  bundle module — which is what `cc-lix-odd` promised and what I verified.  But
  the probe runs at **8671 jobs** against roughly **3000** for the C⋆-side
  closure, so the mapping-torus and `ℂP` layer costs about 5.7k Mathlib jobs
  beyond it.  Both numbers are true and only one of them was in my first
  report.  When relaying "light", say which side it is light on.
* **I wrote a Mathlib name from memory and it did not exist**, which is the
  rule I had been holding other lanes to.  `Nat.pos_pow_of_pos` is gone at
  `81a5d257`; the name is `Nat.pow_pos`, taking base positivity with the
  exponent implicit.  One error, job 8671 of 8671, with the entire closure
  below it green.
* **A stale `cc-last.log` reads as a fix that did not take.**  After relaunching
  the probe I read the log on the node and saw the *same* error I had just
  fixed.  It was the previous run's log: the relaunched probe had not yet
  reached the build phase and had not truncated it.  This is the same aliasing
  as the entry below, in the opposite direction — there I read a file newer
  than the log, here a log older than the file.  **Wait on the probe's own
  completion signal; never conclude from a log you did not watch get written.**
* **`sorryAx` in an audit line can be Lean's error recovery, not anyone's
  `sorry`.**  `#audit_closed_axioms` reported
  `not_problemLIX_of_lemmaTwo_data depends on axioms outside the classical
  allowlist: [sorryAx]` while the two theorems it is built from both reported
  clean.  Nothing upstream had a `sorry`.  The real error was twelve lines
  earlier — `Unknown identifier not_problemLIX_of_exists`, because I had
  inserted the new section *above* the theorem it applies — and Lean recovered
  from the failed elaboration by filling the proof with `sorryAx`, which the
  audit then honestly reported.

  Two things worth keeping.  **Read the first error, not the loudest one**: an
  axiom-closure violation downstream of a failed elaboration is a symptom.  And
  the gate behaved exactly as designed — a proof that only *looked* complete
  because Lean papered over an error was refused, which is the case
  `#audit_closed_axioms` exists for and the one that is hardest to catch by
  eye.
* **Do not put a probe at the end of a compound background command.**  I ran
  `python3 …; grep -c …; bash ccprobe.sh … | tail -30` in one backgrounded
  call, and the "wait until the output file is non-empty" watcher fired on the
  first line the *python* printed, not on the probe.  The probe's own stdout
  then never reached the file, which held six bytes.  I was therefore about to
  read `cc-last.log` on the node for a verdict, which is the stale-log trap two
  entries down.

  What settled it instead, and is the general move: **look for something in the
  log that could only be there if the log is yours.**  I grepped the node's log
  for the audit line of the theorem I had just added, found it at
  `ProblemLIX.lean:298`, and only then read `Build completed successfully
  (8706 jobs)` as mine.  A job count alone would not have distinguished the two
  runs, because adding one theorem to an existing module changes no job count.
* **"I checked an hour ago" is not a check, in a tree five lanes commit to.**
  Asked whether the `M₂(M₂) ≅ M₄` flattening existed, I searched, found nothing,
  and said so — correctly, at the time.  Later I thanked `cs-clutching` for
  building it as a `StarAlgEquiv`, endorsing a duplicate: `cs-limit` had landed
  exactly that at 21:40, and had even told me they were sending `cs-clutching`
  the pieces.  The first answer was right; the endorsement was not, and nothing
  about the first licensed the second.  **Re-run the search before encouraging
  work, not only before answering a question.**
* **A polling watcher must not `git pull` into a shared working tree.**  I ran
  two background watchers that pulled every 30 to 45 seconds so they would see
  a peer's declaration land.  The lead stopped them: in a tree five lanes write
  to, a pull on a loop is the abort-on-a-peer's-uncommitted-file hazard
  repeated indefinitely, and it can sweep in-flight bytes into another lane's
  probe — which is the same aliasing that has already cost this lane two false
  diagnoses, industrialised.

  A watcher over a shared checkout may only *read*.  If it needs to see remote
  commits, `git fetch` and inspect `origin/main` with `git show`, never
  updating the working tree.  Better still, and what replaced them here: have
  the producing lane announce.  A push notification from the lane that made the
  change is strictly cheaper and strictly more reliable than any number of
  lanes polling for it.
* **A hypothesis that two lanes rely on and neither has checked is the one that
  fails at the end.**  `cc-lix-odd`'s Step D needs every tower dimension even
  and Step C needs every one positive.  Those are conditions on *my* `lixDD`
  consumed by *their* proof, and until they raised it neither side had verified
  the other's form.  They hold — `LIX.even_lixDD`, `LIX.lixDD_pos`, beside the
  definition — and I had landed them precisely because Step D runs on evenness,
  but landing a lemma because you believe it is needed is not the same as
  confirming it is the one needed.  Cross-lane hypotheses want checking from
  both ends, and the cost of not doing so is paid at the join.
* **A mechanism that protects the run does not protect the artifact.**  I held
  the closed endpoint as a patch outside the tree with a guessed name labelled
  "confirm with cc-lix-odd", reasoning that the guess could only fail loudly on
  first run with nothing pushed.  True, and `cc-lix-odd` pointed out the gap:
  the label degrades in a way the mechanism does not catch — someone else
  applies the patch, or it sits long enough that the label reads as
  already-confirmed, and the protection is gone while the guess remains.  The
  guess is now removed rather than annotated.  **Do not let a safe mechanism
  become a reason to leave an unconfirmed value in an artifact.**
* **A correct diagnosis can still carry a wrong fix, and this one did.**  My
  reading of `CStarSimple.lean:64` was right — `map_mem_closure` was solving
  `f x =?= a * b` with the first-order splitting `f := (a * ·)`, contradicting
  the supplied `hx` — and pinning `f` is the fix.  But the repair I sent used
  `mulRight_continuous`, which at this pin is
  `@[deprecated (since := "2026-02-20")] alias` for `continuous_mul_const`
  (`Mathlib/Topology/Algebra/Monoid.lean:110`), and a deprecation is an error
  under `-DwarningAsError=true`.  `cs-simplicity` caught it and used
  `continuous_mul_const b` with `(f := fun x : R => x * b)`.  The name came out
  of the *error message*, which had printed `mulRight_continuous b has type
  Continuous ⇑(AddMonoidHom.mulRight b)` — so it was a live name in the file
  being compiled and I reused it without checking its own status.  A name that
  appears in an error message is not thereby a name you may write.
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
