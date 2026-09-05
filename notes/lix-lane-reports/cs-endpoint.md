# cs-endpoint

Owns `Analysis/CStarKOne.lean`, `Analysis/CStarKOneInjectivityCriterion.lean`,
`Analysis/CStarKOneWhitehead.lean`, `Analysis/CStarSymmetryComponent.lean`,
`Analysis/LIXEndpointStatement.lean`,
`Manuscript/NinetyNineProblems/ProblemLIX.lean`.

## 1. GREEN

*(nothing recorded yet; probe round 1 in flight)*

## 2. AUTHORED, UNVERIFIED

* `Analysis/CStarKOne.lean`, `Analysis/CStarKOneInjectivityCriterion.lean`,
  `Analysis/CStarKOneWhitehead.lean`, `Analysis/CStarSymmetryComponent.lean`,
  `Analysis/LIXEndpointStatement.lean` — inherited at `fa86fdb1a`; the errors
  quoted in the lane brief predate that commit, so the true state is being
  measured before anything is touched.
* `Manuscript/NinetyNineProblems/ProblemLIX.lean` — **blocked on
  `IsSimpleCStar`** (see NEEDS).  Drafted, not landed: it must not define a
  second simplicity predicate, so it lands the moment `Analysis/CStarSimple*`
  exists.

## 3. NEEDS

### From `cs-simplicity` — one definition, and nothing else

```lean
-- GroupApproximation/Analysis/CStarSimple.lean   (any `CStarSimple*` name)
namespace GroupApproximation

/-- A C⋆-algebra is simple when its only closed two-sided ideals are `⊥` and `⊤`. -/
def IsSimpleCStar (A : Type u) [CStarAlgebra A] : Prop := …
```

Three constraints on the shape, in decreasing order of how expensive they are
to fix later:

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

### From `cs-limit` — the algebra, and one named `Prop` I am providing

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

### From `cs-simplicity` (second item)

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

Append in this order (dependencies first); `ProblemLIX` will add two more
lines once `cs-simplicity` and `cs-limit` land, and this list is regenerated
then:

```
import GroupApproximation.Analysis.SequentialGroupColimit
import GroupApproximation.Analysis.CStarUnitaryComponent
import GroupApproximation.Analysis.CStarMatrixBlockInclusion
import GroupApproximation.Analysis.CStarKOne
import GroupApproximation.Analysis.CStarKOneInjectivityCriterion
import GroupApproximation.Analysis.LIXEndpointStatement
import GroupApproximation.Analysis.CStarSymmetryComponent
import GroupApproximation.KTheory.MatrixProjection
import GroupApproximation.KTheory.BlockMoves
import GroupApproximation.Analysis.CStarKOneWhitehead
```

`CStarKOneWhitehead` is the Whitehead lemma (`K₁` is abelian).  Nothing in the
endpoint chain needs it — `not_k1Inj_of_hasWitness` never uses commutativity —
so it can be wired separately or last.

## 4. TRAPS

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
