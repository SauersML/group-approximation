# STW XXII endpoint: exact conditionality map (2026-09-05)

Adversarial audit of the outermost declaration of the Problem XXII
counterexample: *what does its statement quantify over, what does its proof
consume, and what is not yet compiled.*

Method: transitive `import` closure computed from the actual `import` lines
(446 project modules), every `Prop` in the statement opened and read, every
proof-term argument in the statement traced to its defining declaration.

## 1. The endpoint

```
GroupApproximation.STW22NegativeSolution.negativeSolutionToProblemXXII
  GroupApproximation/Analysis/STW22NegativeSolution.lean:50
```

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
        antipodalAllTracesGauge_isCoordinateNormComparison)
```

`AntipodalCounterexampleAlgebra := BaseAlgebra AntipodalCounterexampleBlock`.

**Binders: none.**  The only free variable is the universe `v` in the Type-I
clause, which strengthens the claim (Type I is asserted for an arbitrary
Hilbert-space universe) rather than weakening it.  The file already carries
`#audit_closed_axioms negativeSolutionToProblemXXII`, which *rejects a leading
binder* as a build error in addition to auditing the axiom closure — so this
property is gated by the build, not by this document.

## 2. Every `Prop` reachable from the statement

None of these is an assumption package; each is a mathematical predicate with
its ordinary meaning, and each was read for this audit.

| Prop | Where | Content |
|---|---|---|
| `CStarAlgebra` | Mathlib | class |
| `TopologicalSpace.SeparableSpace` | Mathlib | countable dense subset |
| `IsNuclearCStarAlgebra` | `Analysis/CStarExactness.lean:424` | `IsNuclearMap id`: CPAP through genuinely finite-dimensional `D`, uniformly on finite sets |
| `STW22.IsTypeI` | `Analysis/STW22TypeIBlocks.lean:103` | GCR: every irreducible rep contains the compacts in its range |
| `IsBauerSimplex ℝ≥0` | `Analysis/STW22BauerSimplex.lean:141` | `IsChoquetSimplex` (lattice condition on the cone, l.106) ∧ `IsCompactConvexClosedBoundary` (convex, compact, closed extreme boundary) |
| `CompactSpace`, `MetrizableSpace` | Mathlib | — |
| `Function.Injective` / `Surjective` | Mathlib | — |
| `IsCoordinateNormComparison` | `Analysis/UniformTracialTwoNullIdeal.lean:198` | `∀ n x, ‖x‖ ≤ r n * G.q n x` |

Two structural points a hostile reader should check, and their answers:

* The statement mentions the **proof term**
  `antipodalAllTracesGauge_isCoordinateNormComparison`, because
  `BoundedUniformTwoCompletion G r hr` carries the comparison datum in its
  type.  That term is a *closed theorem*
  (`Analysis/STW22AntipodalNormComparison.lean:82`), not a hypothesis, so it
  introduces no conditionality.
* The final two clauses are the literal Problem XXII conclusion.
  `canonicalExtension` (`Analysis/STW22CanonicalTraceExtension.lean:42`) is the
  map `T(A) → T(M)` sending a base trace to its extension along
  `baseToCompletion`; `restrictToBase_canonicalExtension` proves it restricts
  back to the identity.  Injective + not surjective is `T(A) ⊊ T(M)`.

## 3. The proof closure: one mathematical input, and it is a theorem

```
negativeSolutionToProblemXXII
  └─ antipodal_trace_space_strict_inclusion            (STW22UnconditionalCore.lean:111)
      └─ not_everyAntipodalCompletionTraceIsContinuousExtension   (:82)
          └─ antipodalCoordinateStateBlockDataUnconditional       (:39)
              └─ antipodalCoordinateStateBlockData                (STW22AntipodalBlockData.lean:284)
                  └─ complexOddMapCommonZero_unconditional        (STW22UnconditionalCore.lean:32)
                      └─ complexOddMapCommonZero
                           (ThirdParty/HamSandwich/SphereOddDegree/ComplexOddMapCommonZero.lean:19)
                          └─ borsuk_ulam                          (…/BorsukUlam.lean:141)
                              └─ no_odd_map_sphere_succ           (…/BorsukUlam.lean:126)
                                  └─ odd_degree_of_odd_sphere_self_map_unconditional
                                       (…/Final/OddDegreeTheoremUnconditional.lean:35)
```

`ComplexOddMapCommonZero` (`STW22AntipodalBlockData.lean:34`) is a named `Prop`
— but it is **discharged**, not assumed: `antipodalCoordinateStateBlockData`
takes it as an explicit argument, and `STW22UnconditionalCore` applies that
argument to the proved `complexOddMapCommonZero_unconditional`.  It appears in
no exported statement.

**`CommonZeroProperty` is not in this closure.**  The Chern-class route
(`Topology/TautologicalCommonZero.lean`, `Topology/TautologicalAntipodal.lean`,
`Analysis/ChernCommonZeroBridge.lean`) is superseded for the endpoint: zero
`Topology.Tautological*` and zero `Chern*` modules occur among the 446 modules
of the endpoint's import closure.  A proof of `CommonZeroProperty` would be a
second, independent route — not a substitution the endpoint is waiting on.

## 4. What is not compiled

The endpoint's closure is 446 project modules; the root `GroupApproximation.lean`
closure is 4050.  **190 modules of the endpoint's closure are not in the root
closure**, i.e. no CI build has ever elaborated them:

* **169 HamSandwich modules** — the v4.32 port in progress under lanes
  `hamsandwich-port-A` / `hamsandwich-port-B`; layered build order in
  `notes/hamsandwich-port-order-2026-09-05.md`.  Only four HamSandwich modules
  are currently in the root closure (`Basic`, `Antipodal`, `Hausdorff`,
  `RealProjectiveSpace`).
* **21 operator-algebra modules**, listed below.  These need nothing from the
  unported part of HamSandwich: building the four sinks
  `STW22AntipodalTraceSimplexBauer`, `STW22AntipodalNormComparison`,
  `STW22BauerSimplexImage`, `TracialStateWeakStarTopology` covers 19 of them;
  the remaining two (`STW22UnconditionalCore`, `STW22NegativeSolution`) are the
  only ones that pull the HamSandwich sink.

```
STW22AntipodalBaseBoundaryMeasure      STW22AntipodalBoundaryMeasureTrace
STW22AntipodalBaseCoordinateMeasures   STW22AntipodalBoundaryTraceFunction
STW22AntipodalBlockComplexCenter       STW22AntipodalCoordinateRestriction
STW22AntipodalBlockMeasureTrace        STW22AntipodalFiniteBoundaryMeasure
STW22AntipodalBlockTraceAffineEquiv    STW22AntipodalNormComparison
STW22AntipodalBlockTraceClassification STW22AntipodalTraceMeasureInverse
STW22AntipodalBlockTraceMeasure        STW22AntipodalTraceSimplexBauer
STW22AntipodalBoundaryComponents       STW22AntipodalTraceSimplexIntegration
STW22AntipodalBoundaryMeasureRoundTrip STW22BauerSimplexImage
TracialStateWeakStarTopology
STW22UnconditionalCore                 STW22NegativeSolution
```

## 5. Verdict

The XXII endpoint is **unconditional as authored**: no hypothesis binders, no
named `Prop` in its statement closure that is assumed rather than proved, and a
`#audit_closed_axioms` gate in the same file that turns either defect into a
build error.  What remains is entirely a **build** obligation, not a
mathematical one: finish the HamSandwich v4.32 port so
`ComplexOddMapCommonZero.lean` elaborates, get the 21 operator-algebra modules
green, and have the lead wire `STW22NegativeSolution` into
`GroupApproximation.lean` so the gate runs in CI.

## 6. Addendum: the CCEGSTW vocabulary gap (opened by audit sweep 8)

Sweep 8 (`afbe9310f`) is right that the endpoint's conjuncts never mention
`IsFactorialTraciallyCompletePair` or `AllTracesUniformTwoContinuous` from
`GroupApproximation/Analysis/TraciallyCompleteCStar.lean`.  That is a separate
defect from conditionality: the endpoint is unconditional, but it states
`T(A) ⊊ T(M)` in the repository's own vocabulary rather than the problem's.

`GroupApproximation/Analysis/STW22DesignatedTraces.lean` closes the half that is
already proved.  With

```text
M := BoundedUniformTwoCompletion antipodalAllTracesGauge …
X := Set.range (canonicalExtension antipodalAllTracesGauge_isCoordinateNormComparison)
```

`X.Nonempty` is the trace at infinity, and **Question 1.1's second form** —
`DesignatedTracesAreAllTraces X`, i.e. `X = Set.univ` — is `Set.range_eq_univ`
away from `¬ Function.Surjective (canonicalExtension …)`, which is proved.

### Route for Question 1.1's first form, `¬ AllTracesUniformTwoContinuous X`

Not yet landed.  The obstacle is not the mathematics but a direction of
estimate.  Refuting the first form needs a sequence that is
`uniformTwoNormOn X`-null, and the witness in hand is `uniformTwoNorm G`-null,
so what is required is `uniformTwoNormOn X ≤ (something)·uniformTwoNorm G` —
the easy direction (each designated trace is dominated by the gauge), but it
needs a *pointwise* bound where the repository currently exposes only the
sequential one.  Concretely:

1. `GroupApproximation/Analysis/STW22CanonicalTraceExtensionModel.lean` proves
   `norm_modelExtension_le_uniformTwoNorm : ‖modelExtension τ x‖ ≤ uniformTwoNorm (G D) x.1`
   but declares it `private`; only the sequential corollary
   `modelExtension_isUniformTwoContinuous` is public, and sequential continuity
   of each trace separately does not give uniformity over `X`.  The name occurs
   nowhere else in the repository, so dropping `private` is safe.
2. For `ρ` a base trace, `canonicalExtension_apply` plus step 1 gives
   `tracialTwoNorm (canonicalExtension ρ) a ≤ √(uniformTwoNorm G (star y * y))`
   with `y := realize … a`, and `uniformTwoNorm_mul_left_le`
   (`STW22CanonicalTraceExtensionEstimates.lean:98`) bounds that by
   `√(‖y‖ · uniformTwoNorm G y)`.  `uniformTwoNormOn_le` then lifts it over `X`.
3. The square root is why the witness must be **norm-bounded**, and the current
   `exists_discontinuous_tracialState_completion` does not say that its witness
   is.  It is: the witness is `fun N ↦ ⟨tail B.seq N, …⟩`
   (`STW22CounterexampleAssembly.lean:463`), and `tail x N n = if n ≤ N then 0
   else x n`, so `‖tail B.seq N‖ ≤ ‖B.seq‖` coordinatewise in `lp ∞`.  What is
   needed is a bounded-witness variant of that theorem — added alongside the
   existing one, not by changing it, since its statement is pinned into
   `stw22_trace_problem_counterexample`.

### Factoriality itself

`IsFactorialTraciallyCompletePair X` has six fields.  Sweep 8 guesses
`isCompact`, `isConvex`, `isClosed` are free; that is right only up to two
missing facts about `canonicalExtension`, which are not in the repository:

* `isCompact` needs `Continuous (canonicalExtension hr)` for the weak-star
  topologies — then `X` is the continuous image of the compact
  `TracialState (BaseAlgebra …)` (`TraciallyComplete.compactSpace_tracialState`).
* `isClosed` follows from `isCompact` and `TraciallyComplete`'s
  `tracialStateWeakStarT2Space`, so it is free *after* `isCompact`.
* `isConvex` needs affineness, `modelExtension (t·σ + (1-t)·τ) = t·modelExtension σ +
  (1-t)·modelExtension τ`, which should follow from uniqueness of the limit
  defining `extensionValue` along a base approximation.
* `isFace`, `faithful` and `unitBallComplete` are substance.  Sweep 8 is right
  that `isFace` is the one to look at first.

## 7. Result: green, with the closed-endpoint gate fired

Probe tag `xxiiEP3`, targets `STW22NegativeSolution` and `STW22DesignatedTraces`:

```text
Build completed successfully (9103 jobs).
info: STW22NegativeSolution.lean:71:21:
  'GroupApproximation.STW22NegativeSolution.negativeSolutionToProblemXXII'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

Zero errors, zero warnings.  That line is `#audit_closed_axioms`, so it
certifies both halves at once: the axiom closure is classical, and the
declaration has no leading input.  The job count moved on every real change
(3455 → 9102/9103 failing → 9103 succeeding), so this is not a stale-olean
replay.

Three defects stood between "unconditional as authored" and "machine-checked",
and none of them was mathematical:

1. **Pinned instance arguments.**  Every declaration of
   `STW22CanonicalTraceExtension` and `STW22BaseUniformTracialGauge` carries
   `[∀ n, Nonempty (TracialState (D n))]`, and at the concrete blocks that
   binder is not synthesized *inside an application* — in the statement as much
   as in the proof.  A diagnostic module established that the class is
   perfectly synthesizable standalone (all six of `(∀ n,) CStarAlgebra /
   Nontrivial / Nonempty (TracialState …)` discharge by `inferInstance` in the
   same context) and that the `@`-applied form of the very same map elaborates.
   So findability was never the problem: the elaborator reaches the binder
   while `D` is undetermined, because the argument that would fix `D` is the
   comparison datum, whose type is stated through the gauge abbreviation `G D`,
   and `∀ n, Nonempty (TracialState (?D n))` has no solution however many
   instances are registered.  `antipodalCanonicalExtensionMap` is the
   `@`-applied map, an `abbrev`, so it *is* `canonicalExtension …`.
2. **Two names that did not exist.**  `UniformTracialSequenceCompletion.uniformTwoNorm`
   (it is `STW22Assembly.uniformTwoNorm`), and `traceZeroSpace` reached through
   `CuntzPedersenTraceZero` when it lives in `CuntzPedersenCoronaObstruction` —
   where `autoImplicit` turned the unresolved name into a variable and reported
   "Function expected at `traceZeroSpace`" instead.
3. **Three missing `open`s.**  `MetrizableSpace` needs `TopologicalSpace`,
   `ℝ≥0` needs `open scoped NNReal`, `BoundedUniformTwoCompletion` needs
   `UniformTracialBoundedCauchyQuotient`.  An `open` never travels through an
   import, so a name that resolves in the module that declares it can still
   fail in an importer.

**Still owed, and not a lane's to do:** none of these modules is in the root
import closure, so CI gates none of it.  The root additions, in dependency
order, are `GroupApproximation.Analysis.STW22NegativeSolution` and
`GroupApproximation.Analysis.STW22DesignatedTraces`.
