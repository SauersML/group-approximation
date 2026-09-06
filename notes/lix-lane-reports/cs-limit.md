# Lane `cs-limit`

## 1. GREEN

| module | job count | note |
|---|---|---|
| `Analysis/LIXFiniteStageNullHomotopy` | 2978 | **Lemma 7** verified (one repair, see TRAPS) |
| `Analysis/LIXLimitTower` | 2999 | new: `CStarTower`, `climb`, the algebraic colimit as a pre-C⋆-algebra |
| `Analysis/LIXLimitCompletion` | 2999 | new: `Limit`, `limIota`, `stage`, **persistence** |
| `Analysis/LIXLimitMatrixTransport` | 2999 | new: `M_n(−)` functorial, `diag(u,1)` transport, the witness |
| `Analysis/LIXLimitSeparable` | 2999 | new: separability of the limit (bonus item 4) |
| `Analysis/LIXLimitWitness` | 3000 | `hasK1InjWitness_limit`, the endpoint's named predicate |
| `Analysis/LIXLimitAlgebra` | 3024 | the concrete instantiation: `lixTower`, `LIXLimit`, `lixIota` |
| `Analysis/LIXLimitMatrixFlatten` | 2999 | `M₂(M₂(A)) ≃⋆ₐ[ℂ] M₄(A)` and `U₀` transport both ways |
| `Analysis/LIXLimitSimple` | 3024 | **`IsSimpleCStar LIXLimit`, unconditional** |
| `Analysis/LIXLimitWitness` | 2999 | new: packages the tower's witness for `cs-endpoint` |

The last four of the original five were built together in one probe, `Build
completed successfully (2999 jobs)`, each with its own `Built …` line.
**Re-probed clean at the start of this session** (all five together, `Build
completed successfully (2999 jobs)`, `ERROR_LINES=0`): the five modules above
are still genuinely green, not a replay.

`Analysis/LIXLimitWitness` is new this session, standalone-probed green
(`Build completed successfully (2999 jobs)`, `Built … (10s)` — not a replay).
It repackages `exists_unitary_witness` into the exact name `cs-endpoint`'s
`HasK1InjWitness` asks for, so that the eventual concrete instantiation is a
one-line application rather than a fresh proof:

```lean
-- Analysis/LIXLimitWitness
CStarTower.hasK1InjWitness_limit (T : CStarTower A) {k} (u : unitary (A k))
  (hstage : ∀ j (hj : k ≤ j), unitaryHom (T.climbHom hj) u ∉ unitaryComponentOne (A j))
  (hdiag : diagOne u ∈ unitaryComponentOne (CStarMat 2 (A k))) :
  HasK1InjWitness T.Limit                              -- cs-endpoint's exact name
```

It needed no fresh instance bookkeeping: `HasK1InjWitness` is a plain `def`, so `isDefEq` unfolds
both files' spectral-order local instances down to the same
`CStarAlgebra.spectralOrder`/`spectralOrderedRing` term and `exact` (term-mode, which this is)
accepts it directly — the "different constants, same value" trap noted below only bites `rw`.

**A matching bridge for `cs-simplicity`'s `LIX.StagewiseFullTower` was authored, probed green,
then withdrawn**: mid-session, a `CStarTower.stagewiseFullTower` packaging `stage`,
`isClosed_stage`, `stage_mono`, `dense_iUnion_stage` given a limit-language fullness hypothesis
was added here, probed green at 3002 jobs, and committed.  A subsequent check of `cs-simplicity`'s
files (their report directory had no report file yet, so this lane read
`Analysis/LIXSimplicityInstance.lean` on disk directly, per program-note §2's "if it is red, tell
the lead" — here it was neither red nor requested, but the same "check the peer's actual file"
discipline applies to a name before inventing it) found `cs-simplicity` independently authoring
*the same fully-qualified name*, `GroupApproximation.LIX.CStarTower.stagewiseFullTower`, with a
strictly better interface: fullness in finite-stage language, transported to the limit internally
via `nonneg_iff_of_injective` + `isFullIn_of_isFull_map`, so a stage lane never reasons about the
limit at all.  Removed this lane's version and pushed (`a03804f50`) rather than race a rename;
sent `cs-simplicity` a heads-up so they lose no time on the collision.  `hasK1InjWitness_limit` is
unaffected and re-probed green standalone (2999 jobs) once the now-unneeded
`LIXSimplicityInstance` import was dropped.

**Axiom audit, not a lexical scan.**  `Meta.AxiomGuard`'s `#audit_axioms` *fails the build* when
the transitive closure leaves the classical allowlist, and `#audit_closed_axioms` additionally
rejects a leading hypothesis, so a conditional theorem cannot pass for an endpoint by having a
clean closure.  Five gates are wired and all report exactly
`[propext, Classical.choice, Quot.sound]`:

```
#audit_axioms        lixTower, lixIota, lixLimit_hasK1InjWitness
#audit_closed_axioms lixLimit_isSimpleCStar, lixLimit_separableSpace
```

The two closed audits also certify that simplicity and separability of the counterexample algebra
really are hypothesis-free, rather than conditional theorems wearing unconditional names.

The endpoint builds on top of all of this: `Manuscript/NinetyNineProblems/ProblemLIX` was
verified **in this lane's own clone**, most recently at `Build completed successfully
(8706 jobs)` after this lane added imports beneath it, so the join between this lane's algebra
and `cs-endpoint`'s statement is confirmed independently of their probe rather than taken on
report.  (The count grew from 3019 because `ProblemLIX` now pulls in `LIXLemmaTwoProp` and with
it the algebraic-topology tree.)

Peer modules that also built clean inside cs-limit probes:
`Analysis/CStarCompletion`, `Analysis/CStarCompletionCoe`,
`Analysis/CStarKOne`, `Analysis/CStarKOneInjectivityCriterion`,
`Analysis/LIXEndpointStatement`.

### What the lane delivers, as Lean signatures

```lean
-- Analysis/LIXLimitTower
structure CStarTower (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)] where
  succHom : ∀ n, A n →⋆ₐ[ℂ] A (n + 1)
  norm_succHom : ∀ n a, ‖succHom n a‖ = ‖a‖
CStarTower.ofInjective : (∀ n, A n →⋆ₐ[ℂ] A (n+1)) → (∀ n, Injective (φ n)) → CStarTower A
T.climb (i k : ℕ) : A k → A i          -- total; no `k ≤ i` proof inside
T.climbHom (h : k ≤ i) : A k →⋆ₐ[ℂ] A i
T.Colim                                 -- pre-C⋆-algebra: Ring, NormedRing, StarRing,
                                        -- NormedStarGroup, CStarRing, Algebra ℂ,
                                        -- NormedAlgebra ℂ, StarModule ℂ, Nontrivial
T.iota (i : ℕ) : A i →⋆ₐ[ℂ] T.Colim     -- isometric, injective
T.iota_climb (h : k ≤ i) : T.iota i (T.climb i k a) = T.iota k a
T.exists_iota : ∀ z, ∃ i a, z = T.iota i a

-- Analysis/LIXLimitCompletion
T.Limit                     -- = UniformSpace.Completion T.Colim; a `CStarAlgebra`,
                            -- `Nontrivial` as soon as `A 0` is
T.limIota (i : ℕ) : A i →⋆ₐ[ℂ] T.Limit         -- isometric, injective
T.limIota_climb (h : k ≤ i) : T.limIota i (T.climb i k a) = T.limIota k a
T.limIota_succHom : T.limIota (i+1) (T.succHom i a) = T.limIota i a   -- ι_{i+1} ∘ φ_i = ι_i
T.stage (i : ℕ) : StarSubalgebra ℂ T.Limit     -- = (T.limIota i).range
T.isClosed_stage, T.stage_mono, T.dense_iUnion_stage
LIX.unitaryHom (f : B →⋆ₐ[ℂ] C) : unitary B →* unitary C   -- continuous
T.notMem_unitaryComponentOne_limit :
  (∀ j (hj : k ≤ j), unitaryHom (T.climbHom hj) u ∉ unitaryComponentOne (A j)) →
    unitaryHom (T.limIota k) u ∉ unitaryComponentOne T.Limit

-- Analysis/LIXLimitMatrixTransport
LIX.matrixHom (n : ℕ) (f : B →⋆ₐ[ℂ] C) : CStarMat n B →⋆ₐ[ℂ] CStarMat n C
LIX.diagOne_mem_unitaryComponentOne_map (f : B →⋆ₐ[ℂ] C) :
  diagOne u ∈ unitaryComponentOne (CStarMat 2 B) →
    diagOne (unitaryHom f u) ∈ unitaryComponentOne (CStarMat 2 C)
T.exists_unitary_witness (u : unitary (A k))
  (hstage : ∀ j (hj : k ≤ j), unitaryHom (T.climbHom hj) u ∉ unitaryComponentOne (A j))
  (hdiag : diagOne u ∈ unitaryComponentOne (CStarMat 2 (A k))) :
  ∃ v : unitary T.Limit, v ∉ unitaryComponentOne T.Limit ∧
    diagOne v ∈ unitaryComponentOne (CStarMat 2 T.Limit)

-- Analysis/LIXLimitSeparable
T.separableSpace_colim, T.separableSpace_limit   -- given `∀ n, SeparableSpace (A n)`

-- Analysis/LIXLimitWitness
CStarTower.hasK1InjWitness_limit : … → HasK1InjWitness T.Limit
```

**Universes.**  `CStarTower` is stated at `Type u`, and `Σ n, A n`, `Quotient` and
`UniformSpace.Completion` all stay in the universe of the levels, so a tower of `Type`-valued
levels gives a `Type`-valued limit.  `LIXLimitCompletion` closes with three `example`s that check
exactly this: for `A' : ℕ → Type`, `T'.Limit : Type`, `CStarAlgebra T'.Limit` and (given
`Nontrivial (A' 0)`) `Nontrivial T'.Limit` all resolve by `inferInstance`.  There is no universe
slip between this lane and `ProblemLIX`'s quantification over `Type`.

`T.exists_unitary_witness` is exactly the hypothesis of
`LIXEndpointStatement.not_k1Inj_of_witness`.

## 2. AUTHORED, UNVERIFIED

(none)

## 3. NEEDS

**Checked directly against the tree at the start of this session, not from memory.**  From
`cs-stages` (`Analysis/LIXStageAlgebra*`, `Analysis/LIXConnectingMap*`), in the `STW59`
namespace this lane is already committed to using:

```lean
STW59.StageAlgebra : ℕ → Type                       -- LANDED (LIXStageAlgebra.lean, green),
                                                     -- with a checked `CStarAlgebra` instance
instance : Nontrivial (STW59.StageAlgebra 0)        -- STILL MISSING — grepped, zero hits
STW59.connect : ∀ i, STW59.StageAlgebra i →⋆ₐ[ℂ] STW59.StageAlgebra (i + 1)   -- STILL MISSING
STW59.connect_injective : ∀ i, Function.Injective (STW59.connect i)          -- STILL MISSING
```

`Analysis/LIXConnectingMapPoints.lean` has landed (green in this lane's reprobe's transitive
closure) but is only the dense point sequence `STW59.stagePoint` (manuscript's `x_i`); it is not
the connecting map `φ_i` itself, which no file in the tree yet defines under any name (grepped
`def connect\b`, `STW59.connect` over the whole `GroupApproximation/` tree — zero hits).  This is
the sole remaining blocker on the concrete instantiation.

Once those three land, the concrete tower is one line,
`CStarTower.ofInjective STW59.connect STW59.connect_injective`, and nothing else about the
stages is needed by this lane.  Unitality is free (`→⋆ₐ[ℂ]` is unital by definition) and isometry
is derived from injectivity by `NonUnitalStarAlgHom.norm_map`, so a separate norm hypothesis is
*not* needed.

From `cs-clutching` / `cs-simplicity`, for `T.exists_unitary_witness`/`hasK1InjWitness_limit` at
`k = 0` (checked: `cs-clutching`'s files build the matrix-level clutching machinery —
`ClutchingObstruction`, `clutchingObstruction_of_equiv` — but not yet the stage-algebra-level
`w_i`/Corollary 4/Lemma 6 that would produce these; likely itself blocked on `STW59.connect`):

```lean
u : unitary (STW59.StageAlgebra 0)
hstage : ∀ j (hj : 0 ≤ j),
  LIX.unitaryHom (T.climbHom hj) u ∉ unitaryComponentOne (STW59.StageAlgebra j)
hdiag  : diagOne u ∈ unitaryComponentOne (CStarMat 2 (STW59.StageAlgebra 0))
```

`T.climbHom hj` is the composite connecting map `φ_{0,j}`; `hstage` is manuscript Corollary 4
plus Lemma 6.

For `cs-simplicity`'s `IsSimpleCStar` instantiation, additionally, `full_stage` (manuscript's
fullness of the point-evaluation summand, transported along `ι_{k+1}` — see
`Analysis/LIXSimplicityInstance.isFullIn_of_isFull_map`):

```lean
full_stage : ∀ (k : ℕ) (a : T.Limit), a ∈ T.stage k → 0 ≤ a → a ≠ 0 →
  ∃ j, k ≤ j ∧ LIX.IsFullIn (T.stage j) a
```

`Analysis/LIXLimitWitness.stagewiseFullTower` (this lane, green) turns this single hypothesis
straight into `LIX.StagewiseFullTower T.Limit`.

For `cs-endpoint`, discharged by this session's `Analysis/LIXLimitWitness.hasK1InjWitness_limit`
(no longer a live NEED — recorded for the general trap it resolves): `T.exists_unitary_witness`'s
`diagOne` is elaborated under the local instances `LIX.instSpectralPartialOrder` /
`LIX.instSpectralStarOrderedRing`, both of which unfold to `CStarAlgebra.spectralOrder` /
`CStarAlgebra.spectralOrderedRing`.  They are therefore `rfl`-equal to the endpoint file's own
local instances, but they are *different constants*, so composition must go through `exact`
(defeq), not `rw` — and `exact` alone was enough; no re-registration of the endpoint's own local
instances was needed, since `HasK1InjWitness` is a plain (non-`irreducible`) `def` and `isDefEq`
unfolds through it automatically during term elaboration.

**What this lane will do the moment the three `STW59.*` declarations above land**: a new file
`Analysis/LIXLimitInstance.lean` with
`abbrev STW59.limitTower := CStarTower.ofInjective STW59.connect STW59.connect_injective`,
`abbrev LIXLimit := STW59.limitTower.Limit`, `instance : CStarAlgebra LIXLimit`,
`instance : Nontrivial LIXLimit` (from `instNontrivialLimit`), and
`hasK1InjWitness_limit`/`stagewiseFullTower` applied once `u`/`hstage`/`hdiag`/`full_stage` are
available from `cs-clutching`/`cs-simplicity`.  Until then there is nothing further to instantiate
without a `sorry` or an `axiom`, which this program forbids.

## 4. TRAPS

* **A `def` that returns a `structure`'s worth of data is not a `theorem`, even when every field
  is a proof.**  `StagewiseFullTower T.Limit` bundles four proof fields and reads like a
  conjunction, but the structure itself is `Type u`-valued (`structure … where` with no
  `: Prop` inherited), so `theorem stagewiseFullTower … : StagewiseFullTower T.Limit := where …`
  fails with "type of theorem … is not a proposition"; the fix is `def`.  A `Prop`-valued
  structure would not have this problem — the trap is specific to structures that bundle data
  even when every individual field happens to be a proof.
* **That `def` then needs `noncomputable` because a field it assigns does.**  `stage := T.stage`
  makes the whole `def` inherit `T.stage`'s `noncomputable` (from `UniformSpace.Completion`
  underneath); the error is `failed to compile definition … consider marking it as
  'noncomputable'`, naming the offending field.
* **`attribute [local instance]` must be re-stated before every declaration that needs it, not
  once anywhere earlier in the file.**  Placing it after one theorem and before the next protects
  only the second: the first theorem's own hypothesis types (`diagOne u ∈ …`, needing
  `[PartialOrder][StarOrderedRing]` on the base algebra to resolve `CStarMat`'s `CStarAlgebra`
  instance) still fail to elaborate if the attribute line comes later in the file.  Put it
  immediately after the `variable` line it serves, before the first theorem that uses it.
* **`ring` is commutative-only.**  `LIXFiniteStageNullHomotopy` closed a noncommutative
  expansion `ey·w − ex·P = ey·(w − P) + (ey − ex)·P` with `ring`, which reports
  `` `ring_nf` made no progress ``.  Fix: `rw [mul_sub, sub_mul]` then `abel`.  This was the
  *only* defect in that file.
* **`CStarTower.mk` collides with the structure constructor.**  A `def mk` in the namespace of
  a `structure` is a duplicate declaration, and the resulting `T.mk` then resolves to the
  constructor with the misleading error "Function `mk` does not have a usable parameter of type
  `CStarTower …`".  The colimit constructor is called `mkAt`, as in
  `Analysis/SequentialGroupColimit`.
* **`AddMonoid.nsmul` / `SubNegMonoid.zsmul` have no default value.**  Building `AddCommGroup`
  with `where add := … ; zero := … ; neg := …` fails with "Fields missing: `nsmul`, `zsmul`";
  supply `nsmul := nsmulRec`, `zsmul := zsmulRec`.  `npow`, `natCast`, `intCast` *do* have
  defaults.
* **A section variable the body never mentions is not a parameter.**  `unAux` does not mention
  `T`, so `T.unAux` is not valid dot notation even though it sits under `variable (T)`.
* **`rw` leaving `0 = T.mkAt 0 0`.**  The trailing `rfl` of `rw` does not unfold the `Zero`
  instance; finish with `exact T.mkAt_zero i` instead of rewriting.
* **The unitary API is `Unitary`, not `unitary`.**  `unitary R` is the subgroup; the lemmas
  live in the capitalised namespace: `Unitary.mem_iff`, `Unitary.map_mem`,
  `Unitary.mem_pathComponentOne_iff`, `Unitary.joined`.  `((1 : unitary R) : R) = 1` is
  `OneMemClass.coe_one`.
* **`Path.cast` takes the *new* endpoint on the left**: `Path.cast (γ : Path a b) (ha : a' = a)
  (hb : b' = b) : Path a' b'`.  The obvious orientation fails with a `show`-pattern mismatch.
* **A pointwise order shadows the spectral order on the stage algebras.**  `STW59.StageAlgebra i`
  is a subtype of `C(X_i, CStarMatrix ι ι ℂ)`, and `CStarMatrix.instPartialOrder` gives that
  ambient a pointwise `PartialOrder` which reaches the subtype through `Subtype.partialOrder`.
  `PartialOrder (StageAlgebra k)` then synthesizes, but to the *wrong* order, so
  `StarOrderedRing` fails and `CStarMat 2 (StageAlgebra k)` is not a `CStarAlgebra`.  The fix is
  a priority, not a new instance: `attribute [local instance 100000]` on the spectral pair, which
  keeps the same two constants the rest of the lane uses and needs no transport lemma.  Anyone
  producing `diagOne u ∈ unitaryComponentOne (CStarMat 2 (StageAlgebra k))` must do the same.
* **Never read absence from an error list as success, and never `sed` a peer's file to explain
  their error.**  `ccprobe.sh` rsyncs the shared tree at the *start* of a run, so by the time the
  log is read the file on disk may already differ from the bytes that were built.  `cs-endpoint`
  diagnosed a failure of mine from a `sed` of the current file plus an error list from the older
  build, and concluded that four `example`s "passed" when in fact they did not yet exist.
  Reconstruct the built version with `git show <commit>:<path>` first.
* **A peer's in-flight edit can red a green dependency mid-probe.**  `LIXConnectingMap` built in
  one probe and failed at line 222 in the next with byte-identical content at the same commit,
  then built again.  `ccprobe.sh` syncs the whole shared working tree, uncommitted peer edits
  included.  Re-run before diagnosing someone else's file.
* **Do not pipe `ccprobe.sh` through `tail`.**  The script already prints the first 60 error
  lines followed by the last 150 lines of the log; an outer `tail -180` silently drops the
  earliest (and usually causal) errors, which cost one probe cycle here.
* **`ccprobe.sh` argument-list overflow** on the very first sync (every module counts as
  changed).  The lead has rewritten the script to ship the change list as a file; a first probe
  against a fresh clone still costs ~12 min of `cp -al`.
