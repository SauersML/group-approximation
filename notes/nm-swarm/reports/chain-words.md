# Lane chain-words: S3a word graphs and the cycle condition (tex 1378–1398)

Snapshot: origin/main 1df28bd83 (09-13).  Scope: the first half of the subshift case of
lem:chain-core-models, from "First suppose $X$ is a subshift" to "The periodic models need not
themselves belong to the subshift."  Everything from "Retain only the cyclic edges" (tex 1400) on
(Z_r, Y_0, language stabilization, Y_0 = CR(T), noncyclic edge ⇒ P) belongs to chain-subshift.

## Keys (12)

| key | tex | sentence | planned carrier |
|---|---|---|---|
| `53fd5ea7d3d0` | 1378 | First suppose X is a subshift over a finite alphabet. | hypotheses `hXc`, `hX` below |
| `9bc3873fb872` | 1378 | word graph at level r, length-r vertices, length-(r+1) edges, prefix → suffix | `word`, `language`, `wordEdge`, `wordGraph` |
| `078684fc2a60` | 1378 | cyclic edge; cycle condition | `IsCyclicEdge`, `CycleCondition` |
| `dfc6d4510272` | 1384 | A subshift satisfying the cycle condition has an LEF crossed product. | `isLEFRing_skewMonoidAlgebra_of_cycleCondition`, `printedSubshiftCycleConditionLEF` |
| `8bf7f40918d5` | 1384 | finite table, Laurent form, window determining the coefficients | `exists_radius` + `isLEFRing_skewMonoidAlgebra_of_periodic` (table step) |
| `56b6a80cc911` | 1384 | high level, cycles containing witness words | `exists_periodicModels_of_cycleCondition` |
| `2ed7f807a3a6` | 1384 | reading the cycles gives periodic models with allowed windows | `exists_periodic_of_isCyclicEdge` |
| `57cd1b63930c` | 1384 | repeat each cycle past twice the largest Laurent degree | `exists_periodicModels_of_cycleCondition` (common period `N > 2B`) |
| `0941296cf395` | 1384 | coefficients as diagonal matrices, u as the cyclic shift | `Pestov91.periodicModel`, `shiftMatrix` (consumed) |
| `4aede6d48b4d` | 1384 | allowed windows preserve products and sums; witnesses separate | `evalFamily` (a ring hom) + the equivariance/separation clauses |
| `b94a006ee638` | 1384 | the product is the finite matrix-ring model | product index `Fin m → K` in `isLEFRing_skewMonoidAlgebra_of_cycleCondition` |
| `533771f4f22d` | 1384 | the periodic models need not belong to the subshift | periodic word `p : ℤ → A` is not asked to lie in `X`; only its windows are |

## Existing carriers (origin/main and lanes/*.files, grepped for uses)

- Consumed: `Pestov91.isLEFRing_skewMonoidAlgebra_of_periodic` (hypothesis `hper`), with
  `periodicModel`, `shiftMatrix` (Pestov91/LEFCrossedProduct); `Pestov91.IsLEFRing` (Pestov91/LEF).
- Pattern only, not reusable: `Pestov91.exists_radius`, `exists_periodic_model`, `evalAlong` are
  stated for the Toeplitz subshift; `Pestov91.exists_finset_dependsOn` for `Set (ℤ → Bool)`.
- Mathlib pin 81a5d257: `SymbolicDynamics.FullShift.shift` (`shift n x i = x (n + i)`), `Subshift`
  (`isClosed`, `mapsTo`), `Fin.init`, `Fin.tail`, `Relation.ReflTransGen`, `Digraph`.
- Nothing on word graphs, cyclic edges, the cycle condition, or finite radius on a general subshift.

## Planned modules (new, unwired; namespace `GroupApproximation.WordGraph`)

1. `GroupApproximation/Dynamics/SubshiftWordGraph.lean` (definitions; lands first)
   - `word (x : ℤ → A) (i : ℤ) (n : ℕ) : Fin n → A := fun j => x (i + j)`
   - `language X n : Set (Fin n → A) := {w | ∃ x ∈ X, word x 0 n = w}`
   - `wordEdge X r u v := ∃ w ∈ language X (r + 1), Fin.init w = u ∧ Fin.tail w = v`
   - `wordGraph X r : Digraph (language X r)`
   - `IsCyclicEdge X r w := w ∈ language X (r + 1) ∧ Relation.ReflTransGen (wordEdge X r) (Fin.tail w) (Fin.init w)`
   - `CycleCondition X := ∀ r w, w ∈ language X (r + 1) → IsCyclicEdge X r w`
   - lemmas: `word_apply`, `word_shift`, `init_word`, `tail_word`, `word_mem_language`,
     `init_mem_language`, `tail_mem_language`, `wordEdge_word`, `exists_realize_of_word_mem_language`,
     `isCyclicEdge_zero`.
   - Spelling agreed with chain-subshift, which builds `retainedSubshift`/`coreSubshift` on it.
2. `GroupApproximation/Dynamics/SubshiftCyclePeriodic.lean`
   - `exists_walkWord_of_reflTransGen`: a directed path of length m is a word of length r + m all of
     whose (r+1)-windows are allowed.
   - `exists_periodic_of_isCyclicEdge`: a cyclic edge `w` gives `k > 0` and a `k`-periodic
     `p : ℤ → A` with `word p 0 (r + 1) = w` and every `word p n (r + 1)` allowed.
3. `GroupApproximation/Dynamics/SubshiftCycleLEF.lean` (imports Pestov91.LEFCrossedProduct)
   - `exists_radius`: a locally constant function on a closed `X ⊆ ℤ → A` depends on `[-r, r]`.
   - `evalFamily`: evaluation along a family of points, as a ring hom into `ι → κ → K`.
   - `exists_periodicModels_of_cycleCondition`, `isLEFRing_skewMonoidAlgebra_of_cycleCondition`.
   - `PrintedSubshiftCycleConditionLEF : Prop` + `printedSubshiftCycleConditionLEF`, `#audit_closed_axioms`.

## Hypothesis spellings

- `A : Type*` `[Finite A] [TopologicalSpace A] [DiscreteTopology A]`; `X : Set (ℤ → A)`;
  `hXc : IsClosed X`; `hX : ∀ n : ℤ, Set.MapsTo (SymbolicDynamics.FullShift.shift n) X X`
  (a Mathlib `Subshift s` supplies `s.isClosed`, `s.mapsTo`).  Definitions need no instances.
- `K : Type` `[Ring K] [Finite K]`; `[MulSemiringAction (Multiplicative ℤ) (LocallyConstant X K)]` with
  `hact : ∀ (j : ℤ) (f : LocallyConstant X K) (x y : X), (∀ i, y.1 i = x.1 (i - j)) → (Multiplicative.ofAdd j • f) x = f y`,
  the tex convention `j • f = f ∘ T^{-j}` for the left shift `T`.

## Interfaces needed

- chain-core S1.1 (coefficient synonym with the ℤ-action): not blocking.  The theorem takes the
  action through `hact`; an instantiation corollary follows once chain-core lands its synonym.

## Residuals

None planned: the three modules rest on Mathlib and Pestov91/LEFCrossedProduct only.

## Status

- Blocker: no `lanes/chain-words.clone`, so no probe yet.  Definitions land unverified (new unwired
  files), then re-land after a GREEN verdict line.
- Census rows go to `metadata/nm-census-rows/chain-words.tsv` after green landings.
