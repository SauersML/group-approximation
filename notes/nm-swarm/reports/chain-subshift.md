# Lane chain-subshift: S3b of sec:chain-core

This lane covers the retained subshifts, the symbolic core `Y_0`, `Y_0 = CR(T)`, and the defects of noncyclic edges.
Parent scope: `notes/nm-swarm/reports/chain-core.md`.  Snapshot origin/main 09d8de801 (09-13).
Tex: non_mf_groups_exist.tex lines 1400–1426, proof of lem:chain-core-models.

## Key split of S3
- **S3b, this lane (16 keys):**
  - `9ea50b0ff631` (Z_r), `cbf45b0e1c51` (periodic extension), `1d52a79f1fef` (dense periodic points, cycle condition), `f7c8d8aab016` (nonempty, Z_{r+1} ⊆ Z_r);
  - `b39310f67614` (Y_0), `ded9e9646e4b` (nonempty, Y_0 ⊆ X), `758517bf8d56` (language stabilization), `647f44a95b8a` (cycle condition of Y_0), `ffa61d258258` (characterization);
  - `048953d87f92` `ae9c3d8b9922` `4fc54b29a740` `a08f25fce44c` (Y_0 = CR(T));
  - `d8f8d764406c` `9c49a2efb0ca` `854ec7cb0423` (noncyclic edge ⇒ P).
- **S3a, chain-words (12 keys):** `53fd5ea7d3d0` `9bc3873fb872` `078684fc2a60` `dfc6d4510272` `8bf7f40918d5` `56b6a80cc911` `2ed7f807a3a6` `57cd1b63930c` `0941296cf395` `4aede6d48b4d` `b94a006ee638` `533771f4f22d`.
- `d8e1a694d87c` stays with S2 and S4.  The wandering sentence ("these defects are wandering by nesting") belongs to S2.

## Existing carriers (origin/main and the Mathlib pin, grepped for uses)
- Mathlib `SymbolicDynamics.FullShift`: `shift` (`shift g x h = x (g + h)`), `cylinder`, `isOpen_cylinder`, `isClosed_cylinder`, `Subshift`.  Also `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`.
- `Pestov91.Subshift` and `Pestov91.SubshiftMinimal` are specific to the Toeplitz shift (`cyl`, `exists_cyl_subset`).  They are not reused here.
- Nothing on origin or in `lanes/*.files` covers retained subshifts, symbolic cores, chain recurrence of subshifts, or noncyclic-edge defects.

## Conventions (agreed with chain-words 09-13)
- Definitions take `{A : Type*} (X : Set (ℤ → A))` and no instances.
- Theorems add `[Finite A] [TopologicalSpace A] [DiscreteTopology A]`, `hXc : IsClosed X`, and `hX : ∀ n : ℤ, Set.MapsTo (SymbolicDynamics.FullShift.shift n) X X`.
- `T` is the shift by one: `(T x) i = x (1 + i)`, i.e. `shift 1`.
- Word graphs come from chain-words: module `GroupApproximation/Dynamics/SubshiftWordGraph.lean`, namespace `GroupApproximation.WordGraph`.
  - Definitions: `word x i n`, `language X n`, `wordEdge X r`, `wordGraph X r`, `IsCyclicEdge X r w`, `CycleCondition X`.
  - Lemmas: `init_word`, `tail_word`, `wordEdge_word`, `exists_realize_of_word_mem_language`.
  - From `SubshiftCyclePeriodic.lean`: `exists_periodic_of_isCyclicEdge`.
- The periodic realization of a cyclic edge is chain-words' `exists_periodic_of_isCyclicEdge`.  This lane uses it for cbf45b0e1c51 (within Z_r).

## Planned modules
1. `GroupApproximation/Dynamics/SubshiftLanguageStabilization.lean` has no upstream dependency; its probe is in progress.  Declarations:
   - `nonempty_iInter_of_antitone`
   - `image_iInter_eq_iInter_image_of_antitone`
   - `exists_eq_iInter_of_antitone`
   - `exists_image_eq_image_iInter_of_antitone`
   - `exists_restrict_image_eq_of_antitone` (758517bf8d56; also available to chain-itinerary for `ρ_lm(Y_l)`)
   - `mem_of_forall_finset_agree` (Y_0 ⊆ X)
2. `GroupApproximation/Dynamics/RetainedSubshift.lean` needs chain-words' word-graph names.  Declarations:
   - `retainedSubshift X r := {x | ∀ i, IsCyclicEdge X r (word x i (r+1))}`, with `isClosed_retainedSubshift` and `shift_mem_retainedSubshift`
   - `exists_periodic_extension` (cbf45b0e1c51)
   - `denseRange_periodic_retainedSubshift` and `cycleCondition_retainedSubshift` (1d52a79f1fef)
   - `retainedSubshift_nonempty` and `retainedSubshift_succ_subset` (f7c8d8aab016)
3. `GroupApproximation/Dynamics/CoreSubshift.lean`.  Declarations:
   - `coreSubshift X := ⋂ r, retainedSubshift X r` (b39310f67614)
   - `coreSubshift_nonempty` and `coreSubshift_subset` (ded9e9646e4b)
   - `cycleCondition_coreSubshift` (647f44a95b8a); only length-(s+1) stabilization is needed
   - `mem_coreSubshift_iff` (ffa61d258258)
4. `GroupApproximation/Dynamics/CoreSubshiftChainRecurrent.lean` needs hull-euler's chain-recurrent set.  Declaration: `coreSubshift_eq_chainRecurrentSet` (048953d87f92, ae9c3d8b9922, 4fc54b29a740, a08f25fce44c).
   - Forward: an accurate closed chain at `x` agrees on a window around `i`, so the words `x_j[i, i+r]` form a closed walk.
   - Converse: realize the edges of a cycle through `x[-N, N+1]` by points of `X`.
5. `GroupApproximation/Dynamics/NoncyclicEdgeDefect.lean`.  Declarations:
   - `reachableCylinderUnion X r b` (P) and `isClopen_reachableCylinderUnion`
   - `mapsTo_shift_reachableCylinderUnion` (T(P) ⊆ P, 9c49a2efb0ca)
   - `not_reachable_of_not_isCyclicEdge` (d8f8d764406c)
   - `shift_mem_defect_of_not_isCyclicEdge` (Tx ∈ P∖T(P), 854ec7cb0423)

## Interfaces needed
- **chain-words:** the word at a position, the language at a length, the level-r edge relation, `IsCyclicEdge`, `CycleCondition`.  Asked; a proposed spelling was sent.
- **hull-euler (S2):** the chain-recurrent set.  Is it stated for `T : X → X` or `X ≃ₜ X`, and over a metric or a uniform space?  Asked.

## Residual Props
None yet.

## Progress log
- 09-13: plan landed.  Module 1 written and probing.
