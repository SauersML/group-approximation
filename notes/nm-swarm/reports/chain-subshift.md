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

## Conventions (agreed with chain-words 09-13)
- Definitions take `{A : Type*} (X : Set (ℤ → A))` and no instances.  Namespace `GroupApproximation.ChainCore`.
- Theorems add `[Finite A] [TopologicalSpace A] [DiscreteTopology A]` as needed, `hXc : IsClosed X`, and `hX : ∀ n : ℤ, Set.MapsTo (SymbolicDynamics.FullShift.shift n) X X`.
- `T` is the shift by one: `(T x) i = x (1 + i)`, i.e. `shift 1`.  On the space `X` it is `(hX 1).restrict (shift 1) X X`.
- For `CR(T)` the alphabet carries `[UniformSpace A] [DiscreteUniformity A]`, and `X` carries the subtype of the product uniformity.  On a compact space every compatible uniformity gives the same `CR(T)` (hull-euler's `chainRecurrentSet_eq_of_compact`).
- Word graphs come from chain-words (`GroupApproximation/Dynamics/SubshiftWordGraph.lean`, namespace `GroupApproximation.WordGraph`).

## Modules
1. `GroupApproximation/Dynamics/SubshiftLanguageStabilization.lean` was landed at 239b3a4ca (probe 0913-154526-50538, `# PROBE GREEN`).  Declarations:
   - `nonempty_iInter_of_antitone`, `image_iInter_eq_iInter_image_of_antitone`, `exists_eq_iInter_of_antitone`
   - `exists_image_eq_image_iInter_of_antitone`, `exists_restrict_image_eq_of_antitone` (758517bf8d56)
   - `mem_of_forall_finset_agree`
2. `GroupApproximation/Dynamics/RetainedSubshift.lean` was landed at dbb102249 (probe 0913-155918-72707, `# PROBE GREEN`).  Declarations:
   - `retainedSubshift X r` (9ea50b0ff631), `retainedSubshift_eq_iInter`, `isClosed_retainedSubshift`, `mapsTo_shift_retainedSubshift`
   - `wordEdge_init`, `reflTransGen_init`, `retainedSubshift_succ_subset` (f7c8d8aab016, the inclusion), `retainedSubshift_antitone`
3. `GroupApproximation/Dynamics/CoreSubshift.lean` was landed at dbb102249 (same probe).  Declarations:
   - `coreSubshift X` (b39310f67614), `mem_coreSubshift_iff` (ffa61d258258)
   - `coreSubshift_subset_retainedSubshift`, `isClosed_coreSubshift`, `mapsTo_shift_coreSubshift`
   - `coreSubshift_subset` (ded9e9646e4b, the inclusion `Y_0 ⊆ X`)
   - `language_eq_image`, `exists_language_retainedSubshift_eq` (758517bf8d56)
4. `GroupApproximation/Dynamics/CoreSubshiftChainRecurrent.lean` was landed at b34b97bfe (probe 0913-165101-16822, `# PROBE GREEN`).  It consumes hull-euler's `ChainRecurrence.lean` (20911e5b2).  Declarations:
   - `windowRel X N`, `windowRel_mem_uniformity`, `exists_windowRel_subset`, `chainStep_windowRel_iff` (4fc54b29a740)
   - `reflTransGen_word_of_transGen` (048953d87f92): a closed chain accurate on `[-N, N]` makes the words `x_k[i, i + r)` a closed walk through the edge `x[i, i + r]`.
   - `transGen_of_reflTransGen` (ae9c3d8b9922): realizing the edges of the cycle through `x[-N, N + 1]` by points of `X` gives a closed chain at `x`.
   - `isChainRecurrent_iff_mem_coreSubshift`, `chainRecurrentSet_eq_preimage_coreSubshift`, `coreSubshift_eq_chainRecurrentSet`, `isMetricChainRecurrent_iff_mem_coreSubshift` (a08f25fce44c)
5. `GroupApproximation/Dynamics/NoncyclicEdgeDefect.lean` was landed at dbb102249 (same probe).  It carries d8f8d764406c 9c49a2efb0ca 854ec7cb0423.  Main reassigned module 5 to fff-quotient, but it was already written, so this lane kept it and sent fff-quotient the SHA.  Declarations:
   - `reachableCylinderUnion X r b`, `reachableCylinderUnion_eq_inter`, `isClopen_setOf_word_mem`, `isClosed_reachableCylinderUnion`
   - `not_reflTransGen_of_not_isCyclicEdge` (d8f8d764406c)
   - `mapsTo_shift_reachableCylinderUnion` (T(P) ⊆ P, 9c49a2efb0ca)
   - `shift_one_injective`, `shift_mem_diff_of_not_isCyclicEdge` (Tx ∈ P ∖ T(P), 854ec7cb0423), `diff_image_shift_nonempty_of_not_isCyclicEdge`
6. `GroupApproximation/Dynamics/RetainedSubshiftPeriodic.lean` is in progress.  It consumes chain-words' `SubshiftCyclePeriodic.lean` (6078315b6).  Planned declarations:
   - `retainedEdge X r`, `reflTransGen_retainedEdge_of_path`, `exists_periodic_extension` (cbf45b0e1c51)
   - `exists_periodic_agree_retainedSubshift`, `retainedSubshift_subset_closure_periodic`, `cycleCondition_retainedSubshift` (1d52a79f1fef)
   - `retainedSubshift_nonempty` (rest of f7c8d8aab016), `coreSubshift_nonempty` (rest of ded9e9646e4b)
   - `cycleCondition_coreSubshift` (647f44a95b8a)
   - Periodic extension: every edge of a retained path is cyclic, so a walk returns from its last suffix to its first prefix.  The path followed by this walk is a closed walk, and reading it periodically gives a periodic point of `Z_r` that extends the path.
   - Nonemptiness: a point of `X` has two equal words `x[i, i + r) = x[j, j + r)` with `i < j`, so the edge `x[i, i + r]` is cyclic.

All landed modules are unwired and queued in `wire-queue.txt`.

## Remaining keys
chain-words landed `SubshiftCyclePeriodic.lean` at 6078315b6, so these are unblocked.  Module 6 carries them:
- cbf45b0e1c51, 1d52a79f1fef, 647f44a95b8a;
- the nonemptiness halves of f7c8d8aab016 and ded9e9646e4b.

## Census rows
`metadata/nm-census-rows/chain-subshift.tsv` holds 13 rows: 9 landed at dbb102249 and 4 at b34b97bfe.

## Interfaces consumed
- **chain-words**, landed 7c770d047: `word`, `language`, `wordEdge`, `IsCyclicEdge`, `CycleCondition`, `init_word`, `tail_word`, `word_shift`, `wordEdge_word`, `exists_realize_of_word_mem_language`.
- **chain-words**, landed 6078315b6: `exists_edgeWalk_of_reflTransGen`, `edge_apply_eq_of_tail_eq_init`.
- **hull-euler**, landed 20911e5b2:
  - `ChainStep`, `IsChainRecurrent`, `chainRecurrentSet`, stated for `T : X → X` over a uniform space
  - `isChainRecurrent_iff_metric`, `chainRecurrentSet_eq_of_compact`

## Model tests (module 6)
`retainedSubshift_nonempty` assumes `[Finite A]`, shift invariance `hX` and `X.Nonempty`.  Each is needed:
- If `X = ∅`, then `Z_r = ∅`.
- Without `Finite A`: let `A = ℤ` and let `X` be the shift orbit of `x i = i`.  The level-1 edges are `n → n + 1`, none of them cyclic, so `Z_1 = ∅`.
- Without `hX`: let `X = {x}` with `x 0 = 0` and `x i = 1` for `i ≠ 0`.  The only level-1 edge is `0 → 1`, which is not cyclic, so `Z_1 = ∅`.

`exists_periodic_extension`, `retainedSubshift_subset_closure_periodic` and `cycleCondition_retainedSubshift` take no hypotheses on `X`.

## Residual Props
None.  No binder stands for a cited result.

## Progress log
- 09-13: plan landed.  Module 1 landed at 239b3a4ca.
- 09-13: modules 2, 3 and 5 landed at dbb102249.  Module 4 started on hull-euler's 20911e5b2.
- 09-13: module 4 landed at b34b97bfe.  13 census rows are in `metadata/nm-census-rows/`.  Module 6 started on chain-words' 6078315b6.
