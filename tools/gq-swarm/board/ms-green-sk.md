# ms-green-sk
Direction: make the simple Kazhdan manuscript's endpoint closure (GroupApproximation/Manuscript/SimpleKazhdanSofic/**) build GREEN on current main.
- 09-18 ~14:45 start. Known red at 505b3b720 (bh-pal-wire, 10:40): LeavittK2.FieldTwoAction, LeavittK2.PaddedCentral.MatrixId,
  LeavittK2.PaddedCentral.Vectors, LeavittK2.RowColumn.VecProd, SkRows.SteinbergWeyl.Diagonal (all unchanged on main since, last touched 09-17 22:xx).
- Probe 1 (origin/main as is, these 5 targets): queued.
- 15:23 probe 1 died at msi VPN (outage), no build ran. Errors instead read from bh-pal-wire's 10:40 MSI log:
  VecProd (2x unusedSectionVars), FieldTwoAction (unusedSectionVars), MatrixId (rw Pi.single_eq_of_ne' postponed-arg
  mismatch), Vectors (noncommPiCoprod_mulSingle: N not inferred from `_`), Diagonal (split_ifs <;> simp_all max recursion).
- Minimal fixes in overlay (GQ_BASE 69db09693): omit-in x3; `show ... from` for the rw; explicit ϕ/hcomm; case-split proof of
  diagonal_weyl_eq with set_option linter.unusedSimpArgs false in. Probe 2 queued ~15:30.
- 16:40 probe on v4 was cleared by the coordinator at restart; it never built.
- 19:36 after restart: the 5 edits are on main BYTE-IDENTICAL to my overlay (landed by the coordinator in 8d6acdcd0c, merge a2646f3723; main e6c93a1fe4).
  The overlay is emptied. FIX-GRAPH's 5 SK OPEN nodes come from the 3c8b417428 build (14:39), which PREDATES that landing. Its errors are exactly the 7 my edits fix.
- 19:37 probe 3 (empty overlay, current main) queued: the 5 fixed modules + 7 downstream SK tops (LeavittK2.{CohnK2.BaseChangeConjLeavitt,
  CohnK2.RelKernelWire, RowColumn, StableReduction.FiveStepRankFourFix, Superperfect.Swindle, UsedLinks, UsedRankFourCloseCohn}); 44 SK modules recompile.
- 21:00 SLURM-BLOCKED (the association counter underflowed). Probe 3 is still queued, and I have NOT re-probed. FIX-GRAPH: my 5 nodes OPEN -> UNPROBED (fix on main).
  Static scan of the 40 never-built downstream SK modules for the leaf error classes (Pi.single_eq_of_ne' in rw, noncommPiCoprod_mulSingle _,
  split_ifs<;>simp_all, Matrix.single_mulVec shape) and for every deprecated alias at the Mathlib pin: no hits. Nothing more to fix without a build.
- Armed (task b12mvum89): wait for probe 3; if it has no verdict, wait for SLURM-BLOCKED to be removed, then re-probe ONCE with the same targets.
- 21:16 probe 3 DEFERRED (sbatch rejected: AssocMaxSubmitJobLimit). Watcher b12mvum89 is now waiting for SLURM-BLOCKED to be removed, then re-probes once.
