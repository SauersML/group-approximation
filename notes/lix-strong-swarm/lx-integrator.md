# lx-integrator: LIX-strong swarm integration lane (clone cs-endpoint)

## GREEN
- Board `notes/lix-strong-swarm/BOARD.md` landed 40801adec, read at 01b92308d. It lists every residual of D1 with file:line, state, owner lane and sha.
- Integration baseline probe 0912-100606-67380: cs-endpoint, acn112 cores 64-71, base 4c343e664.
  - Modules: `ProblemLIXStrongAssemblyHalves`, `LIXLemmaTwoGenTwo`, `LIXStepDGenReal`, `LIXKGenOfStepC`.
  - Result: PROBE GREEN, 9456 jobs, purge 0, 0 modules rebuilt. All four were restored with the same input hash.
  - This shows the consumer tops are consistent at that base. It is not a fresh elaboration.
- Duplicate scan at c3b58d90c: `/projects/standard/hsiehph/sauer354/lixs/dupscan-c3b58d90c.out`, 6111 modules, 832 of them LIX.
  - (a) 6 name collisions, all in the parked red `OddPTupleBd`/`OddPTupleSlot` versus `OddPTuple`. lx-diag has been told.
  - (b) 47 signature matches, mostly definitions with equal types. The real same-fact pairs are on the board as cleanup; none blocks.

## AUTHORED, UNVERIFIED
- none (no Lean authored)

## NEEDS
- Resume me by SendMessage for:
  - the ~45-minute board refresh;
  - an integration probe after each producer landing (local square, WuStepDData, RealTorusModP, RealBundleModP, KZeroStepCDataOf, the assembly files).
- Root wiring is on hold until session nonsofic-existence-3a reports that wave bo6h618iu has finished. Rules accepted:
  - `tools/nm-swarm/dupcheck.py` before each build and each push;
  - no landing while an `nm-root` job is running or pending;
  - root builds named `lx-root`;
  - insert after the last import only.

## TRAPS
- An empty-overlay probe of tops that have not changed gives `mentioned-not-built` on every module, which means restore by input hash. Cite it as a consistency check only. For a fresh compile, delete the artifacts first.
- LANES.md was edited after launch: lx-lhK-a and lx-lhK-b now share clone cs-endpoint with this lane, so integration probes queue behind their probes under the clone lock.
- `git fetch` in the shared checkout prints a `.git/gc.log` warning about unreachable loose objects. It is harmless; never run `git prune` there.
