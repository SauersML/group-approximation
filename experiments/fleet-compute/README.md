# Fleet compute: the shared MSI environment

Maintained by the `compute-steward` lane. The user's standing orders for compute:
- share compute and never build the same thing twice;
- run no unnecessary MSI compute;
- do not oversubscribe sioux (acn112, acn116), which is shared with other users;
- kill what you no longer need;
- run nothing heavy on the laptop;
- never use RAM-backed `/tmp` for builds or storage.

## Paths

All paths are on MSI, under the `/projects` mount.

| What | Path |
|---|---|
| Shared Python 3.10 (numpy, scipy, networkx, python-sat) | `/projects/standard/hsiehph/sauer354/fleet-env/venv/bin/python` |
| SAT solvers | `/projects/standard/hsiehph/sauer354/fleet-env/bin/kissat`, `/projects/standard/hsiehph/sauer354/fleet-env/bin/cadical` |
| CryptoMiniSat bindings (`pycryptosat`) | `/projects/standard/hsiehph/sauer354/kdf-sat/venv/bin/python` (Python 3.8; belongs to `kdf-sat`, use it read-only) |
| Shared Leavitt checker | `/projects/standard/hsiehph/sauer354/nonsofic-certificates/current/`, a copy of `experiments/nonsofic-certificates/` at the commit in `current/VERSION` |
| GAP 4.14 (base library only) | `module load sagemath/10.7`, then `sage -gap -q file.g`, or `sage -c '...'` with `libgap` |
| Cairn check workspaces | `/scratch.global/sauer354/cc-<lane>`: a `--shared` clone of the MSI checkout at the tip; delete it when done |
| Per-lane outputs | `/scratch.global/sauer354/<lane>/` |

- **The shared env:** do not `pip install` into it. If a lane needs a package, message `compute-steward`, which installs it once for everyone.
- **GAP:** it runs inside a Singularity container, so each start costs a few seconds. It has `FpGroup`, coset enumeration and `LowIndexSubgroupsFpGroup`. The `kbmag` and `LowIndex` packages are not installed. Ask before building your own GAP.
- **The build script:** `/projects/standard/hsiehph/sauer354/fleet-env-build.sh` built the env with 4 cores, niced, on projects storage. Rerunning it is idempotent.

## Where to run

- **Direct runs.** `msi '<cmd>'` runs on acn112, one of the two sioux nodes: 128 cores and 503 GiB, shared with other users. Stay within 4 cores, 16 GB and 30 minutes, prefix with `nice -n 10`, and set `TMPDIR` to your projects or scratch directory.
- **Bigger or longer work.** Use `sbatch` on `msismall` or `agsmall`: at most 16 cores, 64 GB and `-t 01:00:00`. Put `--output` on `/projects` or `/scratch.global`. The `sioux` partition is allowed only within the same limits.
- **Name jobs `<lane>-<task>`** so they can be attributed.
- **RAM-backed directories.** `/tmp`, `/dev/shm`, `/var/tmp` and `/run` are RAM-backed and shared. Never build or store anything there.
- **The laptop** is for git plumbing, grep and file edits only.
- **Slow jobs.** If something takes too long, make it faster (a better encoding, smaller instances, pruning) rather than running it longer.

Example:

```text
sbatch -p msismall -c 4 --mem=16G -t 00:30:00 -J <lane>-<task> \
  -o /scratch.global/sauer354/<lane>/%x-%j.out \
  --wrap '/projects/standard/hsiehph/sauer354/fleet-env/venv/bin/python script.py'
```

## Reuse, do not rebuild

- **Leavitt computations:** import the shared checker from the pinned path above, and do not copy it into lane directories. This covers exact normal forms in `L_{F_2}(1,2)^x`, `F_2[L^x]` arithmetic, automaton composition, the Garden-of-Eden test and the Kervaire--Laudenbach derivation verifier. If you need a newer checker, land the change in the repo and ask `compute-steward` to refresh `current/`.
- **No per-lane builds:** no second Python env, SAT build or GAP install per lane.
- **Lean and `lake`:** build only in existing warm checkouts with warm caches, and only when a lane truly needs it.

## Kill etiquette

- Cancel your own jobs as soon as you have the signal: `scancel <id>` for jobs, `kill <pid>` for direct runs.
- Never touch jobs you cannot attribute to your own lane. That includes `nm-*` (the non-MF swarm), `pool-*` (gam), `k979-*`, and every other user's processes.
- If a fleet job looks hung, message its lane. `compute-steward` kills a job only when its lane is gone.

## Audit, 2026-09-12 09:52 CDT

- **acn112:** load 17 of 128 cores, 6 GiB used of 503 GiB.
- **Fleet processes:** a few seconds' worth of `cairn why` runs and checkouts from `nh-mipstar-groups`, `hyperbolic-sofic`, `nh-fournier-facio` and `cairn-integrator`.
- **Peer jobs, left alone:**
  - `nm-root` and `nm-kh-*` dispatchers;
  - `pool-sw0*` on `msismall`, one of 16 cores running and six pending;
  - `k979-gate` on `sioux` node acl42, 24 cores, plus a pending sweep.
- **acn116:** not reachable without an active job there.
- **Result:** no hung or oversubscribing fleet job, and nothing killed.
