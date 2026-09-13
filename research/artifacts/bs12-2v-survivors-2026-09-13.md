# Small elements of 2V against every conjugator (2026-09-13)

Target: `bs12-embeds-in-brin-thompson-2v`. This is a finite computation, not a
proof of the target, and it changes no node status.

## Test

The earlier searches (`research/artifacts/bs12-2v-search-2026-09-13.md`) fixed
small conjugators `f`. This run instead asks which small `g` could be the image
of `s` in an embedding `BS(1,2) → 2V`, for **any** conjugator `f`. Two exclusions
are rigorous:

- **torsion:** `g^p = id` for some `p`.
- **hyp:** some brick `u → v` of the table of `g^p` has, in every coordinate,
  `u_j` and `v_j` prefix-comparable, and in some coordinate `|u_j| ≠ |v_j|`.
  - In that coordinate the brick contains the fixed point `u_j t^∞` (or
    `v_j t^∞`), so `g^p` has a fixed point `x` with `δ_{g^p}(x) ≠ 0`.
  - If `q` is the least period of `x`, then `δ_{g^p}(x) = (p/q) δ_{g^q}(x)`, so
    `δ_{g^q}(x) ≠ 0`.
  - Item 1 of `bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets`
    forbids that whenever `f g f^-1 = g^2` for some `f ∈ 2V`.

## Runs

- **Classifier.** `bs12-2v-survivors-2026-09-13/bs12survive.py`, md5
  `c17d47475a8fa2d1b72544eda168da39`. It imports `bs12search.py` from the
  earlier artifact unchanged (md5 `ba4e6c9038d897cd744e38c08bf383b8`), and every
  shard log prints both md5s.
- **Elements.** Every table with `n ≤ 5` bricks, sides of length `≤ D`, and
  every bijection between domain and range bricks.
- **Procedure.** For `p = 1, …, 48` it tests `torsion` and `hyp` on `g^p`; above
  4000 bricks it reports `blowup`; `survivor` otherwise.
- **Self-test** (output `selftest OK`):
  - the baker map and an attracting `V` element are `hyp` at `p = 1`;
  - the Kojima--Sheng-type root `h_1` is `hyp` at `p = 2`;
  - two 2- and 3-cycles of bricks are `torsion`;
  - a 64-cycle of depth-6 cubes is `survivor`.

| Slurm job | `D` | tables | hyp | torsion | blowup | survivor |
|---|---|---|---|---|---|---|
| 713316 | 3 | 4,646,571 | 4,553,732 | 92,823 | 0 | 16 |
| 713317 | 4 | 5,429,915 | 5,328,644 | 101,255 | 0 | 16 |

- **Completion.** All 32 shards of each array printed `DONE` and `ALLDONE`, with
  no errors. The 4,646,571 total matches job 705410.
- **Logs.** `bs12-2v-survivors-2026-09-13/job713316-logs.txt` and
  `job713317-logs.txt`, with the sbatch files.

## Survivors

- **Script.** `bs12-2v-survivors-2026-09-13/bs12order.py`, md5
  `deae4e5292ea2369677d6cc509b48846`.
- **Procedure.** It reduces tables by merging sibling bricks split on the same
  coordinate, then tests `torsion` and `hyp` for `p ≤ 4096`.
- **Run.** `srun` job 713880; output in `job713880-order.log`.
- **Result.** In each file the 16 survivors are 16 distinct reduced tables, and
  **every one has exact order 70**.

## Reading

- **Every table is excluded.** Every element of `2V` with a table of at most 5
  bricks and sides of length at most 4 is either torsion or has a periodic point
  with nonzero exponent. So none is the image of `s` under an embedding
  `BS(1,2) → 2V`, for any conjugator `f` of any size.
- **Strength.** This is stronger than jobs 705410 and 706577, which bounded `f`.
- **Scope.** It does not decide the target. A witness needs a nonempty aperiodic
  core and table lengths `L(g^N) = O(log N)`
  (`bs12-images-in-nv-have-logarithmic-table-length`), and the only known
  elements of `2V` with that growth are much larger (Callard--Salo,
  arXiv:2208.00685v3, §6.3).
