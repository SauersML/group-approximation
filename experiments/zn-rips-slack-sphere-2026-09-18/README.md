# Slack-one sphere criterion for Rips complexes of Z^n

This directory supports `zn-rips-slack-sphere-criterion` and `z7-rips-contractible-at-scales-12-14-16-and-18-to-54`.

## Programs

All programs are single-threaded, with no dependencies beyond the C++ standard library or numpy.

- `slack_crit.cpp`. Build with `g++ -O2 -o slack_crit slack_crit.cpp`. Usage: `./slack_crit n rmin rmax [printU]`.
  - Computes `U(n,r)` with a complete balance test.
  - Reports "not handled" when an unbalanced partition has fewer than `n` parts.
  - Otherwise searches, for every `(x, k)` with `k` the first index of a block of equal values, for a slack-one
    dominator `y`. It checks `y` against every signed arrangement `z` of every partition in `U(n,r)` with `z_k > 0`.
  - Prints `without-y=<count of (x,k) with no certified y>`.
  - With a fourth argument, it also prints `U(n,r)` as `U r=<r>: ...`.
- `slack_crosscheck.py`. Usage: `python3 slack_crosscheck.py n r "p1;p2;..."`, where each `p` is a comma-separated
  partition.
  - An independent numpy re-implementation of the dominator search, for a given list `U(n,r)`.
  - It materializes all signed arrangements as an int16 array.
  - It orders `y` candidates by `| |y| − r/2 |`.
- `sphere_free.cpp`. Build with `g++ -O2`. Usage: `./sphere_free n r`.
  - An explicit point-level replay on `Lmax = L([−r,r]^{n−1} × [0,r])`.
  - Deletes the balanced sphere points first.
  - For each unbalanced sphere point `x`, searches `hull(0,x)` for `y ≻ 0` with the slack-one inequality and
    `N[x] ∩ C ⊆ N[y]`. The current set `C` still contains all unbalanced sphere points, so the result does not depend
    on the deletion order.
- `u_only.cpp`, `slack_shard.cpp`, `runner.sh`, `U8.txt`: the sharded `n = 8` check. `./u_only 8 r r 1` prints `U(8,r)`
  into `U8.txt`, with the same code as `slack_crit.cpp`. `./slack_shard 8 r U8.txt s S` runs the dominator search of `slack_crit.cpp`
  for the partitions with index `≡ s (mod S)`, with one extra exact pruning bound. `runner.sh` drives the shards.
- `hull_rounds.py`, `sphere_rounds.cpp`: see F.
- `U7.txt`, `U7small.txt`. The lists `U(7,r)` printed by `slack_crit 7 r r 1` and fed to `slack_crosscheck.py`.

## Results (`results.txt`)

- **A.** `./slack_crit 7 10 54`.
  - `without-y=0` at `r = 12, 14, 16` and at every `r` in `18..54`.
  - "not handled" at `r = 10, 11, 13, 15, 17`.
  - Exit code 1 only because of those not-handled scales.
- **B.** `slack_crosscheck.py` for `n = 7` at every `r` with `U(7,r)` nonempty among `12, 14, 16, 18, 19, 21, …, 35`.
  Every run gives `without-y=0`.
- **C.** `./slack_crit n n 30|40` for `n = 4, 5, 6`.
- **D.** `sphere_free` at `(4,5), (5,6), (5,7), (5,9), (6,8), (6,10), (6,11)`. Every unbalanced sphere point is
  slack-one dominated against the current set, and `undominated=0` everywhere. This agrees with C.
- **E.** `n = 8`.
  - `./slack_crit 8 r r` for odd `r = 69, …, 59`.
  - `U8.txt` status lines for odd `37..57` and even `20..36`.
  - The shard logs for those scales. All 227 shards exit 0 with `without-y=0`.
- **F.** The limit of the method at scales with non-full-support unbalanced partitions. The unbalanced sphere points
  with a zero coordinate cannot all be deleted first.
  - `hull_rounds.py n r` allows any `y ∈ hull(0,x)`, `y ≻ 0`, against the full current set on `Lmax`, and deletes in
    maximal rounds. It leaves 96 of 176 points at `(5,5)` and 284 of 512 at `(6,6)`.
  - `sphere_rounds.cpp` is a point-level slack-one version with rounds. It gets stuck at `(5,5), (6,6), (6,7), (6,9)`
    and `(7,10)`, and deletes everything at `(5,6), (6,8), (7,12)`.
