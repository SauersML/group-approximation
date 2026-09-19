# Top-shell link collapses: formula witness, obstruction, sign-hull certificates (2026-09-19)

Nodes: `zn-rips-top-shell-formula-link-collapse` (claim), `zn-rips-top-shell-formula-link-collapse-proof` (route),
`zn-rips-top-shell-sign-hull-certificates` (claim) and its `-proof`. All totals are in `results.txt`.

Throughout, `k` is the level (the programs call it `n`), `r` the radius, `E = e_k`,
`Lmax = {x in Z^k : 1 <= |x|_1 <= r, x > 0}`, `Top = {|x| = r}`, `Z_0 = Top cap {x_k = 0}`.
Every program builds its sets from these definitions and uses explicit `d_1` distances. None uses symmetry.

## Files

| file | role |
|---|---|
| `tools/zgen.py k r` | prints `Z_0` (one point per line) |
| `tools/tgen.py k r` | prints `Top \ Z_0` (points with `|x| = r`, `x_k >= 1`) |
| `tools/gen.py k r desc/asc` | writes `L-k-r.txt` (`Lmax`) and `K-k-r-<order>.txt`: lines `K u \| e_j + e_k`, `j` the last nonzero index of `u`, sorted by `j` |
| `tools/kzc1.cpp` | the (K)/(D) line replayer of `z8-rips-scale-11-reduces-to-top-shell-link-collapses` (copied unchanged) |
| `tools/udom9.cpp` | formula witness, one-step order-free test: a dominator `v notin Z_0`, `d(v,w) <= r`, of `N[b]` inside `N(u) cap Lmax` |
| `tools/udom10.cpp` | `udom9` with a choice of norm-two witness (`WIT=max` is the argmax witness) |
| `tools/udom11.cpp` | the obstruction test of Claim 2 (candidates in all of `N(u) cap Lmax`, blockers outside `Z_0`) |
| `tools/ex66.py` | the explicit example of Claim 2 at `(6,6)`; its output is `ex66.out` |
| `tools/shdom.cpp` | argmax witness, `F`-certificate test with `v` near `b` or in the box |
| `tools/shdomw.cpp` | all witnesses `w in hull(0,u,E)` with `|w| <= WMAX`, complete box search for `v` |
| `prefix_avoids_T.py [DIR]` | checks that the (8,11) (D) prefix and tail never delete or use a point of `T` |
| `inputs/` | the point files named in `results.txt` |

`shdomw` environment variables:
- `WMAX` (default 3) is the largest witness norm tried.
- `STOP1=1` stops at the first good witness.
- `TOPF=1` sets `F = Top`; `TOPF=2` sets `F = {x in Top : x_k <= 1}`; the default is `F = Z_0`.
- `ONLYUNB=1` skips balanced `u`.

A `u=... good: [w] ngood=m` line lists the witnesses that certify `u`. `ngood=0` means none does: for every
witness in range, some bad point has no valid `v` anywhere in its box. With `TOPF=1` and `WMAX = r - 1`, the
witness range is complete.

## How to run

```
g++ -O2 -o shdomw tools/shdomw.cpp
python3 tools/zgen.py 6 6 > Z-6-6.txt
WMAX=3 STOP1=1 ./shdomw 6 6 Z-6-6.txt | tail -n 1
python3 tools/tgen.py 6 6 > T-6-6.txt
TOPF=1 ONLYUNB=1 WMAX=3 STOP1=1 ./shdomw 6 6 T-6-6.txt | tail -n 1
g++ -O2 -o udom11 tools/udom11.cpp
./udom11 6 6 Z-6-6.txt | tail -n 1
python3 tools/gen.py 6 6 desc
g++ -O2 -o kzc1 tools/kzc1.cpp
./kzc1 6 6 L-6-6.txt K-6-6-desc.txt 1 985 /dev/null | tail -n 1
python3 tools/ex66.py
python3 prefix_avoids_T.py experiments/zn-rips-link-collapse-scale-11-2026-09-19
```

The large scales (`(7,7)`, `(7,8)`, `(8,11)`) were run in shards under `nice -n 19` with a timeout, and several were
stopped early. `results.txt` says which, and how far each got.
