# VR(Z^8, d_1; 9): the (D)-only obstruction and a partial link-collapse certificate

Continues `../zn-rips-link-collapse-2026-09-18` (which certifies (8,8)) and `../zn-rips-lifted-domination-core-2026-09-18`
(the (D)-only obstructions). Notation: `Lmax_8` at `r = 9` has 299,208 points, `E = e_8`.

## 1. The obstruction (used by `research/z8-rips-lifted-domination-certificates-fail-at-scale-9-proof.md`)

- `cores/K8_9.txt.gz`: 113,321 points, sorted, one per line. It is the stall set `a8_9` of `ilv4 8 9`.
- `gfpr.cpp`: `gfp.cpp` of the core directory plus a wall-clock budget and a resume position (argv[5..7]), and `-` for "no
  start file". On `a8_9` it finds `F(a8_9) = a8_9`.
- `kchk` (the checker on main, unchanged) verifies that `K8_9` is self-blocking. The output is in `results.txt`.

## 2. The partial (D)+(K) certificate at (8,9). NOT a proof of contractibility.

The pieces:
- `partial/d-prefix-8-9.txt.gz` has the 185,887 `A`/`D` lines of `ilv4`, from `Lmax_8` down to `a8_9`. `vcert2` of the core
  directory checks them: all moves are valid, and 113,321 points are left.
- `partial/k-stages-1-12-8-9.txt.gz` has the `kzf` stages 1–12, concatenated, starting at `a8_9`.
  They hold 17,750 moves: 11,148 `K` and 6,602 `D`. The `D` moves come in the cascades that `K` moves unlock, in
  stages 2 and 4–6. The moves leave 95,571 points, stored in `partial/end-stage-12-8-9.txt.gz`.
- `kzv5` replay checks all 12 stages. Each stage's end set equals the search output. See `results.txt`.
  - Stages 1–3 were searched with `kze`.
  - Stages 4 and later were searched with `kzf`.
- For k = 2..7 at r = 9, contractibility is already on main (`z7-rips-contractible-at-scale-9`).

Structural observation (from (8,8), where it is exact):
- In the (8,8) certificate, the `K` moves are exactly the 5,152 norm-8 points with `x_8 = 0`, and the rest is a D cascade.
- At (8,9), the stall set after the `D` prefix starts at 113,321 points. Each `K` stage removes about 500–1,600 points
  per 1,100 s.
- The estimate is about 22k `K` moves in total, 11,148 of them done, before a D cascade. That is about 5 more CPU-hours of `kzf`, then a replay.

Cost at (8,9):
- each `K` search takes about 0.17 s CPU;
- 70% of that is the protected collapse, and about 30% is building the link (17–19k points);
- a dirty-worklist variant gave no speedup.

(8,10) does not fit in 2 GB. `a8_10` has 186,502 points, and the bit adjacency alone is about 4.3 GB.

## Reproduce / resume

```
g++ -O2 -march=native -o kzf kzf.cpp ; g++ -O2 -march=native -o kzv5 kzv5.cpp ; g++ -O2 -o gfpr gfpr.cpp
zcat partial/end-stage-12-8-9.txt.gz > e12.txt
./kzf 8 9 e12.txt e13.txt k13.txt 1100            # next search stage; repeat until "REACHES"
./kzv5 8 9 start.txt kstage.txt end.txt 700       # replay one stage (exit 3 = budget, resume on the rest)
```
