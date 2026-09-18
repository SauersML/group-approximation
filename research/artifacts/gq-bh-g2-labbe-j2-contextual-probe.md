# Probing J_2(Ω_U) = 0: contextual certificates and window obstructions

Lane bh-g2-labbe, 2026-09-18. This artifact holds the exact computation behind
`contextual-closure-certifies-quantum-rigidity` and `labbe-scale-two-commutation-crosses-faults-at-distance-five`.
- **Job.** One Slurm job (`msismall`, one core, 8 GB), job 1326476, 51 s, exit 0.
- **Runs.** A smoke run (`--smoke`, under 3 s) and a ring-5 method listing (`--ring5`, under 1 s) ran directly on one
  core.
- **Script.** `j2probe.py`, reproduced verbatim at the end. It is stdlib Python 3.6, exact, with no randomness. The job
  ran the version with sha256 `4e90ab2e…6872a`. The copy below (sha256 `63d57b2f…22364`) adds only the per-offset method
  log and the `--ring5` mode.

## 1. Why no Gröbner run

A Gröbner computation does not terminate on this presentation, whichever way the answer goes.
- The scale-2 presentation `C_2` has one generator orbit per letter under `Z^2`. If `J_2 = 0`, the relations include
  `[P_0^a, P_v^b] = 0` for every `v`, which is one leading-term orbit per displacement. So even a shift-invariant
  Gröbner basis is infinite.
- A degree-bounded run on a finite window `K` meets roughly `(19|K|)^d` words. That is about `10^12` at `d = 4` for
  `|K| = 50`.

The questions that can be answered exactly are window questions: is `[P_0^a, P_v^b]` zero in `C_2(K)`, the algebra of
the relations supported in `K`?
- **Positive answers.** Context splits, and determinism steps, give certificates of fixed shape.
- **Negative answers.** Explicit two-dimensional representations of `C_2(K)` ("window walls") exclude every
  certificate supported in `K`, of every degree at once. That is strictly more than a degree-bounded run can say.

## 2. The four parts of the script

- **A. Languages.**
  - Labbé: legal `3×3` (94) and `5×5` (229) windows from `ω^k` layouts, as in the recognizability artifact.
  - Calibrations: checkerboard; Ledrappier `x(z+e_2) = x(z) + x(z+e_1)` (box patterns: free bottom row and right
    column, 512 at `5×5`); full 2-shift (512 at `3×3`).
- **B. Determinism closure** (`determinism-closure-certifies-quantum-rigidity`), region `|v|_∞ <= 10`.
- **C. Window walls.** Windows `[0, 2D+1+2m] × [0, 2H]` with a band of `2D` agreeing columns between the two ends.
  Legality is interior-box only, which matches the relations of `C_D(K)`. The transposed language gives the `e_2`
  direction. Also computed: `(6,0)`, with bands `[1,4]` and `[2,5]`.
- **D. Contextual closure** (claim node, item 2). Ring by ring, certify `v` by one of:
  - a determinism step using the current certified set, or
  - a context split over pairwise-commuting rectangles `T ∋ 0`, `T' ∋ v`.

  Rectangles are the Pareto-maximal ones whose offsets are all certified. Their patterns are admissible for every box
  meeting them (partial-box legality). Up to 40 window pairs are tried per offset, largest overlap first. Newly
  certified ring points are reused within the ring.

## 3. Calibration: all PASS

| test | expected | observed |
|---|---|---|
| B checkerboard D=1, Ledrappier D=1,2 | fill region | fill (441 of 441) |
| B full 2-shift D=1 | exactly B_2 | B_2 |
| C full 2-shift | walls at every height | 64 walls at H=1, then the cap |
| C checkerboard, Ledrappier D=1,2 | no walls | 0 at every H computed (Ledrappier: the right end is always determined) |
| D checkerboard, Ledrappier D=1,2 | reach the stop radius | radius 6, 7, 7 (all by determinism) |
| D full 2-shift | nothing beyond B_2 | blocked at ring 3 |

The Labbé language counts (94, 229) agree with the recognizability artifact, and every `5×5` pattern is Wang-valid.

## 4. Labbé results

- **B.**
  - `D = 2`: the closure is exactly `B_4`, so all 40 offsets at distance 5 are open.
  - `D = 1`: the closure is exactly `B_2`.
- **C, `(5,0)` and `(0,5)`.**
  - There are no double faults for `H = 2..6` (heights 5 to 13), with margins `m = 0, 1`.
  - The same holds among globally legal windows.
  - At `H = 2` this is the two-box window, so by item 4 of the claim node a certificate exists there.
  - The numbers of bands leaving one end open grow slowly: 13 to 21 on the left, 15 to 25 on the right, along `e_1`.
- **C, `(6,0)`.** Double-fault bands at heights 5, 7, 9, 11 number `7, 5, 3, 1`, the same for bands `[1,4]` and
  `[2,5]`. At height 13 there are none.
- **C, `(0,6)`.** There is 1 double-fault band at `H = 2`, and none for `H = 3..6`.
- **D, `D = 2`, ring 5.** The listing from `--ring5`:
  - context splits: `(−5,−2)`, `(−2,−5)`, `(−2,5)`, each with two `5×5` windows (listed corners and overlap in the
    output), and their negatives;
  - determinism steps enabled by them: `(−5,−1)`, `(−5,0)`, `(−5,1)`, `(−5,2)`, `(−5,3)`, `(−1,−5)`, `(−1,5)`,
    `(0,−5)`, `(3,5)`, `(5,3)`, and their negatives;
  - uncertified: `(±5,±5)`, `(±5,±4)`, `(±4,±5)`, `(−3,5)`, `(3,−5)`.
- **D, rings 6 to 20.** Nothing is certified. The commuting shapes stay at `(3,6)`, `(5,5)` and `(6,4)`.
- **D, `D = 1`.** Nothing beyond `B_2`.

## 5. Resonance reading (heuristic)

The torus model is in `labbe-shift-is-quantum-rigid-iff-rigid-at-scale-two`:
- fault columns come in triples (lines `x = φ, 0, 1`);
- fault rows come in pairs (lines `y = φ, 0`).

A band pins the torus point to precision `ε(H)`. A double fault along `e_1` at separation `L` needs
`‖L − (φ−1)‖_(φ²Z) < ε(H)`, and along `e_2` it needs `‖L + 1‖ < ε(H)`. The observations match:

| offset | distance | walls |
|---|---|---|
| `(5,0)` | `0.854` | none |
| `(6,0)` | `0.146` | through height 11 |
| `(0,6)` | `0.854` | only at height 5 |

The walls die near `ε ≈ 1/H`. Predicted resonances:
- along `e_1`: `L = 6, 11, 19` (`0.146, 0.090, 0.056`);
- along `e_2`: `L = 7, 12, 20`.

The diagonal offsets, where the closure stops, lie along the normals of the anti-diagonal family (`x + y ∈ {0,1}`,
two adjacent anti-diagonals) and of the diagonal-type faults. Their resonance analysis is the next computation: walls
with diagonal separating bands.

## 6. Status of J_2

- **Positive.** Commutation holds at every distance `<= 4`, and at 26 of the 40 offsets at distance 5.
- **Negative.** Certificates for `(6,0)` need windows of height `>= 13` (within width 7).
- **Open.** Neither decision is reached. The window representations above are representations of the window algebras,
  not of `C_2`. Global ones of dimension 2 are excluded if `labbe-shift-is-wall-rigid` holds.

## 7. Job output (verbatim; long uncertified lists cut at 330 characters per line)

```
[    0.1s] PART A: languages
[    0.2s] Labbe |L_3x3| = 94  |L_5x5| = 229  |L_2x2| = 50
[    0.2s] checker 2/2  Ledrappier 32/512  full 512
[    0.2s] PART B: determinism closure, region |v|_inf <= 10
[    0.2s] CLOSURE checker D=1 |C|=441 max|v|=10 sweeps=2: fills region  [calibration PASS]
[    0.3s] CLOSURE ledrappier D=1 |C|=441 max|v|=10 sweeps=3: fills region  [calibration PASS]
[    0.6s] CLOSURE ledrappier D=2 |C|=441 max|v|=10 sweeps=2: fills region  [calibration PASS]
[    0.7s] CLOSURE full2 D=1 |C|=25 max|v|=2 sweeps=1: = B_2  [calibration PASS]
[    0.7s] CLOSURE labbe D=1 |C|=25 max|v|=2 sweeps=1: = B_2
   .....................
   .....................
   .....................
   .....................
   .....................
   .....................
   .....................
   .....................
   ........#####........
   ........#####........
   ........##0##........
   ........#####........
   ........#####........
   .....................
   .....................
   .....................
   .....................
   .....................
   .....................
   .....................
   .....................
[    0.7s]    open offsets at |v|_inf = 3: 24 of 24, e.g. [(-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -3), (-2, 3), (-1, -3), (-1, 3), (0, -3)]
[    1.2s] CLOSURE labbe D=2 |C|=81 max|v|=4 sweeps=1: = B_4
   .....................
   .....................
   .....................
   .....................
   .....................
   .....................
   ......#########......
   ......#########......
   ......#########......
   ......#########......
   ......####0####......
   ......#########......
   ......#########......
   ......#########......
   ......#########......
   .....................
   .....................
   .....................
   .....................
   .....................
   .....................
[    1.2s]    open offsets at |v|_inf = 5: 40 of 40, e.g. [(-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-4, -5)]
[    1.2s] CLOSURE CALIBRATION PASS
[    1.2s] PART C: band walls (window certificates)
[    1.3s] BAND full2 D=1 m=0 w=4 H=1 h=3 local=4096 bands=64 left_undet=64 right_undet=64 walls=64  e.g. ends ((0, 1), (1, 0))
[    2.1s]    cap 400000 reached at height 5
[    2.2s] BAND checker D=2 m=0 w=6 H=2 h=5 local=2 bands=2 left_undet=0 right_undet=0 walls=0
[    2.2s] BAND checker D=2 m=0 w=6 H=3 h=7 local=2 bands=2 left_undet=0 right_undet=0 walls=0
[    2.2s] BAND checker D=2 m=0 w=6 H=4 h=9 local=2 bands=2 left_undet=0 right_undet=0 walls=0
[    2.2s] BAND checker D=2 m=0 w=6 H=5 h=11 local=2 bands=2 left_undet=0 right_undet=0 walls=0
[    2.2s] BAND checker D=2 m=0 w=6 H=6 h=13 local=2 bands=2 left_undet=0 right_undet=0 walls=0
[    2.2s] BAND checker D=2 m=0 w=6 H=7 h=15 local=2 bands=2 left_undet=0 right_undet=0 walls=0
[    2.2s] BAND checker D=2 m=0 w=6 H=8 h=17 local=2 bands=2 left_undet=0 right_undet=0 walls=0
[    2.2s] BAND checker D=2 m=0 w=6 H=9 h=19 local=2 bands=2 left_undet=0 right_undet=0 walls=0
[    2.2s] BAND checker D=2 m=0 w=6 H=10 h=21 local=2 bands=2 left_undet=0 right_undet=0 walls=0
[    2.2s] BAND ledrappier D=1 m=0 w=4 H=1 h=3 local=64 bands=16 left_undet=16 right_undet=0 walls=0
[    2.2s] BAND ledrappier D=1 m=0 w=4 H=2 h=5 local=256 bands=64 left_undet=64 right_undet=0 walls=0
[    2.2s] BAND ledrappier D=1 m=0 w=4 H=3 h=7 local=1024 bands=256 left_undet=256 right_undet=0 walls=0
[    2.2s] BAND ledrappier D=1 m=0 w=4 H=4 h=9 local=4096 bands=1024 left_undet=1024 right_undet=0 walls=0
[    2.3s] BAND ledrappier D=1 m=0 w=4 H=5 h=11 local=16384 bands=4096 left_undet=4096 right_undet=0 walls=0
[    2.9s] BAND ledrappier D=1 m=0 w=4 H=6 h=13 local=65536 bands=16384 left_undet=16384 right_undet=0 walls=0
[    5.6s] BAND ledrappier D=1 m=0 w=4 H=7 h=15 local=262144 bands=65536 left_undet=65536 right_undet=0 walls=0
[    7.0s]    cap 400000 reached at height 16
[    7.1s] BAND ledrappier D=2 m=0 w=6 H=2 h=5 local=1024 bands=256 left_undet=256 right_undet=0 walls=0
[    7.1s] BAND ledrappier D=2 m=0 w=6 H=3 h=7 local=4096 bands=1024 left_undet=1024 right_undet=0 walls=0
[    7.2s] BAND ledrappier D=2 m=0 w=6 H=4 h=9 local=16384 bands=4096 left_undet=4096 right_undet=0 walls=0
[    7.8s] BAND ledrappier D=2 m=0 w=6 H=5 h=11 local=65536 bands=16384 left_undet=16384 right_undet=0 walls=0
[   10.5s] BAND ledrappier D=2 m=0 w=6 H=6 h=13 local=262144 bands=65536 left_undet=65536 right_undet=0 walls=0
[   12.2s]    cap 400000 reached at height 14
[   12.3s] BAND CALIBRATION PASS (full2 walls at every H; checker/Ledrappier none)
[   12.4s] BAND labbe-e1 D=2 m=0 w=6 H=2 h=5 local=270 bands=195 left_undet=13 right_undet=15 walls=0 | global=266 walls=0
[   12.5s] BAND labbe-e1 D=2 m=0 w=6 H=3 h=7 local=407 bands=304 left_undet=15 right_undet=17 walls=0 | global=374 walls=0
[   12.5s] BAND labbe-e1 D=2 m=0 w=6 H=4 h=9 local=631 bands=479 left_undet=17 right_undet=19 walls=0 | global=502 walls=0
[   12.8s] BAND labbe-e1 D=2 m=0 w=6 H=5 h=11 local=971 bands=744 left_undet=19 right_undet=21 walls=0 | global=652 walls=0
[   13.0s] BAND labbe-e1 D=2 m=0 w=6 H=6 h=13 local=1500 bands=1175 left_undet=21 right_undet=25 walls=0 | global=824 walls=0
[   13.1s] BAND labbe-e2 D=2 m=0 w=6 H=2 h=5 local=291 bands=185 left_undet=17 right_undet=20 walls=0 | global=277 walls=0
[   13.1s] BAND labbe-e2 D=2 m=0 w=6 H=3 h=7 local=390 bands=263 left_undet=19 right_undet=22 walls=0 | global=360 walls=0
[   13.2s] BAND labbe-e2 D=2 m=0 w=6 H=4 h=9 local=542 bands=365 left_undet=21 right_undet=24 walls=0 | global=456 walls=0
[   13.4s] BAND labbe-e2 D=2 m=0 w=6 H=5 h=11 local=726 bands=511 left_undet=25 right_undet=26 walls=0 | global=565 walls=0
[   13.7s] BAND labbe-e2 D=2 m=0 w=6 H=6 h=13 local=1017 bands=723 left_undet=29 right_undet=28 walls=0 | global=688 walls=0
[   13.8s] BAND labbe-e1 D=2 m=1 w=8 H=2 h=5 local=386 bands=195 left_undet=13 right_undet=15 walls=0 | global=349 walls=0
[   13.8s] BAND labbe-e1 D=2 m=1 w=8 H=3 h=7 local=550 bands=298 left_undet=15 right_undet=17 walls=0 | global=469 walls=0
[   13.9s] BAND labbe-e1 D=2 m=1 w=8 H=4 h=9 local=799 bands=452 left_undet=17 right_undet=19 walls=0 | global=609 walls=0
[   14.2s] BAND labbe-e1 D=2 m=1 w=8 H=5 h=11 local=1157 bands=675 left_undet=19 right_undet=21 walls=0 | global=771 walls=0
[   14.4s] BAND labbe-e1 D=2 m=1 w=8 H=6 h=13 local=1680 bands=1027 left_undet=21 right_undet=25 walls=0 | global=955 walls=0
[   14.5s] BAND labbe-e2 D=2 m=1 w=8 H=2 h=5 local=455 bands=185 left_undet=17 right_undet=20 walls=0 | global=389 walls=0
[   14.6s] BAND labbe-e2 D=2 m=1 w=8 H=3 h=7 local=578 bands=261 left_undet=19 right_undet=22 walls=0 | global=484 walls=0
[   14.6s] BAND labbe-e2 D=2 m=1 w=8 H=4 h=9 local=750 bands=357 left_undet=21 right_undet=24 walls=0 | global=592 walls=0
[   14.9s] BAND labbe-e2 D=2 m=1 w=8 H=5 h=11 local=962 bands=476 left_undet=23 right_undet=26 walls=0 | global=713 walls=0
[   15.3s] BAND labbe-e2 D=2 m=1 w=8 H=6 h=13 local=1245 bands=649 left_undet=25 right_undet=28 walls=0 | global=848 walls=0
[   15.3s] WALL6 labbe-e1 H=2 h=5 local=325  band[1,4] bands=195 walls=7  band[2,5] bands=195 walls=7
[   15.3s] WALL6 labbe-e1 H=3 h=7 local=475  band[1,4] bands=299 walls=5  band[2,5] bands=303 walls=5
[   15.3s] WALL6 labbe-e1 H=4 h=9 local=707  band[1,4] bands=464 walls=3  band[2,5] bands=467 walls=3
[   15.3s] WALL6 labbe-e1 H=5 h=11 local=1053  band[1,4] bands=706 walls=1  band[2,5] bands=713 walls=1
[   15.4s] WALL6 labbe-e1 H=6 h=13 local=1589  band[1,4] bands=1099 walls=0  band[2,5] bands=1103 walls=0
[   15.4s] WALL6 labbe-e2 H=2 h=5 local=362  band[1,4] bands=185 walls=1  band[2,5] bands=185 walls=1
[   15.4s] WALL6 labbe-e2 H=3 h=7 local=475  band[1,4] bands=262 walls=0  band[2,5] bands=262 walls=0
[   15.4s] WALL6 labbe-e2 H=4 h=9 local=629  band[1,4] bands=361 walls=0  band[2,5] bands=361 walls=0
[   15.5s] WALL6 labbe-e2 H=5 h=11 local=837  band[1,4] bands=495 walls=0  band[2,5] bands=492 walls=0
[   15.5s] WALL6 labbe-e2 H=6 h=13 local=1127  band[1,4] bands=688 walls=0  band[2,5] bands=684 walls=0
[   15.5s] PART D: contextual closure (window case-split certificates)
[   15.7s] CTX full2 D=1 ring 3: +det 0 +ctx 0; uncertified within ring 3: 24; ball radius 2; shapes [(3, 3)]
[   15.8s] CTX full2 D=1 ring 4: +det 0 +ctx 0; uncertified within ring 4: 56; ball radius 2; shapes [(3, 3)]
[   15.8s] CTX full2 D=1 ring 5: +det 0 +ctx 0; uncertified within ring 5: 96; ball radius 2; shapes [(3, 3)]
[   15.8s] CTX full2 D=1 ring 6: +det 0 +ctx 0; uncertified within ring 6: 144; ball radius 2; shapes [(3, 3)]
[   15.8s] CTX full2 RESULT: certified ball radius 2; 144 offsets within radius 6 uncertified: [(-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5
[   15.8s] CTX checker D=1 ring 3: +det 12 +ctx 0; uncertified within ring 3: 0; ball radius 3; shapes [(4, 4)]
[   15.8s] CTX checker D=1 ring 4: +det 16 +ctx 0; uncertified within ring 4: 0; ball radius 4; shapes [(5, 5)]
[   15.8s] CTX checker D=1 ring 5: +det 20 +ctx 0; uncertified within ring 5: 0; ball radius 5; shapes [(6, 6)]
[   15.8s] CTX checker D=1 ring 6: +det 24 +ctx 0; uncertified within ring 6: 0; ball radius 6; shapes [(7, 7)]
[   15.8s] CTX checker RESULT: certified ball radius 6; 0 offsets within radius 6 uncertified: []
[   15.8s] CTX ledrappier D=1 ring 3: +det 12 +ctx 0; uncertified within ring 3: 0; ball radius 3; shapes [(4, 4)]
[   15.9s] CTX ledrappier D=1 ring 4: +det 16 +ctx 0; uncertified within ring 4: 0; ball radius 4; shapes [(5, 5)]
[   16.2s] CTX ledrappier D=1 ring 5: +det 20 +ctx 0; uncertified within ring 5: 0; ball radius 5; shapes [(6, 6)]
[   17.5s] CTX ledrappier D=1 ring 6: +det 24 +ctx 0; uncertified within ring 6: 0; ball radius 6; shapes [(7, 7)]
[   24.0s] CTX ledrappier D=1 ring 7: +det 28 +ctx 0; uncertified within ring 7: 0; ball radius 7; shapes [(8, 8)]
[   24.0s] CTX ledrappier RESULT: certified ball radius 7; 0 offsets within radius 7 uncertified: []
[   24.7s] CTX ledrappier D=2 ring 5: +det 20 +ctx 0; uncertified within ring 5: 0; ball radius 5; shapes [(6, 6)]
[   26.4s] CTX ledrappier D=2 ring 6: +det 24 +ctx 0; uncertified within ring 6: 0; ball radius 6; shapes [(7, 7)]
[   34.5s] CTX ledrappier D=2 ring 7: +det 28 +ctx 0; uncertified within ring 7: 0; ball radius 7; shapes [(8, 8)]
[   34.5s] CTX ledrappier RESULT: certified ball radius 7; 0 offsets within radius 7 uncertified: []
[   34.5s] CTX CALIBRATION PASS (full2 blocked at 2; checker, Ledrappier reach the stop radius)
[   34.6s] CTX labbe D=1 ring 3: +det 0 +ctx 0; uncertified within ring 3: 24; ball radius 2; shapes [(3, 3)]
[   34.6s] CTX labbe D=1 ring 4: +det 0 +ctx 0; uncertified within ring 4: 56; ball radius 2; shapes [(3, 3)]
[   34.7s] CTX labbe D=1 ring 5: +det 0 +ctx 0; uncertified within ring 5: 96; ball radius 2; shapes [(3, 3)]
[   34.7s] CTX labbe D=1 ring 6: +det 0 +ctx 0; uncertified within ring 6: 144; ball radius 2; shapes [(3, 3)]
[   34.7s] CTX labbe D=1 ring 7: +det 0 +ctx 0; uncertified within ring 7: 200; ball radius 2; shapes [(3, 3)]
[   34.8s] CTX labbe D=1 ring 8: +det 0 +ctx 0; uncertified within ring 8: 264; ball radius 2; shapes [(3, 3)]
[   34.8s] CTX labbe D=1 ring 9: +det 0 +ctx 0; uncertified within ring 9: 336; ball radius 2; shapes [(3, 3)]
[   34.9s] CTX labbe D=1 ring 10: +det 0 +ctx 0; uncertified within ring 10: 416; ball radius 2; shapes [(3, 3)]
[   34.9s] CTX labbe RESULT: certified ball radius 2; 416 offsets within radius 10 uncertified: [(-10, -10), (-10, -9), (-10, -8), (-10, -7), (-10, -6), (-10, -5), (-10, -4), (-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 5), (-10, 6), (-10, 7), (-10, 8), (-10, 9), (-10, 10), (-9, -10), 
[   36.1s] CTX labbe D=2 ring 5: +det 10 +ctx 3; uncertified within ring 5: 14; ball radius 4; shapes [(3, 6), (5, 5), (6, 4)]  e.g. (-5, -2) via ((5, 5), (5, 5), -4, -3, -5, -3)
[   36.7s] CTX labbe D=2 ring 6: +det 0 +ctx 0; uncertified within ring 6: 62; ball radius 4; shapes [(3, 6), (5, 5), (6, 4)]
[   37.3s] CTX labbe D=2 ring 7: +det 0 +ctx 0; uncertified within ring 7: 118; ball radius 4; shapes [(3, 6), (5, 5), (6, 4)]
[   37.9s] CTX labbe D=2 ring 8: +det 0 +ctx 0; uncertified within ring 8: 182; ball radius 4; shapes [(3, 6), (5, 5), (6, 4)]
[   38.3s] CTX labbe D=2 ring 9: +det 0 +ctx 0; uncertified within ring 9: 254; ball radius 4; shapes [(3, 6), (5, 5), (6, 4)]
[   38.7s] CTX labbe D=2 ring 10: +det 0 +ctx 0; uncertified within ring 10: 334; ball radius 4; shapes [(3, 6), (5, 5), (6, 4)]
[   39.2s] CTX labbe D=2 ring 11: +det 0 +ctx 0; uncertified within ring 11: 422; ball radius 4; shapes [(3, 6), (5, 5), (6, 4)]
[   40.2s] CTX labbe D=2 ring 12: +det 0 +ctx 0; uncertified within ring 12: 518; ball radius 4; shapes [(3, 6), (5, 5), (6, 4)]
[   41.3s] CTX labbe D=2 ring 13: +det 0 +ctx 0; uncertified within ring 13: 622; ball radius 4; shapes [(3, 6), (5, 5), (6, 4)]
[   42.7s] CTX labbe D=2 ring 14: +det 0 +ctx 0; uncertified within ring 14: 734; ball radius 4; shapes [(3, 6), (5, 5), (6, 4)]
[   44.2s] CTX labbe D=2 ring 15: +det 0 +ctx 0; uncertified within ring 15: 854; ball radius 4; shapes [(3, 6), (5, 5), (6, 4)]
[   45.8s] CTX labbe D=2 ring 16: +det 0 +ctx 0; uncertified within ring 16: 982; ball radius 4; shapes [(3, 6), (5, 5), (6, 4)]
[   47.7s] CTX labbe D=2 ring 17: +det 0 +ctx 0; uncertified within ring 17: 1118; ball radius 4; shapes [(3, 6), (5, 5), (6, 4)]
[   49.0s] CTX labbe D=2 ring 18: +det 0 +ctx 0; uncertified within ring 18: 1262; ball radius 4; shapes [(3, 6), (5, 5), (6, 4)]
[   50.0s] CTX labbe D=2 ring 19: +det 0 +ctx 0; uncertified within ring 19: 1414; ball radius 4; shapes [(3, 6), (5, 5), (6, 4)]
[   51.0s] CTX labbe D=2 ring 20: +det 0 +ctx 0; uncertified within ring 20: 1574; ball radius 4; shapes [(3, 6), (5, 5), (6, 4)]
[   51.0s] CTX labbe RESULT: certified ball radius 4; 1574 offsets within radius 20 uncertified: [(-20, -20), (-20, -19), (-20, -18), (-20, -17), (-20, -16), (-20, -15), (-20, -14), (-20, -13), (-20, -12), (-20, -11), (-20, -10), (-20, -9), (-20, -8), (-20, -7), (-20, -6), (-20, -5), (-20, -4), (-20, -3), (-20, -2), (-20, -1), (
[   51.0s] DONE
exit=0
```

## 8. Script `j2probe.py` (verbatim)

```python
#!/usr/bin/env python3
"""j2probe.py -- exact bounded probes of scale-D quantum rigidity of Z^2 SFTs (lane bh-g2-labbe, 2026-09-18).

Part A  box languages: Labbe's Omega_U from omega^k windows (as in recog.py); calibrations: checkerboard (rigid),
        Ledrappier (rigid: triangle-permutive), full 2-shift (not rigid: walls).
Part B  two-sided determinism closure C_D (node determinism-closure-certifies-quantum-rigidity): the offsets v whose
        commutation [P_0, P_v] = 0 is certified in the scale-D presentation by determinism alone.
Part C  band walls.  Window K = [0, w) x [0, 2H], w = 2D+2+2m; ends L = (m, H), R = (m+2D+1, H); band = columns
        m+1..m+2D.  Two patterns on K, every s x s box of which is legal (s = 2D+1), that agree on the band and differ
        at L and at R give a 2-dim representation of the window algebra C_D(K) (relations supported in K) with
        [P_L^a, P_R^b] != 0.  So no certificate of that commutation, of ANY degree, uses only relations in K.
        Done for v along e_1 and (transposed language) along e_2.
Single-threaded, stdlib only, exact, no randomness.  Usage: python3 j2probe.py [--smoke]
"""
import sys, time, itertools
from collections import defaultdict
T0 = time.time()
SMOKE = '--smoke' in sys.argv
BUDGET = 50 if SMOKE else 2100
def el(): return time.time() - T0
def log(*a): print('[%7.1fs]' % el(), *a, flush=True)

# ---------------------------------------------------------------- Labbe data (verbatim from recog.py / labbe_lang.py)
tilesU = ['FOJO','FOHL','JMFP','DMFK','HPJP','HPHN','HKFP','HKDP','BOIO','GLEO','GLCL','ALIO',
          'EPGP','EPIP','IPGK','IPIK','IKBM','IKAK','CNIP']
alpha = {0: [[11]], 1: [[8]], 2: [[13]], 3: [[9]], 4: [[17]], 5: [[16]], 6: [[14]], 7: [[15]], 8: [[11, 1]], 9: [[8, 0]], 10: [[18, 5]], 11: [[12, 6]], 12: [[13, 7]], 13: [[13, 4]], 14: [[10, 1]], 15: [[9, 1]], 16: [[17, 3]], 17: [[16, 3]], 18: [[14, 6]], 19: [[15, 7]], 20: [[14, 2]]}
beta = {0: [[4]], 1: [[5]], 2: [[7], [0]], 3: [[4], [1]], 4: [[5], [1]], 5: [[6], [1]], 6: [[7], [1]], 7: [[2], [3]], 8: [[16]], 9: [[17]], 10: [[18]], 11: [[20]], 12: [[18], [8]], 13: [[19], [8]], 14: [[20], [9]], 15: [[11], [15]], 16: [[12], [15]], 17: [[10], [14]], 18: [[13], [15]]}
gamma = {0: [[0]], 1: [[1]], 2: [[2]], 3: [[7]], 4: [[3]], 5: [[4]], 6: [[6]], 7: [[5]], 8: [[10]], 9: [[8]], 10: [[9]], 11: [[11]], 12: [[13]], 13: [[12]], 14: [[16]], 15: [[15]], 16: [[17]], 17: [[18]], 18: [[14]]}
ci = {c: i for i, c in enumerate('RTLB')}
RT = [t[ci['R']] for t in tilesU]; TP = [t[ci['T']] for t in tilesU]
LF = [t[ci['L']] for t in tilesU]; BT = [t[ci['B']] for t in tilesU]

def apply(s, M):  # M: list of columns, each bottom -> top
    out = []
    for col in M:
        imgs = [s[a] for a in col]
        w = len(imgs[0])
        if any(len(im) != w for im in imgs):
            raise ValueError('width')
        for j in range(w):
            c = []
            for im in imgs:
                c.extend(im[j])
            out.append(c)
    if any(len(c) != len(out[0]) for c in out):
        raise ValueError('height')
    return out

def omega(M): return apply(alpha, apply(beta, apply(gamma, M)))
def omega_pow(M, k):
    for _ in range(k): M = omega(M)
    return M
def valid(M):
    W, H = len(M), len(M[0])
    for x in range(W):
        for y in range(H):
            t = M[x][y]
            if x + 1 < W and RT[t] != LF[M[x + 1][y]]: return False
            if y + 1 < H and TP[t] != BT[M[x][y + 1]]: return False
    return True

big = omega_pow([[0]], 7)
L22 = set()
def add22(I, S):
    for x in range(len(I) - 1):
        for y in range(len(I[0]) - 1):
            S.add((I[x][y], I[x][y + 1], I[x + 1][y], I[x + 1][y + 1]))
add22(big, L22)
while True:
    new = set(L22)
    for q in L22: add22(omega([[q[0], q[1]], [q[2], q[3]]]), new)
    if new == L22: break
    L22 = new
Q2 = sorted(L22)
minside = {}
for k in range(1, 9):
    imgs = [omega_pow([[a]], k) for a in range(19)]
    minside[k] = min(min(len(I) for I in imgs), min(len(I[0]) for I in imgs))
IMG = {}
def labbe_windows(w, h):
    """All globally legal w x h patterns of Omega_U, column form (tuple of w columns, each bottom->top)."""
    need = max(w, h) - 1
    k = next(k for k in range(1, 9) if minside[k] >= need)
    if k not in IMG:
        IMG[k] = [omega_pow([[q[0], q[1]], [q[2], q[3]]], k) for q in Q2]
    S = set()
    for Y in IMG[k]:
        W, H = len(Y), len(Y[0])
        for x in range(W - w + 1):
            cols = Y[x:x + w]
            for y in range(H - h + 1):
                S.add(tuple(tuple(c[y:y + h]) for c in cols))
    return S

# ---------------------------------------------------------------- calibration languages (column form)
def lang_checker(s): return set(tuple(tuple((i + j + ph) % 2 for j in range(s)) for i in range(s)) for ph in (0, 1))
def lang_ledrappier(s):
    """x(i,j+1) = x(i,j) + x(i+1,j) mod 2; box patterns = free bottom row + free right column (group shift, all extend)."""
    S = set()
    for bits in itertools.product((0, 1), repeat=2 * s - 1):
        g = [[0] * s for _ in range(s)]
        for i in range(s): g[i][0] = bits[i]
        for j in range(1, s):
            g[s - 1][j] = bits[s - 1 + j]
            for i in range(s - 1): g[i][j] = g[i][j - 1] ^ g[i + 1][j - 1]
        S.add(tuple(tuple(g[i]) for i in range(s)))
    return S
def lang_full(s): return set(tuple(tuple(b[i * s:(i + 1) * s]) for i in range(s)) for b in itertools.product((0, 1), repeat=s * s))
def transpose(P):
    w, h = len(P), len(P[0])
    return tuple(tuple(P[i][j] for i in range(w)) for j in range(h))

# ---------------------------------------------------------------- Part B: determinism closure
def closure(L, s, Rmax):
    D = (s - 1) // 2
    Lst = list(L)
    C = set((a, b) for a in range(-2 * D, 2 * D + 1) for b in range(-2 * D, 2 * D + 1))
    pos = [(i, j) for i in range(s) for j in range(s)]
    cache = {}
    def is_rule(q, Fq):
        key = (q, Fq)
        r = cache.get(key)
        if r is not None: return r
        Fl = sorted(Fq); seen = {}; ok = True
        for P in Lst:
            k = tuple(P[i][j] for (i, j) in Fl); c = P[q[0]][q[1]]
            o = seen.get(k)
            if o is None: seen[k] = c
            elif o != c: ok = False; break
        cache[key] = ok
        return ok
    sweeps = 0
    changed = True
    while changed:
        changed = False; sweeps += 1
        for a in range(-Rmax, Rmax + 1):
            for b in range(-Rmax, Rmax + 1):
                v = (a, b)
                if v in C: continue
                hit = False
                for q in pos:
                    for sg in (1, -1):   # (w): v + f in C ; (z): v - f in C ; f = p - q
                        Fq = frozenset(p for p in pos if p != q and
                                       (a + sg * (p[0] - q[0]), b + sg * (p[1] - q[1])) in C)
                        if is_rule(q, Fq): hit = True; break
                    if hit: break
                if hit:
                    C.add(v); C.add((-a, -b)); changed = True
    return C, sweeps

def show(C, Rmax):
    for b in range(Rmax, -Rmax - 1, -1):
        print('   ' + ''.join('0' if (a, b) == (0, 0) else ('#' if (a, b) in C else '.') for a in range(-Rmax, Rmax + 1)))

# ---------------------------------------------------------------- Part C: locally legal windows and band walls
def to_rows(P): return transpose(P)
def local_levels(Lbox, s, w, hmax, cap, tlimit):
    """Yield (h, list of row-form w x h patterns whose s x s boxes are all legal), h = s..hmax."""
    colext = defaultdict(set)
    for P in Lbox: colext[P[:-1]].add(P[-1])
    strips = set(Lbox); width = s
    while width < w:
        new = set()
        for P in strips:
            for c in colext.get(P[-(s - 1):], ()): new.add(P + (c,))
        strips = new; width += 1
    level = [to_rows(P) for P in strips]
    up = defaultdict(set)
    for P in Lbox:
        B = to_rows(P); up[B[:-1]].add(B[-1])
    h = s
    yield h, level
    while h < hmax:
        if el() > tlimit: log('   time limit at height', h); return
        nxt = []
        for P in level:
            top = P[-(s - 1):]
            partial = [()]
            for c in range(w - s + 1):
                cands = up.get(tuple(r[c:c + s] for r in top))
                if not cands: partial = []; break
                npart = []
                for pr in partial:
                    if c == 0: npart.extend(cands)
                    else:
                        for t in cands:
                            if t[:s - 1] == pr[c:c + s - 1]: npart.append(pr + (t[-1],))
                partial = npart
                if not partial: break
            for r in partial: nxt.append(P + (r,))
            if len(nxt) > cap: log('   cap %d reached at height %d' % (cap, h + 1)); return
        level = nxt; h += 1
        yield h, level

def band_walls(pats, s, m, H):
    D = (s - 1) // 2; Lc, Rc = m, m + 2 * D + 1
    groups = defaultdict(set)
    for P in pats: groups[tuple(row[m + 1:m + 2 * D + 1] for row in P)].add((P[H][Lc], P[H][Rc]))
    lund = rund = walls = 0; ex = None
    for key, S in groups.items():
        if len(set(a for a, b in S)) > 1: lund += 1
        if len(set(b for a, b in S)) > 1: rund += 1
        Sl = list(S); f = None
        for i in range(len(Sl)):
            for j in range(i + 1, len(Sl)):
                if Sl[i][0] != Sl[j][0] and Sl[i][1] != Sl[j][1]: f = (Sl[i], Sl[j]); break
            if f: break
        if f:
            walls += 1
            if ex is None: ex = f
    return len(groups), lund, rund, walls, ex

def band_run(name, Lbox, s, m, Hmax, cap, glob=None):
    """glob(w, h) -> set of globally legal row-form w x h patterns (or None)."""
    D = (s - 1) // 2; w = 2 * D + 2 + 2 * m
    res = {}
    for h, level in local_levels(Lbox, s, w, 2 * Hmax + 1, cap, BUDGET):
        if h % 2 == 0 or h < s: continue
        H = (h - 1) // 2
        nb, lu, ru, wl, ex = band_walls(level, s, m, H)
        line = 'BAND %s D=%d m=%d w=%d H=%d h=%d local=%d bands=%d left_undet=%d right_undet=%d walls=%d' % (
            name, D, m, w, H, h, len(level), nb, lu, ru, wl)
        if glob is not None:
            G = glob(w, h)
            gnb, glu, gru, gwl, gex = band_walls(G, s, m, H)
            line += ' | global=%d walls=%d' % (len(G), gwl)
        log(line + ('  e.g. ends %s' % (ex,) if ex else ''))
        res[H] = wl
    return res

# ---------------------------------------------------------------- Part D: contextual closure
# Sound criterion (proof in the artifact): let B_R ⊆ C (certified), W = R+1, so every W x W window T is pairwise
# commuting.  For T ∋ 0, T' ∋ v, S = T ∩ T', e_tau = prod_S P^tau commutes with P_0 and P_v, sum_tau e_tau = 1, and
# e_tau P_0^a = [a = a0] e_tau whenever all locally legal T-patterns extending tau have the letter a0 at 0 (expand over
# T; locally illegal terms contain an illegal box).  So if no tau is extendable in both T and T' with BOTH ends
# undetermined, [P_0^a, P_v^b] = 0 in the scale-D presentation.  Rings |v|_inf = R+1 are certified one at a time.
def square_patterns(Lbox, s, W, cap):
    if W == s: return [to_rows(P) for P in Lbox]
    last = None
    for h, level in local_levels(Lbox, s, W, W, cap, BUDGET): last = (h, level)
    if last is None or last[0] != W: return None
    return last[1]

def rule_tester(L, s):
    """det_ok(v, C): v is added by one (w)/(z) determinism step of Part B, using the current certified set C."""
    Lst = list(L); pos = [(i, j) for i in range(s) for j in range(s)]; cache = {}
    def is_rule(q, Fq):
        key = (q, Fq); r = cache.get(key)
        if r is not None: return r
        Fl = sorted(Fq); seen = {}; ok = True
        for P in Lst:
            k = tuple(P[i][j] for (i, j) in Fl); c = P[q[0]][q[1]]
            o = seen.get(k)
            if o is None: seen[k] = c
            elif o != c: ok = False; break
        cache[key] = ok
        return ok
    def det_ok(v, C):
        for q in pos:
            for sg in (1, -1):
                Fq = frozenset(p for p in pos if p != q and (v[0] + sg * (p[0] - q[0]), v[1] + sg * (p[1] - q[1])) in C)
                if is_rule(q, Fq): return True
        return False
    return det_ok

# Legality used by certificates: a pattern on a pairwise-commuting rectangle T has e_pi = 0 unless, for EVERY s x s box
# B meeting T, pi restricted to T ∩ B extends to a legal B-pattern (expand over B \ T, which commutes with T ∩ B).
PROJ = {}
def proj_sets(tag, Lbox, s):
    key = (tag, s)
    if key not in PROJ:
        d = {}
        for ix0 in range(s):
            for iw in range(1, s - ix0 + 1):
                for iy0 in range(s):
                    for ih in range(1, s - iy0 + 1):
                        d[(ix0, iy0, iw, ih)] = set(tuple(tuple(P[ix0 + i][iy0:iy0 + ih]) for i in range(iw)) for P in Lbox)
        PROJ[key] = d
    return PROJ[key]

COLS = {}
def columns(tag, Lbox, s, b, cap):
    key = (tag, s, b)
    if key in COLS: return COLS[key]
    pj = proj_sets(tag, Lbox, s)
    cp = {}
    for iy0 in range(s):
        for ih in range(1, s - iy0 + 1):
            S = None
            for ix in range(s):
                T = set(c[0] for c in pj[(ix, iy0, 1, ih)])
                S = T if S is None else (S & T)
            cp[(iy0, ih)] = S
    letters = sorted(set(x for P in Lbox for col in P for x in col))
    cols = [()]
    for j in range(b):
        bys = [j - (s - 1)] if j < b - 1 else list(range(b - s, b))
        new = []
        for c in cols:
            for x in letters:
                cc = c + (x,); ok = True
                for by in bys:
                    lo = max(0, by)
                    if cc[lo:j + 1] not in cp[(lo - by, j - lo + 1)]: ok = False; break
                if ok: new.append(cc)
        cols = new
        if len(cols) > cap: cols = None; break
    COLS[key] = cols
    return cols

PATCACHE = {}
METHOD = {}
COMPAT = {}
def rect_patterns(tag, Lbox, s, a, b, cap):
    """Row-form a x b patterns satisfying partial-box legality for every box meeting the rectangle (None if over cap/time)."""
    key = (tag, s, a, b)
    if key in PATCACHE: return PATCACHE[key]
    pj = proj_sets(tag, Lbox, s)
    cols = columns(tag, Lbox, s, b, cap)
    res = None
    def boxes_ok(Q, c, bxs):
        """All boxes with lower-left column bx in bxs, every row placement: restriction of Q (columns 0..c) is legal."""
        for bx in bxs:
            lo = max(0, bx); iw = c - lo + 1; ix0 = lo - bx
            for by in range(-(s - 1), b):
                ylo = max(0, by); yhi = min(b - 1, by + s - 1)
                if tuple(Q[x][ylo:yhi + 1] for x in range(lo, c + 1)) not in pj[(ix0, ylo - by, iw, yhi - ylo + 1)]:
                    return False
        return True
    if cols is not None:
        ck = (tag, s, b)
        if ck not in COMPAT:
            def pair_ok(c1, c2):   # necessary: every box position ix0, ix0+1 of an adjacent pair, every row placement
                for ix0 in range(s - 1):
                    for by in range(-(s - 1), b):
                        ylo = max(0, by); yhi = min(b - 1, by + s - 1)
                        if (c1[ylo:yhi + 1], c2[ylo:yhi + 1]) not in pj[(ix0, ylo - by, 2, yhi - ylo + 1)]: return False
                return True
            COMPAT[ck] = {c1: [c2 for c2 in cols if pair_ok(c1, c2)] for c1 in cols}
        compat = COMPAT[ck]
        first_bx = [1 - s] if a > 1 else list(range(1 - s, 1))
        pats = [(c,) for c in cols if boxes_ok((c,), 0, first_bx)]
        ok_all = True
        for c in range(1, a):
            bxs = [c - (s - 1)] if c < a - 1 else list(range(a - s, a))
            new = []
            for P in pats:
                for col in compat[P[-1]]:
                    Q = P + (col,)
                    if boxes_ok(Q, c, bxs): new.append(Q)
            pats = new
            if len(pats) > cap or el() > BUDGET: ok_all = False; break
        if ok_all: res = [to_rows(P) for P in pats]
    PATCACHE[key] = res
    return res

def contextual_closure(name, Lbox, s, Rstop, cap, maxtry, Wmax):
    """Certified set C grown ring by ring; contexts are overlaps of pairwise-commuting rectangles (all offsets in C)."""
    D = (s - 1) // 2
    C = set((a, b) for a in range(-2 * D, 2 * D + 1) for b in range(-2 * D, 2 * D + 1))
    det_ok = rule_tester(Lbox, s)
    ucache = {}
    def comm_rect(a, b): return all((dx, dy) in C for dx in range(-(a - 1), a) for dy in range(-(b - 1), b))
    def shapes():
        full = set()
        for a in range(1, Wmax + 1):   # every width, with its maximal commuting height
            if not comm_rect(a, 1): break
            b = 1
            while b + 1 <= Wmax and comm_rect(a, b + 1): b += 1
            full.add((a, b))
        pareto = [x for x in full if not any(y != x and y[0] >= x[0] and y[1] >= x[1] for y in full)]
        return sorted(pareto)
    def umap(shape, p, rect):
        key = (shape, p, rect); d = ucache.get(key)
        if d is None:
            pats = rect_patterns(name, Lbox, s, shape[0], shape[1], cap)
            if pats is None: ucache[key] = False; return False
            rx0, ry0, rw, rh = rect; d = {}
            for P in pats:
                t = tuple(P[y][rx0:rx0 + rw] for y in range(ry0, ry0 + rh)); val = P[p[1]][p[0]]
                o = d.get(t)
                if o is None: d[t] = val
                elif o != val: d[t] = -1
            ucache[key] = d
        return d
    def top_pairs(n0, n1, c, K):   # 1-dim placements: [x0, x0+n0) ∋ 0 and [x1, x1+n1) ∋ c, by overlap
        out = []
        for x0 in range(-(n0 - 1), 1):
            for x1 in range(c - (n1 - 1), c + 1):
                o = min(x0 + n0, x1 + n1) - max(x0, x1)
                if o > 0: out.append((o, x0, x1))
        out.sort(key=lambda t: (-t[0], t[1], t[2]))
        return out[:K]
    def certify(v, shp):
        cand = []
        for A in shp:
            for B in shp:
                for ox, x0, x1 in top_pairs(A[0], B[0], v[0], 6):
                    for oy, y0, y1 in top_pairs(A[1], B[1], v[1], 6):
                        cand.append((ox * oy, A, B, x0, y0, x1, y1, ox, oy))
        cand.sort(key=lambda c: (-c[0],) + tuple(c[1:]))
        for area, A, B, x0, y0, x1, y1, ox, oy in cand[:maxtry]:
            sx, sy = max(x0, x1), max(y0, y1)
            d0 = umap(A, (-x0, -y0), (sx - x0, sy - y0, ox, oy))
            d1 = umap(B, (v[0] - x1, v[1] - y1), (sx - x1, sy - y1, ox, oy))
            if d0 is False or d1 is False: continue
            if not any(a == -1 and d1.get(t) == -1 for t, a in d0.items()):
                return (A, B, x0, y0, x1, y1)
        return None
    pending = []
    for r in range(2 * D + 1, Rstop + 1):
        if el() > BUDGET: log('CTX %s: time budget reached before ring %d' % (name, r)); break
        pending += [(a, b) for a in range(-r, r + 1) for b in range(-r, r + 1) if max(abs(a), abs(b)) == r and (a, b) not in C]
        ndet = nctx = 0; ex = None
        progress = True
        while pending and progress and el() < BUDGET:
            progress = False; shp = shapes(); rest = []
            for v in pending:
                if v in C: continue
                if det_ok(v, C): C.add(v); C.add((-v[0], -v[1])); ndet += 1; progress = True; METHOD[v] = "det"; continue
                w = certify(v, shp)
                if w:
                    C.add(v); C.add((-v[0], -v[1])); nctx += 1; progress = True
                    METHOD[v] = ("ctx",) + tuple(w)
                    if ex is None: ex = (v, w)
                else: rest.append(v)
            pending = [v for v in rest if v not in C]
        ball = next(q for q in range(0, r + 2) if any(max(abs(a), abs(b)) == q + 1 and (a, b) not in C
                                                          for a in range(-q - 1, q + 2) for b in range(-q - 1, q + 2)))
        log('CTX %s D=%d ring %d: +det %d +ctx %d; uncertified within ring %d: %d; ball radius %d; shapes %s%s' % (
            name, D, r, ndet, nctx, r, len(pending), ball, shapes(), ('  e.g. %s via %s' % ex) if ex else ''))
    unc = sorted(pending)
    ball = next(q for q in range(0, Rstop + 2) if any(max(abs(a), abs(b)) == q + 1 and (a, b) not in C
                                                      for a in range(-q - 1, q + 2) for b in range(-q - 1, q + 2)))
    log('CTX %s RESULT: certified ball radius %d; %d offsets within radius %d uncertified: %s' % (
        name, ball, len(unc), Rstop, unc[:60]))
    return ball, unc

# ---------------------------------------------------------------- run
def main():
    Rm = 4 if SMOKE else 10
    log('PART A: languages')
    LAB3, LAB5 = labbe_windows(3, 3), labbe_windows(5, 5)
    log('Labbe |L_3x3| = %d  |L_5x5| = %d  |L_2x2| = %d' % (len(LAB3), len(LAB5), len(Q2)))
    assert len(LAB3) == 94 and len(LAB5) == 229, 'Labbe language counts differ from recog.py'
    assert all(valid([list(c) for c in P]) for P in LAB5)
    CH3, CH5, LE3, LE5, FU3 = lang_checker(3), lang_checker(5), lang_ledrappier(3), lang_ledrappier(5), lang_full(3)
    log('checker %d/%d  Ledrappier %d/%d  full %d' % (len(CH3), len(CH5), len(LE3), len(LE5), len(FU3)))

    log('PART B: determinism closure, region |v|_inf <= %d' % Rm)
    full_region = (2 * Rm + 1) ** 2
    calib = True
    for name, L, s, expect in [('checker', CH3, 3, 'fill'), ('ledrappier', LE3, 3, 'fill'), ('ledrappier', LE5, 5, 'fill'),
                               ('full2', FU3, 3, 'ball'), ('labbe', LAB3, 3, None), ('labbe', LAB5, 5, None)]:
        C, sw = closure(L, s, Rm); D = (s - 1) // 2
        rad = max(max(abs(a), abs(b)) for a, b in C)
        st = 'fills region' if len(C) == full_region else ('= B_%d' % (2 * D) if len(C) == (4 * D + 1) ** 2 else 'bounded')
        ok = (expect == 'fill' and len(C) == full_region) or (expect == 'ball' and len(C) == (4 * D + 1) ** 2) or expect is None
        calib = calib and ok
        log('CLOSURE %s D=%d |C|=%d max|v|=%d sweeps=%d: %s%s' % (name, D, len(C), rad, sw, st,
            '' if expect is None else ('  [calibration %s]' % ('PASS' if ok else 'FAIL'))))
        if name == 'labbe':
            show(C, Rm)
            ring = sorted(v for v in itertools.product(range(-Rm, Rm + 1), repeat=2)
                          if max(abs(v[0]), abs(v[1])) == 2 * D + 1 and v not in C)
            log('   open offsets at |v|_inf = %d: %d of %d, e.g. %s' % (2 * D + 1, len(ring), 8 * (2 * D + 1), ring[:12]))
    log('CLOSURE CALIBRATION %s' % ('PASS' if calib else 'FAIL'))
    if not calib: log('ABORT: calibration failed'); return

    log('PART C: band walls (window certificates)')
    Hm = 3 if SMOKE else 10
    cap = 20000 if SMOKE else 400000
    c1 = band_run('full2', FU3, 3, 0, Hm, cap)
    c2 = band_run('checker', CH5, 5, 0, Hm, cap)
    c3 = band_run('ledrappier', LE3, 3, 0, Hm, cap)
    c4 = band_run('ledrappier', LE5, 5, 0, Hm, cap)
    bc = all(v > 0 for v in c1.values()) and len(c1) > 0 and all(v == 0 for d in (c2, c3, c4) for v in d.values())
    log('BAND CALIBRATION %s (full2 walls at every H; checker/Ledrappier none)' % ('PASS' if bc else 'FAIL'))
    if not bc: log('ABORT: band calibration failed'); return
    gx = lambda w, h: set(to_rows(P) for P in labbe_windows(w, h))
    gy = lambda w, h: set(labbe_windows(h, w))   # original window h x w (columns); its column form = transposed row form
    LAB5T = set(transpose(P) for P in LAB5)
    for m in (0,) if SMOKE else (0, 1):
        band_run('labbe-e1', LAB5, 5, m, 3 if SMOKE else 6, cap, gx)
        band_run('labbe-e2', LAB5T, 5, m, 3 if SMOKE else 6, cap, gy)

    # displacement (6,0): window [0,6] x [0,2H], ends (0,H), (6,H); separating bands of 4 agreeing columns [1,4] or [2,5]
    def walls6(name, Lbox, Hmax):
        for h, level in local_levels(Lbox, 5, 7, 2 * Hmax + 1, cap, BUDGET):
            if h % 2 == 0: continue
            H = (h - 1) // 2; out = []
            for lo in (1, 2):
                g = defaultdict(set)
                for P in level: g[tuple(row[lo:lo + 4] for row in P)].add((P[H][0], P[H][6]))
                wl = sum(1 for S in g.values() if any(p[0] != q[0] and p[1] != q[1] for p in S for q in S))
                out.append('band[%d,%d] bands=%d walls=%d' % (lo, lo + 3, len(g), wl))
            log('WALL6 %s H=%d h=%d local=%d  %s' % (name, H, h, len(level), '  '.join(out)))
    walls6('labbe-e1', LAB5, 3 if SMOKE else 6)
    walls6('labbe-e2', LAB5T, 3 if SMOKE else 6)
    log('PART D: contextual closure (window case-split certificates)')
    mt = 40
    r1 = contextual_closure('full2', FU3, 3, 6, cap, mt, 6)[0]
    r2 = contextual_closure('checker', CH3, 3, 6, cap, mt, 8)[0]
    rs = 5 if SMOKE else 7
    r3 = contextual_closure('ledrappier', LE3, 3, rs, cap, mt, 8)[0]
    r4 = contextual_closure('ledrappier', LE5, 5, rs, cap, mt, 8)[0]
    dc = r1 == 2 and r2 == 6 and r3 == rs and r4 == rs
    log('CTX CALIBRATION %s (full2 blocked at 2; checker, Ledrappier reach the stop radius)' % ('PASS' if dc else 'FAIL'))
    if not dc: log('ABORT: contextual calibration failed'); return
    contextual_closure('labbe', LAB3, 3, 6 if SMOKE else 10, cap, mt, 8 if SMOKE else 12)
    contextual_closure('labbe', LAB5, 5, 7 if SMOKE else 20, cap, mt, 9 if SMOKE else 14)
    log('DONE')

if "--ring5" in sys.argv:
    LAB5 = labbe_windows(5, 5)
    contextual_closure("labbe", LAB5, 5, 5, 400000, 40, 9)
    for v in sorted(METHOD): print("METHOD", v, METHOD[v])
else:
    main()
```
