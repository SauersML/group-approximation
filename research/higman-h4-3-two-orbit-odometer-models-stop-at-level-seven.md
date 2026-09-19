---
rg: 2
id: higman-h4-3-two-orbit-odometer-models-stop-at-level-seven
kind: claim
title: Homomorphisms from H4(3)/<<[a,c]^2>> to the Sylow 2-subgroup W_k of S_(2^k) that send a to the two-orbit odometer x -> x + 2 exist exactly for k <= 7, so this family of tree models dies at level 8 after reaching ord(a) = 64
distinct_from:
  higman-h4-3-has-no-odometer-models-beyond-level-five: that excludes a acting as one 2^k-cycle (k >= 6); this treats a with two 2^(k-1)-cycles that swap no level-1 vertex, a family that survives two levels longer and reaches ord(a) = 64 instead of 32.
  higman-power-pair-collapse-is-base-uniform-up-to-torsion: that asks whether H4(3)/<<[a,c]^2>> has generators of infinite order; this does not settle it and only kills one family of candidate tree models with a of infinite order.
  higman-order-2e-models-need-exponential-rank: that bounds degree against ord(a) = 2^e in any finite quotient; this gives an explicit transitive 2-group quotient of degree 128 with ord(a) = 64 and shows it does not extend along the two-orbit odometer.
artifacts:
  - experiments/higman-jodometer-lifting-2026-09-19/jlift.c
  - experiments/higman-jodometer-lifting-2026-09-19/j1-output.txt
  - experiments/higman-jodometer-lifting-2026-09-19/xcheck-output.txt
  - experiments/higman-jodometer-lifting-2026-09-19/model-j1-level7.g
  - experiments/higman-jodometer-lifting-2026-09-19/verify.g
  - experiments/higman-jodometer-lifting-2026-09-19/verify-j1-level7-output.txt
---

**ESTABLISHED** (proposed, computed) by `higman-h4-3-two-orbit-odometer-models-stop-at-level-seven-proof`.

**Setting.** `H4(3) = < a, b, c, d | b^a = b^3, c^b = c^3, d^c = d^3, a^d = a^3 >` and
`R = [a,c]^2`, with the conventions of `higman-h4-3-has-no-odometer-models-beyond-level-five`. The
level-`k` vertices of the binary tree are `Z/2^k`, and `x mod 2^r` is the ancestor at level `r`.
For `J >= 0` the *`J`-odometer* is `x -> x + 2^J`. A *`J`-odometer model of level `k`* is a
homomorphism `H4(3)/<<R>> -> W_k` that sends `a` to the `J`-odometer. For `J = 1`, `a` has two
cycles of length `2^(k-1)` (the even and the odd vertices). Models are counted up to conjugation by
the centralizer `C_k` of `a` in `W_k`, which has order `2^(2k-1)`.

**Statement.**
1. **The family dies at level 8.** There is no `1`-odometer model of level `k >= 8`. The class
   counts at levels 1 to 8 are `8, 80, 332, 1908, 24336, 318432, 11776, 0`.
2. **Level 7 is reached with `ord(a) = 64`.** `model-j1-level7.g` is a level-7 model. GAP checks
   that all five relators hold, that the images are tree automorphisms, and that `a` has two
   64-cycles. The orders of `(a, b, c, d)` are `(64, 4, 4, 16)`. The image is a transitive 2-group
   of degree 128 and order `2^29`.
3. **The shape of the survivors.**
   - At level 7 every model moves some level-1 vertex. The swap patterns `(a,b,c,d)` are `0100`,
     `0110`, `0001` and `0111`.
   - Every level-7 model has `ord(d) = 16`, and every level-6 model has `ord(d) = 8`. So
     `ord(a) <= 4 ord(d)` holds with equality at the top levels.
   - The maximum log2 orders of `(a,b,c,d)` are `(4,3,4,4)`, `(5,3,4,3)` and `(6,3,4,4)` at levels
     5, 6 and 7.
4. **Order ladder.** In every finite 2-group quotient, `ord(a) <= 4 ord(d)`, since `ord(a)` divides
   `3^ord(d) - 1` and `v_2(3^(2^s) - 1) = s + 2`.

**What it kills.**
- The second tree family proposed in `higman-h4-3-has-no-odometer-models-beyond-level-five`. No
  action of `H4(3)/<<R>>` on `T_2` has `a` acting as `x -> x + 2` on every level. Without `R` the
  question is open: that run did not finish in the time limit.
- The best ord(a) per family grows: 32 for `J = 0` (level 5) and 64 for `J = 1` (level 7). This is
  consistent with a wall at level `5 + 2J`, but no proof of that is claimed.
- `J = 2` is not decided. The first level-6 node already has `2^28` linear lifts, which is out of
  reach for this exhaustive method.
- A model with every generator fixing level 1 is a pair of `0`-odometer models one level down. So
  the missing `0000` pattern at level 7 is the `J = 0` wall at level 6 seen again.
