---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k4-n19-g6-window-proof
kind: route
title: Cover C_19^4 by the 19 rotations of the window {0,1,2,3,4,6} and certify c(G_6) >= 8.7515 by a symmetry-reduced exact-rational SDP branch-and-bound
target: hermitian-edge-trace-norm-web-rank-k4-n19
requires: []
artifacts:
  - research/hermitian-edge-trace-norm-odd-antihole-facets-by-size.md
  - experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/fastbb.py
  - experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/run.sh
  - experiments/hermitian-edge-trace-norm-web-k4-p7-2026-09-19/README.md
  - experiments/hermitian-edge-trace-norm-web-k4-p7-2026-09-19/g6s.log
---

A computer-assisted proof. It is unreviewed and not Lean-verified. Lane w10-078, 2026-09-19.

Notation: `c(F)` is the minimum of `||C||_1` over admissible `C` on `F`. `G_6` is the graph on
`0..5` with `K_5` on `0..4` and vertex `5` adjacent to `2, 3, 4`.

## Step 1. Windows

- Let `U_t = {t, t+1, t+2, t+3, t+4, t+6}` (mod `19`), for `t in Z_19`.
  - Inside `U_t`, the pairs at cyclic distance at most `4` are all pairs of `t..t+4`, and
    `(t+6, t+2)`, `(t+6, t+3)`, `(t+6, t+4)`.
  - The pairs `(t+6, t)` and `(t+6, t+1)` are at distance `6` and `5`. So `U_t` induces `G_6`, with
    `t+6` in the role of vertex `5`.
- Each vertex lies in exactly `6` of the `U_t`.
- The covering lemma (Lemma 1 of `hermitian-edge-trace-norm-odd-antihole-facets-by-size`) gives
  `||C||_1 >= (19/6) c(G_6)`.
  - A principal submatrix of an admissible matrix is admissible on the induced subgraph.
- With `c(G_6) >= 8.7515`: `(19 x 8.7515)^2 = 166.2785^2 = 27648.54 > 27648 = (6 x 16 sqrt3)^2`.
  So `(19/6) 8.7515 > 16 sqrt3`.

## Step 2. `c(G_6) >= 8.7515`

The command is

```text
SYM='3.4+4.5-3.5<4.5;4.5<3.5;0.3<1.3' ROOT=2 FIRST=0-1 \
  bash run.sh g6s 'W13/1.2.3.4:0,1,2,3,4,6' 8.7515 2.376 0 1.5707963267948966 40
```

It is run in `experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/`. The final line of
`g6s.log` reads `ALL CLOSED`.

- `W13/1.2.3.4:0,1,2,3,4,6` is the subgraph of `C_13^4` induced on those vertices. Its vertices
  are indexed `0..5` in that order, so it is `G_6`.
- **The certificate** is that of `fastbb.py`, unchanged from w9-078's `c(K_5) >= 7.2169`.
  - The gauge makes the 5 edges at the root `2` real and positive, which leaves 8 free phases.
  - If some modulus exceeds `T`, pinching gives `||C||_1 >= 2T + MCUT`. The remaining four
    vertices always contain two disjoint edges, so `MCUT = 4`, and `2 x 2.376 + 4 >= 8.7515`.
  - Otherwise a box of phases is closed by an exactly checked Gaussian-rational `Z` with
    `-I < Z < I`, via `||C||_1 >= tr(ZC)` minimised over the box and the moduli in `[1, T]`.

**The symmetry reduction is valid.** Write `u(x)` for the distance from `x` to `pi Z`. With the
star tree at `2`, the phase `i.j` of a free edge is the phase of the triangle `{2, i, j}`, and
`i.j + j.k - i.k` is that of `{i, j, k}`.

1. Relabelling by an automorphism of `G_6`, conjugating `C`, and replacing `C` by `-C` each keep
   admissibility and `||C||_1`.
2. Conjugation maps every triangle phase `phi` to `-phi`.
3. For `-C`, regauge by `-1` on every vertex other than `2`. Then every free phase gains `pi`, and
   every triangle phase gains `pi`.
4. So conjugation and `-C` keep every `u(triangle)`, while automorphisms permute the triangles.
5. `Aut(G_6)` contains the permutations of `{2, 3, 4}` and the swap of `0, 1`.
   - The triangles through `5` are `{3,4,5}`, `{2,4,5}`, `{2,3,5}`, the complements of `2, 3, 4`
     in `{2, 3, 4, 5}`.
   - `S_3` on `{2, 3, 4}` permutes these triangles as it permutes their missing vertices. So some
     permutation gives `u(345) <= u(245) <= u(235)`.
   - The swap of `0, 1` fixes those three triangles and exchanges `{0,2,3}` and `{1,2,3}`. So one
     can also have `u(023) <= u(123)`.
   - These are the three SYM conditions. `sym_drop` drops a box only when one condition fails
     everywhere on it.
6. Finally, by 3, `-C` moves the phase of `01` by `pi`, and by 2 conjugation negates it. Neither
   changes any `u`. So one can take this phase in `[0, pi/2]` without losing the conditions in 5.

Every admissible `C` is thus equivalent to one in the searched region, with the same trace norm.

## Step 3. Conclusion

By Steps 1 and 2, `||C||_1 >= (19/6) 8.7515 > 16 sqrt3` for every admissible `C` on `C_19^4`.
