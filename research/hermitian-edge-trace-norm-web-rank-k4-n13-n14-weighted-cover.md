---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k4-n13-n14-weighted-cover
kind: route
title: Cover C_13^4 and C_14^4 by weighted rotations of the window {0,1,2,3,4,8} and certify c(K_5 plus a pendant, w) >= 6.23539 by a symmetry-reduced exact-rational SDP branch-and-bound
target: hermitian-edge-trace-norm-web-rank-k4-n13-n14
requires: []
artifacts:
  - research/hermitian-edge-trace-norm-odd-antihole-facets-by-size.md
  - experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/fastbb.py
  - experiments/hermitian-edge-trace-norm-web-k4-weighted-2026-09-19/README.md
  - experiments/hermitian-edge-trace-norm-web-k4-weighted-2026-09-19/fastbbw.py
  - experiments/hermitian-edge-trace-norm-web-k4-weighted-2026-09-19/runw.sh
  - experiments/hermitian-edge-trace-norm-web-k4-weighted-2026-09-19/k5p.log
---

A computer-assisted proof. It is unreviewed and not Lean-verified. Lane w11-078, 2026-09-19.

Notation: for a graph `H` on `0..m-1` and weights `w_i > 0`, `c(H, w)` is the minimum of `||C||_1`
over Hermitian `C` on `H` (zero diagonal, zero on non-edges) with `|C_ij| >= sqrt(w_i w_j)` on
edges; `|w| = sum w_i`. `H` below is `K_5` on `0..4` plus vertex `5` joined only to `4`, and
`w = (3/4, 3/4, 3/4, 3/4, 1, 1/5)`, `|w| = 21/5`.

## Step 1. The weighted covering lemma

**Lemma.** Let `C` be Hermitian `N x N` and let `W_1, ..., W_m` be diagonal with `W_t >= 0` and
`sum_t W_t <= I`. Then `||C||_1 >= sum_t ||W_t^(1/2) C W_t^(1/2)||_1`.

*Proof.* Write `C = P - N` with `P, N >= 0` and `||C||_1 = tr P + tr N`. By the triangle
inequality and positivity,
`||W_t^(1/2) C W_t^(1/2)||_1 <= tr(W_t^(1/2) P W_t^(1/2)) + tr(W_t^(1/2) N W_t^(1/2)) = tr(W_t (P + N))`.
Summing, `sum_t tr(W_t (P + N)) = tr((sum_t W_t)(P + N)) <= tr(P + N)`, since `P + N >= 0`. QED.

**Homogeneity.** `c(H, s w) = s c(H, w)` for `s > 0`: `C` is feasible for `w` iff `s C` is
feasible for `s w`.

## Step 2. Windows

Let `n in {13, 14}` and `U_t = {t, t+1, t+2, t+3, t+4, t+8}` (mod `n`).

- Inside `U_t` the pairs at cyclic distance at most `4` are the pairs of `t..t+4` and
  `(t+4, t+8)`. The pairs `(t+8, t+j)`, `j = 0..3`, have distances `8, 7, 6, 5` for `n = 14` and
  `5, 6, 6, 5` for `n = 13` (the smaller of `8 - j` and `n - 8 + j`). So `U_t` induces `H`, with
  `t + j` in the role of `j` for `j <= 4` and `t + 8` in the role of `5`.
- Let `W_t = diag` of the weight `w_j / |w|` at `t + j` (`j = 0..4`) and `w_5/|w|` at `t + 8`,
  zero elsewhere. Every vertex receives each of the six weights from exactly one `t`, so
  `sum_t W_t = I`.
- For admissible `C` on `C_n^4`, the principal submatrix of `W_t^(1/2) C W_t^(1/2)` on `U_t` is
  Hermitian on `H`, with `|entry_ij| = sqrt(w_i w_j) |C_ij| / |w| >= sqrt((w_i/|w|)(w_j/|w|))`.
  So its trace norm is at least `c(H, w/|w|) = c(H, w)/|w|`, and by the Lemma
  `||C||_1 >= n c(H, w) / |w|`.
- With `c(H, w) >= 6.23539` (Step 3), exactly in rationals:
  `(14 x 6.23539)^2 = 7620.4973... >= 432 (21/5)^2 = 7620.48 = (12 sqrt3 |w|)^2`, and
  `(13 x 6.23539)^2 = 6570.7349... >= 363 (21/5)^2 = 6403.32 = (11 sqrt3 |w|)^2`.

## Step 3. `c(H, w) >= 6.23539`

The command, in `experiments/hermitian-edge-trace-norm-web-k4-weighted-2026-09-19/`, is

```text
SYM='0.1<0.2,0.3,1.2,1.3,2.3;0.2<0.3,1.2,1.3' ROOT=4 FIRST=0-1 CKEVERY=200 \
  bash runw.sh k5p 'W14/1.2.3.4:0,1,2,3,4,8' 6.23539 3/4,3/4,3/4,3/4,1,1/5 0 1.5707963267948966
```

The final line of `k5p.log` reads `ALL CLOSED`.

**The certificate** (`fastbbw.py`; its header lists the changes against `fastbb.py` of w9-078).
Write `D = diag(w)` and `C = D^(1/2) K D^(1/2)`; then `C` is feasible iff `K` is admissible on `H`.

- The gauge makes the 5 edges at the root `4` real and positive. The pendant edge `45` carries no
  phase, which leaves the 6 phases `i.j` (`0 <= i < j <= 3`), the phase of the triangle `{4, i, j}`.
- **Modulus cut.** If `|K_ij| > T_ij`, pinching `C` into `{i, j}` and a packing of the other four
  vertices into disjoint edges and triangles gives `||C||_1 >= 2 T_ij sqrt(w_i w_j) + MCUT_ij`.
  - An edge `ab` of the packing contributes `2 |C_ab| >= 2 sqrt(w_a w_b)`.
  - A triangle `abc` contributes `2 sqrt(w_a w_b + w_b w_c + w_a w_c)`: its `3 x 3` block has trace
    zero, and for a trace-zero `lambda in R^3`, `||lambda||_1^2 >= 2 ||lambda||_2^2 = 4 sum |C_..|^2`.
  - `T_ij` is set so that `2 T_ij sqrt(w_i w_j) + MCUT_ij >= TARGET`. The values, printed on the
    first line of `k5p.log`, are `2.1` on `i4`, `3.6173` on `45` and `2.2421` on `ij`.
- **Boxes.** Otherwise a box of phases, with moduli `|K_e| in [1, T_e]`, is closed by a
  Gaussian-rational `Z'` with `-D < Z' < D`, checked exactly by Fraction pivots of `D -+ Z'`.
  Then `Z = D^(-1/2) Z' D^(-1/2)` has `-I < Z < I`, and
  `||C||_1 >= tr(Z C) = tr(Z' K) = sum_e |K_e| g_e(phase_e)`, minimised over the box as in `fastbb.py`.
- Calibration: on `K_3` with weights `1, 2, 3` the program closes `6.6` and fails at `6.64`, while
  `c(K_3, w) = 2 sqrt 11 = 6.6332` (the triangle bound above, attained).

**The symmetry reduction is valid.** Write `u(x)` for the distance from `x` to `pi Z`.

1. Relabelling by an automorphism of `H` that preserves `w`, conjugating `C`, and replacing `C` by
   `-C` each keep feasibility and `||C||_1`.
2. Conjugation maps every triangle phase `phi` to `-phi`. For `-C`, regauge by `-1` on every vertex
   other than `4`; then every free phase, being a triangle phase, gains `pi`. So both keep every
   `u(i.j)`.
3. `S_4` on `{0, 1, 2, 3}` fixes `4` and `5` and the weights. It maps the triangle `{4, i, j}` to
   `{4, s(i), s(j)}`; reversing the orientation of a triangle negates its phase, which keeps `u`.
   So `S_4` permutes the six values `u(i.j)` as it permutes the pairs `ij`.
4. `S_4` is transitive on pairs, so some element makes `u(0.1)` the least of the six. The
   stabiliser of the pair `01` is `{e, (01), (23), (01)(23)}`, and it acts regularly on the
   four pairs `02, 03, 12, 13` (`(01)` swaps `02 <-> 12`, `03 <-> 13`; `(23)` swaps `02 <-> 03`, `12 <-> 13`). So a further element
   makes `u(0.2)` the least of `u(0.2), u(0.3), u(1.2), u(1.3)`. These are the two SYM
   conditions; `sym_drop` drops a box only when one inequality fails everywhere on it.
5. Finally, by 2, `-C` moves the phase `0.1` by `pi` and conjugation negates it, and neither changes
   any `u`. So one can take `0.1` in `[0, pi/2]` without losing the conditions in 4.

Every feasible `C` is thus equivalent to one in the searched region, with the same trace norm.

## Step 4. Conclusion

By Steps 2 and 3, `||C||_1 >= 14 x 6.23539 / 4.2 > 12 sqrt3` on `C_14^4` and
`||C||_1 >= 13 x 6.23539 / 4.2 > 11 sqrt3` on `C_13^4`, for every admissible `C`.
