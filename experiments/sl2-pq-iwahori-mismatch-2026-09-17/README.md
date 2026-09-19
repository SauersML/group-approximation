# q-adic Iwahori mismatch for SL_2(Z[1/pq])

Supports `research/iwahori-depth-drift-bounds-smooth-vertex-mismatch.md`.

Setting: `K_0 = SL_2(Z_q)`, `K_1 = g K_0 g^-1` with `g = diag(q,1)`, and
`I = K_0 cap K_1 = {b = 0 mod q}`. `sigma_0` is a level-`k` representation of
`K_0`, meaning a representation of `SL_2(Z/q^k)`. `sigma_1` is a level-`k`
representation of `K_1`. The mismatch is the fraction of `sigma_0|_I` that has
no partner in `sigma_1|_I`.

## Files

- `chartab.py`: numerical character tables (Burnside), checked against the
  orthogonality relations and against `sum deg^2 = |G|`.
- `mismatch_lp.py q k [theta]`: computes the least mismatch `c_k(theta)` with
  HiGHS. The constraint is that the `K_0`-trivial fraction of `sigma_0` is
  `<= theta`. The script also prints an exact rational weak-duality lower bound.
- `depth_drift.py q k`: exact check of the depth-drift certificate. Let
  `c = (q-1)/(q+1)`. The certificate is `g = d_1 - d_0` on nontrivial
  `I`-irreps and `g = -c` on the trivial one.
  - Every nontrivial `chi` has `E g >= c` through `K_0`.
  - Every nontrivial `chi` has `E g <= -c` through `K_1`.
  - It follows that `eps >= (1 - theta_0) c`.

Each run takes seconds, except `depth_drift.py 2 4`, which takes a few minutes.
Run the scripts from this directory.

## Results (2026-09-18)

`mismatch_lp.py` (primal optimum = exact certified dual bound):

| q | k | theta | c_k(theta) | (1-theta)(q-1)/(q+1) |
|---|---|-------|-----------|----------------------|
| 2 | 1 | 1/2 | 1/4 | 1/6 |
| 2 | 2 | 1/2 | 1/6 | 1/6 |
| 2 | 3 | 1/2 | 1/6 | 1/6 |
| 2 | 1 | 0 | 1/2 | 1/3 |
| 2 | 2 | 0 | 1/3 | 1/3 |
| 2 | 3 | 0 | 1/3 | 1/3 |
| 3 | 1 | 0 | 1/2 | 1/2 |
| 3 | 2 | 0 | 1/2 | 1/2 |
| 3 | 2 | 1/2 | 1/4 | 1/4 |

`depth_drift.py`: the certificate holds exactly, with equality in the extreme
case, for these `(q,k)`:

- `(2,1)`, `(2,2)`, `(2,3)`, `(2,4)`;
- `(3,1)`, `(3,2)`;
- `(5,1)`.

In every case `Phi` takes all three values `{-1,0,1}`.

For `k >= 2`, the least mismatch is exactly `(1-theta)(q-1)/(q+1)`, and it does
not decrease as `k` grows. This is the uniform bound proved in the research
note.
