---
rg: 2
id: thompson-f-p22-over-f2-census-through-degree-nine-proof
kind: route
title: Settle every pair degree by degree with exact F_2 rank on letter windows, after reproducing the landed degree-seven census exactly and checking a plane symmetry the program never uses
target: thompson-f-p22-over-f2-exhaustive-census-through-degree-nine
requires: []
artifacts:
  - research/artifacts/hl-f-kernel-profiles-2026-09-14.md
---

Notation as in the claim. Let `W_D = M_(D, D+3)`.

**Step 1 (reduction to windows).** This is Steps 1–2 of `thompson-f-p22-over-f2-census-exhaustive-proof`.
`δ(a, b)` is the least `D` for which `A_D : (u, v) -> a u + b v` has a nonzero kernel on `F_2[W_D]^2`.

**Step 2 (normal forms by insertion).** Let `m = x_(i_1) ... x_(i_d)` with `i_1 <= ... <= i_d`, and let `p`
be a letter.
- *Moving the letter.* The relation `x_q x_i = x_i x_(q+1)` (`i < q`) moves `x_p` to the right past each
  `i_t` smaller than its current value `q`, raising `q` by one each time. It stops at the first `i_j >= q`.
- *Result.* The word `x_(i_1) ... x_(i_(j−1)) x_q x_(i_j) ... x_(i_d)` is nondecreasing, because
  `i_(j−1) <= q − 2`.
- *Monomials.* So `kprof.c` builds `x_p m` in normal form by this insertion, and sets `s m = x_i (x_j m)` for
  `s = x_i x_j`.

Distinct normal forms are distinct elements of `M`, as used in `thompson-f-p22-over-f2-census-exhaustive-proof`.

**Step 3 (rank).** `kprof.c` (md5 `0da7e074b9a437956da486660044e6dc`) computes the rank over `F_2` of `[A | B]`,
whose columns are `a u` and `b v` for `u, v ∈ W_D`.
- *Singleton peeling.* Suppose row `r` has exactly one nonzero entry, in column `c`. Then no linear dependency
  among the columns involves `c`, so `rank M = 1 + rank M'`, where `M'` deletes row `r` and column `c`. This is
  repeated while singleton rows remain.
- *Core.* The remaining core is eliminated by incremental Gaussian elimination over `F_2` on sorted sparse
  columns.
- *Kernel.* The kernel dimension is `2|W_D| − rank`.

**Step 4 (run).** `census_shard.sh` (md5 `57dec68d1b7a654b2ff3888baf2b4dcc`) takes the pairs `a < b` with `a mod 16`
fixed.
- *Degree by degree.* At degree `D` it tests only the pairs whose kernel was zero through `D − 1`.
- *Abort.* It aborts if `kprof` fails or omits a pair.
- *Job.* MSI job 753122 ran `census.sbatch` (md5 `6575ddd4a9367258635c706a2fc8d7c4`) as 16 tasks.
- *Snapshot.* At 2026-09-14 08:30 CDT every task had finished degree 9.
- *Merge.* `census_compare.py` (md5 `efe947172e87967d64b7100d169f01bf`) merges the shards and counts only degrees
  finished in all 16.

**Step 5 (checks).**
- *Independent implementation.* For `D <= 5`, the calibration build of `kprof.c` agrees with `kprof_check.py`
  (bubble-rewrite normal forms, plain elimination) on `(|W_D|, rows, rank, kernel)` in all 80 tested cases. That
  build differs from the landed one only in input handling (artifact §2). Every free-monoid control kernel is zero.
- *Reproduction.* Through degree 7 the per-degree histogram is `357, 3804, 3399, 6951, 5799, 7629, 8037`. The
  survivor list equals the landed `s35_unsolved_after_k7.json.gz` element for element; both flags are `true` in
  `census_compare.json`.
- *Plane symmetry.*
  - If `a u = b v` then `a (u + v) = (a + b) v`. The map `(u, v) -> (u + v, v)` is a linear bijection of
    `F_2[W_D]^2`, and swapping `u` and `v` handles `(a, b) -> (b, a)`.
  - So `k_D(a, b)`, and hence `δ(a, b)`, depends only on the plane `{0, a, b, a + b}`. Its three unordered pairs
    are `{a, b}`, `{a, a + b}` and `{b, a + b}`, and there are `(2^9 − 1)(2^9 − 2)/6 = 43435 = 130305/3` planes.
  - The program never uses this symmetry. Yet the survivor lists after degrees 7 and 9 are closed under it, and
    every per-degree count is divisible by 3.
- *Certificates.* MSI job 751856 checked explicit degree-8 common multiples for four pairs by composing
  piecewise-linear maps. All four are on the landed degree-7 list and absent from the degree-9 list.

The lower-bound part (item 2) rests on Steps 1–3: the insertion applies defining relations of `M`, and the rank
is exact.
