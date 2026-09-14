# Thompson's F, Guba's Problem P_(2,2) over F_2: window kernel profiles and the census beyond degree seven

Lane `hl-f-kernel-profiles`, 2026-09-14. Executes idea 3 of `research/artifacts/ideas-f-hyperbolic-2026-09-13.md`
(kernel-dimension profiles for stubborn `P_(2,2)` pairs). MSI directory:
`/scratch.global/sauer354/hl-f-kernel-profiles/`. Code: `experiments/thompson-f/kprof/`.

Nodes landed with this artifact:
- `thompson-f-ore-window-kernel-profiles-monotone-binomial-floor` and route
  `thompson-f-ore-window-kernel-profiles-proof`.

## 1. What a profile is, and the verdict on idea 3

For a pair `a, b` of nonzero elements of `F_2[S]`, `S` one of Guba's monomial sets, and degree `D`,
`k_D(a, b) = dim{(u, v) ∈ F_2[M_(D, D+3)]^2 : a u = b v}`. The least `D` with `k_D > 0` is the minimal
common-multiple degree `δ(a, b)` (letter windows suffice, Step 2 of
`thompson-f-p22-over-f2-census-exhaustive-proof`).

**Verdict: idea 3 is dead as a certification device** (claim item 3). A stubborn pair has `k_D = 0` in every
computed degree, so its profile has no terms to extrapolate. Positive profiles belong to settled pairs, are
nondecreasing, and sit above the binomial floor `C(2D+3−δ, D−δ)` coming from right multiples of one kernel
vector (claim items 1–2). The kill criterion recorded in the idea sweep ("profiles show no recurrence") is
superseded by a stronger reason: for the pairs that matter there is no profile at all.

**What survives from the computation.** The C implementation is fast enough to extend the `F_2` census of
`P_(2,2)` beyond degree 7, which the landed census named as the next computation. See §4.

## 2. Program and calibration

`kprof.c`. Calibration and the degree `<= 7` sample profiles ran with md5 `11baa44ed5707427334960e3429a27a2`
(`calib.out`, `logs/small_751484.log` header). The landed version, md5 `0da7e074b9a437956da486660044e6dc`,
adds reading pairs from standard input; the elimination is unchanged, and on MSI it reproduces the argument
mode output byte for byte at `k = 0` and `k = 7` (`cmp` on four pairs). Normal forms by left insertion (a letter `p` inserted into
a normal form walks right while the next letter is `<` its current value, growing by one per letter passed);
products `s u` for `s = x_i x_j` computed as `x_i (x_j u)`. Rank of `[A | B]` over `F_2` by singleton-row
peeling (a row with one live entry at column `c` contributes one to the rank and removes `c`), then sparse
incremental elimination on the remaining core. `kernel = 2|V| − rank`. Mode `free` uses the free monoid as a
non-Ore control.

Calibration (`calib.sh`, MSI, all `CALIB_OK`):
- **Cross-check against an independent implementation.** `kprof_check.py` builds normal forms with the bubble
  rewrite `x_j x_i -> x_i x_(j+1)` of `ore_linalg.py` and plain elimination on Python integers. For `k = 0..5`
  the tuples `(|V|, rows, rank, kernel)` agree exactly on 5 `S_(3,5)` pairs (30 cases), 5 `S_(2,4)` pairs
  (30 cases) and 4 free-monoid pairs (20 cases).
- **Free control.** Every free-monoid kernel is `0`.
- **Consistency with the landed census.** Through `k = 7`, all 24 sampled settled pairs have a positive
  kernel by degree 7 and all 24 sampled unsettled pairs have `k_D = 0` for `D <= 7` (`analyze.py`: 0
  problems). The full census reproduction is §4.

## 3. Profiles (sample, seed 20260914)

`sample_pairs.py` draws 6 unsettled pairs from each x_0-sieve category of 199bac76a and 24 settled pairs.
Selected exact profiles `k_0..k_8`:

| set | a | b | role | δ | profile |
|---|---|---|---|---|---|
| S_(2,4) | 1 | 2 | settled | 1 | 0, 1, 6, 28, 120, 495, 2002, 8008 (= `C(2D+2, D−1)`, floor attained) |
| S_(2,4) | 5 | 26 | settled | 2 | 0, 0, 1, 7, 36, 165, 715, 3003 (= `C(2D+1, D−2)`, floor attained) |
| S_(2,4) | 3 | 12 | settled | 3 | 0, 0, 0, 1, 9, 54, 274, 1275 (floor `C(2D, D−3)` exceeded from D = 4) |
| S_(3,5) | 74 | 256 | settled | 2 | 0, 0, 1, 7, 36, 165, 715, 3003 (floor attained) |
| S_(3,5) | 278 | 480 | settled | 3 | 0, 0, 0, 1, 8, 45, 220, 1002, 4381 (floor attained through D = 6) |
| S_(3,5) | 5 | 401 | settled | 4 | 0, 0, 0, 0, 1, 10, 66, 363, 1806 |
| S_(3,5) | 82 | 273 | settled | 7 | 0, …, 0, 1, 16 |
| S_(3,5) | 19 | 29 | unsettled after 7 | 8 | 0, …, 0, 1 |
| S_(3,5) | 483 | 484 | unsettled after 7 | 8 | 0, …, 0, 8 |

Of the 24 sampled pairs unsettled after degree 7, **8 settle at degree 8** and 16 have `k_8 = 0`.
Full data: `research/artifacts/hl-f-kernel-profiles-2026-09-14-data/`.

**Independent check of four degree-8 settlements (MSI job 751856, 4 tasks, all COMPLETED 0:0).** For the
pairs `(19, 29)`, `(280, 296)`, `(216, 223)`, `(498, 501)`, all on the landed list of pairs unsettled after
degree 7, the landed `ore_certify.py` (md5 `bfa7a0289ff8b2fd9abaab3000f0ad73`) produced explicit
`u, v ∈ F_2[M_(8, 11)]` with `a u = b v`, and the landed `ore_verify.py cert`
(md5 `0774d779b2d4e5d6977037aec1c7fed2`) recomputed `a u = b v ≠ 0` by composing piecewise-linear maps,
without normal forms: `certificates_checked: 1, ALL_OK: true` in every task. Term counts `|u| + |v|`:
334, 80, 1025, 3366. Certificates: `cert8_out_{0..3}.json.gz`; log excerpts `cert8_log_{0..3}.txt`.
So these four pairs have `δ = 8` over `F_2` (degree `<= 7` excluded by the landed census).

## 4. Census extension

(Filled in when MSI job 751674 finishes: all 130305 pairs, degrees 0..10, 16 shards; the reproduction of the
landed degree-7 histogram and unsettled list; the per-degree settled counts for D = 8, 9, 10.)

## 5. Exact gap

- A non-Ore pair of `P_(2,2)` can only be certified by an argument valid in every degree; no finite profile or
  census does it (claim item 3; `thompson-f-ore-obstructions-must-see-finite-support`).
- The census extension measures how fast survivors settle. It is evidence either way, not proof.
