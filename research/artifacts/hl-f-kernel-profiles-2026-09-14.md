# Thompson's F, Guba's Problem P_(2,2) over F_2: window kernel profiles and the census beyond degree seven

Lane `hl-f-kernel-profiles`, 2026-09-14. Executes idea 3 of `research/artifacts/ideas-f-hyperbolic-2026-09-13.md`
(kernel-dimension profiles for stubborn `P_(2,2)` pairs). MSI directory:
`/scratch.global/sauer354/hl-f-kernel-profiles/`. Code: `experiments/thompson-f/kprof/`.

Nodes landed with this artifact:
- `thompson-f-ore-window-kernel-profiles-monotone-binomial-floor` and route
  `thompson-f-ore-window-kernel-profiles-proof`;
- `thompson-f-p22-over-f2-exhaustive-census-through-degree-nine` and route
  `thompson-f-p22-over-f2-census-through-degree-nine-proof`.

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

## 4. Census through degree nine

Node: `thompson-f-p22-over-f2-exhaustive-census-through-degree-nine`, route
`thompson-f-p22-over-f2-census-through-degree-nine-proof`.

**Run.**
- **Job.** MSI job 753122, 16 tasks, using `census.sbatch`, `census_shard.sh` and `kprof.c` (md5
  `0da7e074b9a437956da486660044e6dc`). It covers all 130305 pairs, with degrees `0..10` requested on windows
  `N = D + 3`.
- **Snapshot at 2026-09-14 08:30 CDT** (`census_sacct_snapshot.txt`, `census_progress_snapshot.txt`):
  - every task had finished degree 9;
  - tasks 0 and 4 had also finished degree 10;
  - the other 14 were still in degree 10.
- **Merge.** `census_compare.py` (md5 `efe947172e87967d64b7100d169f01bf`, run by `compare_pull.sh`) counts only
  degrees finished in all tasks.
- **Discarded run.** An earlier submission, job 751674, tested no pairs, because `kprof` then read pairs only from
  its arguments. It was discarded, and `census_shard.sh` now aborts on any missing output.

**Reproduction.** `census_compare.json` reports `hist_matches_landed_through_7: true` and
`unsolved_after_7_matches_landed_list: true`.

**Per-degree counts.**

| D | settled at D | unsettled before D | fraction settled | planes settled |
|---|---|---|---|---|
| 1 | 357 | 130305 | 0.27% | 119 |
| 2 | 3804 | 129948 | 2.93% | 1268 |
| 3 | 3399 | 126144 | 2.69% | 1133 |
| 4 | 6951 | 122745 | 5.66% | 2317 |
| 5 | 5799 | 115794 | 5.01% | 1933 |
| 6 | 7629 | 109995 | 6.94% | 2543 |
| 7 | 8037 | 102366 | 7.85% | 2679 |
| 8 | 8880 | 94329 | 9.41% | 2960 |
| 9 | 8619 | 85449 | 10.09% | 2873 |

After degree 9, 76830 pairs (25610 planes) survive (`s35_unsolved_after_k9.json.gz`).

**Plane symmetry.** `k_D(a, b)` depends only on the plane `{0, a, b, a + b}` (route, Step 5). The program never uses
this, and the data satisfy it:
- the survivor lists after degrees 7 and 9 are closed under `{a, b} -> {a, a + b}`;
- every count above is divisible by 3;
- the planes add up to 43435.

**Kernel dimension at the first positive degree** (`kernel_at_first_degree_hist`).
- **Usually one-dimensional.** At `D = 9`, 3510 of the 8619 pairs settle with kernel dimension 1.
- **Sometimes many at once.** Some pairs settle with many independent minimal multiples: `k_8 = 409` for 18 pairs,
  and `k_9 = 1140` for 6 pairs.
- **Symmetry.** Every multiplicity is divisible by 3.

**Degree 10 (partial, not counted).**
- Task 0 went from 2207 to 1771 survivors in 20228 s.
- Task 4 went from 3591 to 3216 survivors in 25359 s.
- Degree-9 wall time per task ranged from 439 s to 18594 s.

**Reading.**
- **No saturating core yet.** Since degree 5, the fraction of survivors settling in the next degree has risen every
  time: 5.01%, 6.94%, 7.85%, 9.41%, 10.09%. Through degree 9 there is no sign of a core of pairs that stops
  settling.
- **Evidence, not proof.** A pair with `δ = ∞` leaves the same finite record as a pair with a huge finite `δ`.
- **Tower bound doesn't apply.** The tower bound `thompson-f-cardinality-certificates-need-tower-degree` concerns
  cardinality certificates, not these linear-algebra degrees.

## 5. Exact gap

- **No certificate from finite data.** A non-Ore pair of `P_(2,2)` needs an argument valid in every degree, and no
  finite profile or census gives one. See claim item 3 of
  `thompson-f-ore-window-kernel-profiles-monotone-binomial-floor`, and
  `thompson-f-ore-obstructions-must-see-finite-support`. The live formulations are the harmonic-splitting and
  private-pivot routes of `research/artifacts/hl-f-p22-invariant-2026-09-13.md`.
- **Candidates.** Over `F_2`, 76830 pairs (25610 planes) have `δ > 9`.
- **Next computation.**
  - **Target:** degree 10 on the survivors, one pair per plane. That saves a factor of 3, which the current run
    doesn't use.
  - **Cost:** the two finished tasks took about 7–9 s per pair at degree 10, so the 25610 planes need roughly 50–65
    CPU hours.
- **Job 753122.** Fourteen tasks were still in degree 10 at the snapshot and are not counted. Some may hit the
  12 h limit.
