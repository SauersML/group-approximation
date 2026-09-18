# Half-tube lemma and synchronization: MSI checks (lane bh-free-61, 2026-09-18)

Evidence for `half-tube-lattice-points-are-edge-split-vertices` and Attempt 4 of
`unimodular-cells-synchronize-under-edge-splits`. Every run was single core and took
seconds, under `nice`, on the shared node. Generic points are modelled by random integer
vectors of 56 to 60 bits. A finite game reads only finitely many strict comparisons, so
a loss at a tie-free integer point persists on an open set. A win at such a point is
evidence only.

## 1. The joint game near a generic point (exact search)

Program `jg.c` (lane scratch). It computes, by exhaustive memoized search, whether the
joint subtractive game from `(w, ζ)` can be won, both from `Δ` and from a stuck cell
`c = XΔ` with `X ∈ {M, X9}`, where `M = [[3,1,0],[1,1,1],[0,1,2]]` and
`X9 = [[9,2,0],[2,1,1],[0,1,2]]`. The point `ζ` is `X·y` with random `y`.

- **Calibration.** `w = (1,1,1)` wins, as it must for every generic `ζ ∈ Δ`. `w = (1,1,100)` against
  `ζ ≈ (1, 2.0001, 2.0011)` loses, as a hand analysis predicts: the third coordinate can
  be reduced only about twice.
- **Closest losing points from `Δ`, by the size of `w`.**
  - Entry sum at most 30: angle about `0.08`–`0.13`.
  - Entry sum at most 90: angle `0.031`–`0.044`.
  - Random points of entry sum about 200–400: angle `0.011`–`0.018`.

  Every point closer than these, in every sample, won. Losers approach `ζ` roughly like
  `1/|w|`, so there is no fixed neighbourhood of winners, only a tube-shaped one.
- **Shared vertices.** In every trial, some `w` won from both `Δ` and `c`. The smallest
  were `(1,1,1)`, `(2,1,1)`, `(0,1,2)`, `(2,1,1)` (entry sum at most 30), and `(4,2,1)`,
  `(9,3,2)`, `(3,3,4)`, `(9,3,2)` (entry sum at most 90).

## 2. The half-tube strategy (rank 3, inside `jg.c`)

For random `t`, `w` is the primitive part of `round(tζ)`, which lies in the half-tube.
The strategy of the lemma's proof is run with exact rational bookkeeping of
`d = u − tz`. Each trial is 40000 points.
- **60-bit `ζ`, `L = |w|` scale 400, 20000 and `5·10^6`, 4 trials each** (480000 points):
  all won. There were no ties and no invariant violations. The maximum was 335077
  moves.
- **Same with `L = 400` and `3000`** (320000 points): all won.
  - The exhaustive search agreed on every point small enough to search: 35353 points,
    all won.
  - 4327, 1509, 4877 and 1568 (`L = 400`) and 4397, 1416, 4160 and 1380 (`L = 3000`) of
    the points were also in the half-tube of `c`. Every one also won the exhaustive game
    from `c`.
- **40-bit `ζ` at `L = 10^8`.** Between 1.8% and 5% of runs stopped early. That version did
  not classify stops. In the classified reruns (56–60 bits), every stop other than a step
  cap was a tie `z_i = z_j`: 4 of 20000 at `L = 10^9` in rank 3. Ties are an artifact of a
  rational `ζ` at depth.
- **A test bug, recorded.** A first version of the shared-tube check read `d` after the
  strategy had overwritten it and reported 523 false "losses". The fixed check saves `d`
  first.

## 3. The half-tube strategy in ranks 3 to 8 (`tubeN.c`, below)

| rank `n` | `L` | tested | won | logical failures | step-cap stops |
|---|---|---|---|---|---|
| 3 | `10^3`, `10^6`, `10^9` | 60000 | 60000 | 0 | 0 |
| 4 | `10^3` / `10^6` / `10^9` | 20000 / 2949 / 12 | 20000 / 2949 / 5 | 0 | 0 / 0 / 7 |
| 5 | `10^3` / `10^6` / `10^9` | 20000 / 1102 / 8 | 20000 / 1102 / 2 | 0 | 0 / 0 / 6 |
| 6 | `10^3` / `10^6` / `10^9` | 20000 / 560 / 7 | 20000 / 560 / 0 | 0 | 0 / 0 / 7 |
| 8 | `10^3` / `10^6` / `10^9` | 20000 / 241 / 5 | 20000 / 241 / 0 | 0 | 0 / 0 / 5 |

- "Logical failures" count every way the lemma could fail:
  - no same-sign pair;
  - `u_i < u_j` for a same-sign pair ordered by `z`;
  - the invariant `|d|_∞ < 1/2` or `z > 0` broken;
  - a stop away from a unit vector;
  - Case B with `z_b ≤ z_k`;
  - in a batched move, the `u` condition binding before the `z` and sign conditions.
- Step-cap stops (`5·10^7` moves) occur only at `|u|` near `10^9` in ranks at least 4.
  There the proof bounds the number of Case A moves by `|u|_1`, and the simple pair
  choice is slow.
- A first version of `tubeN.c` chose arbitrary pairs in Case B, including pairs of zero
  coordinates of `u`. It ran away in rank at least 4, as the proof predicts for that
  choice. The version below follows the proof.

## 4. The pointwise round lemma (`prl.c`, lane scratch)

For each stuck `3×3` matrix `X` of entry sum at most 26 (1369 up to row and column
permutation), and each braid pair, one full braid cut is made (Euclid rule). A leaf is
*bad* if its least left-reduction entry sum is at least that of `X`. The intersection of
the bad leaves of the three pairs is then tested for a common interior point, with an
exact `__int128` cone test.
- **Calibration.** `M` and `X9` have no bad leaves. `[[0,2,5],[2,1,1],[7,2,0]]` has one
  bad leaf per pair.
- **Controls for the intersection test.** Same cone: meets. Two halves of `Δ`: do not
  meet. Nested: meet.
- **Result.** 1217 matrices have a pair with no bad leaf. 85 are covered pointwise by
  different pairs. 67 have a common bad interior point, the first being
  `[[0,1,5],[1,1,1],[4,3,0]]` with witness ray `(96,35,63)`. No overflow.

## `tubeN.c`

```c
/* bh-free-61: half-tube lemma in rank n = m+1 >= 3.  zeta generic (random 56-bit integer coordinates), t > 0,
   w = primitive part of round(t.zeta).  d = w - t'.zeta has |d|_inf < 1/2.  Strategy: pick a pair (i,j) with
   d_i d_j >= 0 and z_i > z_j, preferring u_j > 0; the lemma says u_i >= u_j always and |d|_inf stays < 1/2.
   Exact arithmetic: d = D / DEN with D, DEN integers.  Single core, self-timed. */
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <unistd.h>
typedef __int128 i128; typedef long long ll;
static volatile sig_atomic_t timeup = 0; static void on_alarm(int s) { (void)s; timeup = 1; }
static unsigned long long rs = 0x9E3779B97F4A7C15ull;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static i128 ab(i128 x) { return x < 0 ? -x : x; }
int main(int argc, char **argv) {
  int n = argc > 1 ? atoi(argv[1]) : 4; ll L = argc > 2 ? atoll(argv[2]) : 100000; int NS = argc > 3 ? atoi(argv[3]) : 20000;
  int lim = argc > 4 ? atoi(argv[4]) : 60; signal(SIGALRM, on_alarm); alarm(lim);
  ll whyc[10] = {0}; ll tested = 0, won = 0, ties = 0, bad = 0, maxsteps = 0, caseB = 0;
  for (int k = 0; k < NS && !timeup; k++) {
    i128 z[8]; ll u[8]; i128 D[8];
    for (int i = 0; i < n; i++) z[i] = (i128)(rnd() >> 8) + 1;
    ll lam = L/2 + (ll)(rnd() % (unsigned long long)(L/2 + 1)); i128 den = z[0]; for (int i = 1; i < n; i++) if (z[i] > den) den = z[i];
    for (int i = 0; i < n; i++) { u[i] = (ll)((2*(i128)lam*z[i] + den) / (2*den)); D[i] = den*(i128)u[i] - (i128)lam*z[i]; }
    ll g = 0; for (int i = 0; i < n; i++) { ll x = u[i], y = g; while (y) { ll t = x % y; x = y; y = t; } g = x; }
    if (g == 0) continue;
    for (int i = 0; i < n; i++) u[i] /= g;
    i128 DEN = (i128)g * den; int ok = 1;
    for (int i = 0; i < n; i++) if (2*ab(D[i]) >= DEN) ok = 0;
    if (!ok) continue;
    tested++; ll steps = 0; int why = 0;
    for (;;) {
      int npos = 0; for (int i = 0; i < n; i++) if (u[i] > 0) npos++;
      if (npos == 1) break;
      int tie = 0; for (int i = 0; i < n; i++) for (int j = i+1; j < n; j++) if (z[i] == z[j]) tie = 1;
      if (tie) { why = 1; break; }
      int bi = -1, bj = -1;
      /* Case A: two coordinates with u > 0 and d of the same sign; orient by z */
      for (int i = 0; i < n && bi < 0; i++) for (int j = 0; j < n && bi < 0; j++) if (i != j && u[i] > 0 && u[j] > 0 && z[i] > z[j] && ((D[i] >= 0 && D[j] >= 0) || (D[i] <= 0 && D[j] <= 0))) { bi = i; bj = j; }
      if (bi < 0) { /* Case B: P = {a,b}, d_a > 0 > d_b; move (b,k) with u_k = 0, z_k largest; the lemma forces z_b > z_k */
        int b = -1, k = -1; for (int i = 0; i < n; i++) if (u[i] > 0 && D[i] < 0) b = i;
        for (int i = 0; i < n; i++) if (u[i] == 0 && (k < 0 || z[i] > z[k])) k = i;
        if (b < 0 || k < 0) { why = 2; break; }
        if (!(z[b] > z[k])) { why = 7; break; }
        bi = b; bj = k; caseB++; }
      if (u[bi] < u[bj]) { why = 3; break; }
      { i128 qz = (z[bi] - 1) / z[bj]; i128 qd = D[bj] == 0 ? qz : (D[bi] / D[bj]) + 1; i128 qm = qz < qd ? qz : qd;
        i128 qu = u[bj] > 0 ? (i128)(u[bi] / u[bj]) : qm; if (qu < qm) { why = 8; break; }   /* lemma: u-legality never binds first */
        if (qm < 1) { why = 9; break; }
        u[bi] -= (ll)qm * u[bj]; z[bi] -= qm * z[bj]; D[bi] -= qm * D[bj]; steps++; }
      for (int i = 0; i < n; i++) if (2*ab(D[i]) >= DEN || z[i] <= 0) why = 4;
      if (why || steps > 50000000) { if (!why) why = 5; break; }
    }
    if (!why) { int one = 0; for (int i = 0; i < n; i++) if (u[i] == 1) one++; if (one == 1) won++; else { why = 6; } }
    if (why == 1) ties++; else if (why) { bad++; whyc[why]++; }
    if (steps > maxsteps) maxsteps = steps;
  }
  printf("%s n=%d L=%lld: tested=%lld won=%lld ties(rational artifact)=%lld BAD=%lld maxsteps=%lld non-progress-moves=%lld\n",
         timeup ? "TIMEOUT(partial)" : "DONE", n, L, tested, won, ties, bad, maxsteps, caseB);
  printf("  BAD by reason: 2:%lld 3:%lld 4:%lld 5(step cap):%lld 6:%lld 7:%lld 8:%lld 9:%lld\n", whyc[2], whyc[3], whyc[4], whyc[5], whyc[6], whyc[7], whyc[8], whyc[9]);
  return 0;
}
```
