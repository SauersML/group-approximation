# Searching for a binary SMART: exhaustive small reversible Turing machines (lane gq-nv-obstruct, 2026-09-18)

**Goal** (coordinator): find a reversible moving-tape machine, or a `kV` element, whose moves nest by a
primitive constant-length-2 substitution with locally readable phases. Inducing on its genuine moves and
finding a head-adjacent `φ` with `φU^2 = Uφ` would then give `BS(1,2) <= nV`, as in the `m = 3` case
(`bs13-embeds-in-brin-thompson-3v`).

**Verdict: not found.**
- Every exhaustively searched class gives either ternary behaviour, like SMART, or binary timing with
  unbounded per-level overhead.
- One partially searched class (8+8 states, binary alphabet, mirror-symmetric) contains machines with
  exactly binary frontier timing `t_{j+1} = 2t_j + {0,-2}`. That is the one lead.
- Two diagnostics count against a clean 2-adic hierarchy for the lead: its cyclic-tape periods, and the
  way its local-type counts drift.
- Nothing here is established except the computations themselves. All runs were on MSI, single core,
  at most 10 minutes each, in `/projects/standard/hsiehph/sauer354/gqsrc/gq-nv-obstruct/`. Nothing was
  run locally.

## 1. Why SMART is ternary, and what binary would need

- **Parity.** In SMART every move is a crossing: it enters a domain at one end and leaves at the other
  (`prop:smart-moves`). If a level-`(k+1)` crossing consists of level-`k` crossings of one sub-domain
  plus boundedly many steps, the number of sub-crossings is odd. So 3 is the least branching above 1.
- **Prefix consistency.** A move that starts at its anchor must begin with the lower-level move of the
  same type, because the machine cannot see the block length. That is why `σ(b)` and `σ(d)` begin with
  `b` and `d`.
  - Mixing crossing and return moves naively breaks this. The run would have to depend on the parity of
    the block length before the head sees it.
- **The natural binary scheme.** Let crossings `X` and returns `Y` satisfy
  `X_{k+1} = X_k Y_k` and `Y_{k+1} = X'_k X_k`, where `'` is the mirror image.
  - This is the constant-length-2 substitution `a→ac, b→bd, c→ba, d→ab`. It is primitive and
    prefix-consistent for crossings.
  - Its durations satisfy `W_{k+1} = W_k + 2W_{k-1}`. The characteristic polynomial is
    `x^2 - x - 2 = (x-2)(x+1)`, so the durations are Jacobsthal-type numbers, `2^k` up to `±` bounded
    terms.
  - To be a move at all, a return must turn one cell short of the anchor. The machine must realize that
    turn locally.

## 2. The search

**Model.** SMART's format (the Kari–Ollinger model).
- There are `n` move states, each with a direction, and `n` read/write states.
- A bijection `β: (read state, symbol) → (move state, symbol)`.
- Alphabet size `g`.

**Filter ("complete counter").** On every cyclic tape of length `L <= Lmax`, the permutation has at most
`n` cycles, each of length at least `L·g^L`. It is calibrated on SMART (mask 5,
β = 4,10,11,1,7,8,2,0,9,5,3,6), which passes with 4 cycles of length `2L·3^L`.

**Frontier test.** On a zero tape with one anchor `1`, record the first-visit times `t_j` of new cells.
- A machine is ballistic if, from some start, `t_{j+1}/t_j → 1`.
- For the others, the overhead is `t_{j+1} - 2t_j` (binary) or `t_{j+1} - 3t_j` (ternary).

| class (states + states, alphabet) | machines | pass filter | non-ballistic | frontier growth |
|---|---|---|---|---|
| 2+2, 2 | 96 | 0 | – | – |
| 2+2, 3 | 2,880 | 24 | – | 2 cycles of `2L·3^L` (ternary counters) |
| 3+3, 2 | 5,760 | 0 | – | – |
| 3+3, 3 | 2,903,040 | 144 | – | 3 cycles of `2L·3^L` (ternary) |
| 4+4, 2 (all) | 645,120 | 1,440 | 192 | ratio 2, overhead **Θ(j)**: `t_j = 2^{j+2} - 2j - 4`, and a second family with overhead growing by 6 every two levels |
| 4+4, 3 (mirror-symmetric) | 184,320 | 240 (SMART among them) | – | ratio 3 or 9 only |
| 6+6, 2 (mirror-symmetric) | 368,640 | 0 | – | – |
| 8+8, 2 (mirror-symmetric, partial: run stopped at the 10-min cap) | ≥ 37,316 passed | 37,316 | ≥ 5,012 (partial) | ratio-2 machines with overhead **periodic**, e.g. `{0,-2}`, `{3,1}`, `{5,3}` |

## 3. The lead: a binary machine with Jacobsthal timing

`M*`: `n = 8`, `g = 2`, mask 169 (states 0, 3, 5, 7 move right), β = 6,14,4,12,10,15,8,13,5,1,7,3,11,2,9,0.

- **Frontier.** `t_j = 6, 12, 22, 44, 86, 172, 342, 684, 1366, 2732, 5462, …, 2796204`. So
  `t_{j+1} = 2t_j + {0,-2}`, and `3t_j = 2^{j+2} ± 2`: bounded overhead, as in §1's scheme.
- **Cyclic tapes.** 4 cycles, of lengths `L·(2^{L+4} ± 2)/3`, for example `4774, 2394` at `L = 7`. Their
  2-adic valuation is only `v_2(L) + 1`, unlike SMART's 3-adic valuation `L`. This counts against a
  `Z_2` factor. It is not a proof, since cyclic tapes are a different system.
- **Local-type counts** (`rtm_levels`, 3·10^6 steps).
  - All 128 local types (phase, state, head cell, two neighbours) occur with nearly equal frequency.
  - The per-type overheads `n_{j+1}(τ) - 2n_j(τ)` grow linearly or quadratically in `j`, and cancel only
    in total.
  - A hierarchy with bounded junctions would make them bounded (a symmetric/antisymmetric analysis of
    §1's recursion gives eigenvalues `2, -1, 1`).
  - So `M*` probably runs linear walks inside its levels, balanced so the total stays binary. A clopen
    `Y` with exactly 2-adic counts would have to omit those walks, which contradicts bounded returns.
    This is a heuristic, not a proof.
  - Some 3-type combinations do cancel to zero after one level, for example classes C2 + C4 + C12 in
    `lev169.out`. Their bounded return and local phase are **untested**.

## 3b. Ranking by per-type overhead (`rtm_levels_batch`, second MSI pass)

The 5,012 non-ballistic 8+8 binary machines of the partial search were ranked. Each got 200k steps from
each of its 16 starts, and the score is `max_τ |n_{j+1}(τ) - 2n_j(τ)|` over the last levels. 3,379 reached
10 or more levels.
- **Best class** (215 machines, max overhead 4 → 6): for example mask 154, β = 8,12,10,14,15,11,13,9,1,6,3,4,0,7,2,5.
  - Its frontier is `t_j = 2^{j+2} - 2j - 4`, the same linear-overhead family as in 4+4 states.
  - Only 40 of the 128 local types occur. Their overheads are bounded (0 or period 2), **except for four
    types whose counts grow linearly**.
  - Those four types are the linear walk that adds `2j` steps per level.
  - Inducing on the complement of the walk would give exact binary counts. But the walks are unbounded
    runs, so `brin-thompson-first-return-maps-lie-in-kv` does not apply.
- **The Jacobsthal lead `M*`** is in a worse class, with quadratic per-type drift.
- **Every machine found so far has an exact bounded-junction binary skeleton plus a linear walk.** The
  natural conjecture, not proved, is that single-head reversible machines of this format cannot avoid
  the walk. The parity argument of §1 is the reason. If so, `BS(1,2)` needs a `kV`-native element (one
  that inserts and deletes cells next to the head), a second head, or a different base altogether.

## 3c. The full mirror-symmetric 8+8 binary class, and the parity lemma

- **Search.** Each direction mask takes 70 s. All masks give 4,560 passes, and the classes are identical
  up to relabeling within mirror pairs, so mask 0 represents the whole space.
- **Ranking.** The full mask-0 class was ranked, 4,200 machines with at least 10 levels. The best class
  is again the bounded skeleton plus a linear walk, with overhead 4 → 6. So in mirror-symmetric
  one-head binary machines with 8+8 states there is **no** binary SMART.
- **Parity lemma** (`crossing-move-hierarchies-have-odd-branching`). Crossing-only hierarchies branch
  oddly. A binary hierarchy needs returns that turn one cell short of the domain end, triggered by marks
  near the head.
- **kV-native options, not built.** A `kV` element can delete or insert a cell next to the head. That
  lets a move change its own domain length, which a Turing machine cannot do.
  - The parity lemma still applies whenever domains grow by a bounded amount per level. So insertion
    helps only by changing *where* the domain ends are, for example by keeping the anchor adjacent to the
    head.
  - A design would have to keep bounded junctions and bounded junction chains. Neither was attempted
    here.

## 3d. Targeted scan for binary timing, without the completeness filter (2026-09-18, coordinator's order)

**Scanner** `rtm_scan_sym`. It covers mirror-symmetric machines, with one direction mask (the others
are equivalent up to relabeling). Each machine runs from the anchored zero tape for up to 20k steps, with
early exits for linear motion and for stalls. It keeps machines with at least 10 frontier advances whose
last 4 ratios lie in [1.8, 2.25].

**Ranker** `rtm_levels_batch2`. The same per-type overhead ranking as §3b, but only over starts whose
frontier ratio is about 2.

| class | scanned | binary-timing candidates | best per-type overhead growth |
|---|---|---|---|
| 4+4 states, 3 symbols | all 46,080 | 974 | growth 2 (max 4 → 6): linear walk |
| 8+8 states, 2 symbols | slice `ord[0]=0`, 1.29M | 24,804 | growth 4: linear walk |
| 6+6 states, 3 symbols | 2 of 9 slices, partial (10-min cap) | 309,052 (25,586 ranked) | **growth 0** for 5 machines; growth 2 otherwise |

**The growth-0 machines** were induced with `rtm_induce`.
- `Y` is the set of local types whose overhead `n_{j+1} - 2n_j` vanishes on the last 8 levels.
- The tool then measures the maximal gap between `Y`-times, the `Y`-counts at the frontier times, and
  whether a window of radius `r` determines the induced index mod `2^k`, using a hash union and counting
  conflicts.
- Example: `M°` = mask 21, β = 3,4,11,0,1,8,16,2,10,13,5,7,6,17,12,9,14,15, start 2.
  - `Y` has 52 types.
  - The `Y`-counts at the frontier are 6, 8, 18, 58, 116, 232, …, 1,900,544: **exact doubling from level
    3**, block sizes `29·2^m`.
  - The maximal gap is **87**, bounded over 6·10^6 steps.
  - But the phase is not local. At `k = 1` the window determines it (radius 3–9, 0 conflicts). At `k = 2`
    there are 182 conflicts at radius 12 and 974 at radius 9. At `k = 3` there are 1.3–1.6·10^6
    conflicts at radius 12–15.
- The other exact-doubling candidates behave the same way. They have 42 and 44 `Y`-types, gaps 221 and
  155, and exact doubling. Their `k = 3` phase has about 10^6 conflicts at radius 12.

**Reading.** Exact 2-adic counts with bounded returns do occur, which the parity lemma allows. But the
2-adic phase is not a local function beyond `k = 1`, which a height-2 renormalization would need.
- This matches gq-affq's conjecture in `gq-affq-binary-two-head-design.md`: a binary hierarchy needs
  control information that grows with the level. Here it shows up as a phase that no bounded window
  determines.
- Not proved. The 6+6 ternary scan covered only 2/9 of the space, and the growth-0 search was not
  exhaustive.

## 3e. Correction to §3d, and the return-time test (2026-09-18)

**Correction.** The phase-conflict counts in §3d are wrong.
- The cause: `rtm_induce` hashed the state and the first window cell into the same FNV byte, so
  `(state 3, cell 0)` and `(state 2, cell 1)` collided.
- `rtm_certcheck`, an independent re-simulation, printed the two "conflicting" windows and they differed.
- The hash has been fixed (state multiplied in separately, plus a second 64-bit hash). With the fix, for
  all three exact-doubling machines:
  - `mod 2` and `mod 4` show **0 conflicts** at radius 6 and 9;
  - the remaining `mod 8` conflicts all involve one early configuration of the orbit.
- So the §3d sentences "mod 4: hundreds of conflicts at radius 12" and "mod 8: about 10^6 conflicts at
  radius 12–15" are withdrawn.

**Return-time test** (`renormalization-return-times-tend-to-zero-adically`, item 3). `rtm_recur` fixes
the first `Y`-configuration `y` at or after `t_1`. It lists later `Y`-times whose state and window of
radius `r` equal those of `y`, with the induced index difference `n`.

| machine (`Y`) | radius | returns found | `n mod 2^j` (or `3^j`) |
|---|---|---|---|
| SMART, genuine level-0 moves (calibration, `m = 3`) | 6 | 2 in `4·10^7` steps | `n ≡ 0 mod 729` (3-adically small, as required) |
| `M°`, mask 21, β = 3,4,11,0,1,8,16,2,10,13,5,7,6,17,12,9,14,15, start 2, 52 zero-overhead types | 10 | `n` = 14852, 29700, 44548, 59396 | **`n ≡ 4 mod 64`** each |
| same | 14 | `n` = 237572, 475140, 712708, 950276 | **`n ≡ 4 mod 64`** each |
| same (`rtm_cert` certificates, checked by `rtm_certcheck`) | 12 / 15 / 16 / 18 | `n = 29·2^m + 4` for `m = 11, 14, 15, 17` | `n ≡ 4 mod 8` |

The other two exact-doubling machines of §3d show the same pattern: their first `mod 8` conflicts have
phase difference 4.

**Reading.**
- Every return of `y` found so far, up to radius 18, has `n ≡ 4 mod 8`, and the matching radius grows
  with `m`. If `U°^{n_m} y → y` along `n_m = 29·2^m + 4` (all radii), then item 3 shows that `U°` has no
  height-2 renormalization, indeed no `mod 8` phase. That convergence is certified only up to radius 18,
  so this remains OPEN.
- **Why 3 passes and 2 fails here.** In SMART induced on genuine moves, every level-`k` move starts at an
  induced time `≡ 0 mod 3^k`: sub-moves are consecutive blocks, and the specials are exactly the
  non-`Y` steps. So returns are 3-adically small.
- In `M°` the zero-overhead `Y` gives exact doubling of counts, with blocks of `29·2^m`. But the
  configuration `y` recurs at induced offset `+4`, at every level: two points at different `mod 8`
  phases agree on ever larger windows. That is a recognizability failure, not a counting failure.
- Consistent with that, the parity lemma (`crossing-move-hierarchies-have-odd-branching`) forces binary
  hierarchies to use returns, and SMART's recognizability comes from a boundary-cell parent table that
  crossing-only hierarchies have. **Not proved for a class.**

## 4. What is left

1. Finish the 8+8 binary mirror-symmetric search: split it by direction mask into ≤ 10-minute runs.
   Then rank the candidates by bounded per-type overhead, not by total overhead.
2. For any candidate, rerun the SMART pipeline:
   - a clopen `Y` with bounded returns and exact `c·2^k` counts per level;
   - unique length-2 desubstitution;
   - radius-`(k+O(1))` phase readability.
3. Design by hand from §1's scheme, `a→ac, b→bd, c→ba, d→ab`. The one missing mechanism is a local
   trigger for a return to turn one cell short of the anchor. For example, the anchor could carry a
   neighbouring mark cell that crossings create on first entry and never erase.
4. Beyond Turing machines: `kV` elements may insert and delete cells next to the head, which Turing
   machines cannot. That may avoid the parity constraint of §1.

## 5. Scripts (verbatim; compiled with `gcc -O2` on MSI)

### `rtm_search.c` (md5 f9b75b43b66fec63cbcc3cd7b47bdf06)

```c
/* rtm_search.c -- search small reversible Turing machines (Kari--Ollinger model, SMART's format)
 * for "complete counter" behaviour on cyclic tapes, as candidates for a binary SMART analogue.
 * Lane gq-nv-obstruct, 2026-09-18. MSI only; single core.
 *
 * Model: n move states q2_i (i < n) with direction dir[i] in {+1,-1}: q2_i --dir--> q1_i;
 *        n symbol states q1_i: bijection beta: (i, a) -> (j, b) meaning q1_i reads a, writes b, goes to q2_j.
 *        Alphabet size g. Configuration on a cyclic tape of length L: (phase, state, pos, tape).
 * Test: for L = 1..Lmax the induced permutation on the 2*n*L*g^L configurations has all cycles of length
 *        >= L*g^L (so every cycle visits at least as many configurations as (pos, tape) pairs), and
 *        at most n cycles. SMART (n = 4, g = 3) passes with exactly 4 cycles of length 2*L*3^L.
 * Output: machines passing up to Lmax, with the cycle lengths at Lmax.
 * Usage: rtm_search n g Lmax [dirmask_filter]   (enumerates all dir masks and all beta permutations)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, g, Lmax;
static int dir[8];
static int betaS[64], betaB[64]; /* index i*g+a -> (state j, write b) */
static int perm[64];
static unsigned char *seen;
static int *cyclen;

static long ipow(int b, int e) { long r = 1; while (e--) r *= b; return r; }

/* config encoding: ((phase*n + state)*L + pos)*T + tape, tape in base g, cell c digit = (tape / g^c) % g */
static long step(long cfg, int L, long T, const long *pw) {
    long tape = cfg % T; cfg /= T;
    int pos = cfg % L; cfg /= L;
    int st = cfg % n; int ph = cfg / n;
    if (ph == 1) { /* move state */
        pos = (pos + dir[st] + L) % L;
        return ((0L * n + st) * L + pos) * T + tape;
    } else {
        int a = (tape / pw[pos]) % g;
        int idx = st * g + a;
        int j = betaS[idx], b = betaB[idx];
        tape += (long)(b - a) * pw[pos];
        return ((1L * n + j) * L + pos) * T + tape;
    }
}

static int test(int L, int verbose) {
    long T = ipow(g, L);
    long N = 2L * n * L * T;
    long pw[16]; for (int c = 0; c < L; c++) pw[c] = ipow(g, c);
    memset(seen, 0, N);
    int ncyc = 0; long minlen = N;
    for (long s = 0; s < N; s++) {
        if (seen[s]) continue;
        long c = s, len = 0;
        while (!seen[c]) { seen[c] = 1; len++; c = step(c, L, T, pw); }
        if (c != s) return 0; /* not a permutation (should not happen for bijective beta) */
        if (len < minlen) minlen = len;
        if (ncyc < 64) cyclen[ncyc] = (int)len;
        ncyc++;
        if (ncyc > n) return 0;
    }
    if (minlen < L * T) return 0;
    if (verbose) { printf("   L=%d cycles=%d lens:", L, ncyc); for (int i = 0; i < ncyc && i < 64; i++) printf(" %d", cyclen[i]); printf("\n"); }
    return 1;
}

static int next_perm(int *a, int m) {
    int i = m - 2; while (i >= 0 && a[i] >= a[i + 1]) i--; if (i < 0) return 0;
    int j = m - 1; while (a[j] <= a[i]) j--; int t = a[i]; a[i] = a[j]; a[j] = t;
    for (int l = i + 1, r = m - 1; l < r; l++, r--) { t = a[l]; a[l] = a[r]; a[r] = t; }
    return 1;
}

int main(int argc, char **argv) {
    n = atoi(argv[1]); g = atoi(argv[2]); Lmax = atoi(argv[3]);
    int onlymask = argc > 4 ? atoi(argv[4]) : -1;
    const char *calib = argc > 5 ? argv[5] : NULL;
    int m = n * g;
    long maxN = 2L * n * Lmax * ipow(g, Lmax);
    seen = malloc(maxN); cyclen = malloc(64 * sizeof(int));
    long tried = 0, passed = 0;
    for (int mask = 0; mask < (1 << n); mask++) {
        if (onlymask >= 0 && mask != onlymask) continue;
        for (int i = 0; i < n; i++) dir[i] = (mask >> i & 1) ? +1 : -1;
        for (int i = 0; i < m; i++) perm[i] = i;
        if (calib) { const char *p = calib; for (int i = 0; i < m; i++) { perm[i] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; } }
        do {
            for (int i = 0; i < m; i++) { betaS[i] = perm[i] / g; betaB[i] = perm[i] % g; }
            tried++;
            int ok = 1;
            for (int L = 1; L <= Lmax && ok; L++) ok = test(L, 0);
            if (ok) {
                passed++;
                printf("PASS mask=%d beta=", mask);
                for (int i = 0; i < m; i++) printf("%d%s", perm[i], i + 1 < m ? "," : "");
                printf("\n");
                test(Lmax, 1);
                fflush(stdout);
            }
        } while (!calib && next_perm(perm, m));
    }
    printf("n=%d g=%d Lmax=%d tried=%ld passed=%ld\nRTM_SEARCH_DONE\n", n, g, Lmax, tried, passed);
    return 0;
}
```

### `rtm_search_sym.c` (md5 363afd83f8cced44fcac9e4136d1bf32)

```c
/* rtm_search_sym.c -- as rtm_search.c, restricted to space-symmetric machines (like SMART):
 * states come in mirror pairs (2i, 2i+1) with opposite directions, and beta commutes with the mirror
 * iota(state) = state ^ 1 (symbols unchanged). Lane gq-nv-obstruct, 2026-09-18. MSI only.
 * Usage: rtm_search_sym n g Lmax   (n even)
 * Output lines "PASS mask=M beta=..." in the same format as rtm_search.c (full beta over all n*g inputs).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, g, Lmax;
static int dir[16];
static int betaS[128], betaB[128];
static unsigned char *seen;
static int cyclen[64];

static long ipow(int b, int e) { long r = 1; while (e--) r *= b; return r; }

static long step(long cfg, int L, long T, const long *pw) {
    long tape = cfg % T; cfg /= T;
    int pos = cfg % L; cfg /= L;
    int st = cfg % n; int ph = cfg / n;
    if (ph == 1) { pos = (pos + dir[st] + L) % L; return ((0L * n + st) * L + pos) * T + tape; }
    int a = (tape / pw[pos]) % g; int idx = st * g + a;
    int j = betaS[idx], b = betaB[idx];
    tape += (long)(b - a) * pw[pos];
    return ((1L * n + j) * L + pos) * T + tape;
}

static int test(int L, int verbose) {
    long T = ipow(g, L), N = 2L * n * L * T;
    long pw[16]; for (int c = 0; c < L; c++) pw[c] = ipow(g, c);
    memset(seen, 0, N);
    int ncyc = 0; long minlen = N;
    for (long s = 0; s < N; s++) {
        if (seen[s]) continue;
        long c = s, len = 0;
        while (!seen[c]) { seen[c] = 1; len++; c = step(c, L, T, pw); }
        if (c != s) return 0;
        if (len < minlen) minlen = len;
        if (ncyc < 64) cyclen[ncyc] = (int)len;
        if (++ncyc > n) return 0;
    }
    if (minlen < L * T) return 0;
    if (verbose) { printf("   L=%d cycles=%d lens:", L, ncyc); for (int i = 0; i < ncyc && i < 64; i++) printf(" %d", cyclen[i]); printf("\n"); }
    return 1;
}

static int next_perm(int *a, int m) {
    int i = m - 2; while (i >= 0 && a[i] >= a[i + 1]) i--; if (i < 0) return 0;
    int j = m - 1; while (a[j] <= a[i]) j--; int t = a[i]; a[i] = a[j]; a[j] = t;
    for (int l = i + 1, r = m - 1; l < r; l++, r--) { t = a[l]; a[l] = a[r]; a[r] = t; }
    return 1;
}

int main(int argc, char **argv) {
    n = atoi(argv[1]); g = atoi(argv[2]); Lmax = atoi(argv[3]);
    int h = n / 2, m = h * g; /* even inputs (2i, a), i < h; output orbits {(2j,b),(2j+1,b)} */
    seen = malloc(2L * n * Lmax * ipow(g, Lmax));
    long tried = 0, passed = 0;
    int ord[64];
    for (int dm = 0; dm < (1 << h); dm++) {
        for (int i = 0; i < h; i++) { dir[2 * i] = (dm >> i & 1) ? +1 : -1; dir[2 * i + 1] = -dir[2 * i]; }
        for (int i = 0; i < m; i++) ord[i] = i;
        do {
            for (int bits = 0; bits < (1 << m); bits++) {
                for (int e = 0; e < m; e++) {
                    int i = e / g, a = e % g;            /* even input (2i, a) */
                    int orb = ord[e], j = orb / g, b = orb % g;
                    int pick = bits >> e & 1;           /* which element of the output orbit */
                    int jj = 2 * j + pick;
                    betaS[(2 * i) * g + a] = jj;         betaB[(2 * i) * g + a] = b;
                    betaS[(2 * i + 1) * g + a] = jj ^ 1; betaB[(2 * i + 1) * g + a] = b;
                }
                tried++;
                int ok = 1;
                for (int L = 1; L <= Lmax && ok; L++) ok = test(L, 0);
                if (ok) {
                    passed++;
                    int mask = 0; for (int i = 0; i < n; i++) if (dir[i] > 0) mask |= 1 << i;
                    printf("PASS mask=%d beta=", mask);
                    for (int x = 0; x < n * g; x++) printf("%d%s", betaS[x] * g + betaB[x], x + 1 < n * g ? "," : "");
                    printf("\n");
                    test(Lmax, 1); fflush(stdout);
                }
            }
        } while (next_perm(ord, m));
    }
    printf("sym n=%d g=%d Lmax=%d tried=%ld passed=%ld\nRTM_SEARCH_DONE\n", n, g, Lmax, tried, passed);
    return 0;
}
```

### `rtm_frontier.c` (md5 e6ae3a92bcf31f0ab1f717d3fd5e47dc)

```c
/* rtm_frontier.c -- for candidate machines (lines "PASS mask=M beta=b0,b1,..." on stdin), simulate on a
 * Z-tape and print the first-visit times of new cells (the frontier), to detect hierarchical crossing times.
 * Lane gq-nv-obstruct, 2026-09-18. MSI only.
 * Usage: rtm_frontier n g steps < survivors.txt
 * For each machine and each start (state s, phase), tape: all 0 except cell 0 = 1 (anchor), head at 0.
 * Prints: machine, start, and the times at which the right frontier reaches cells 1,2,3,... (up to 24),
 * and the successive ratios t(k+1)/t(k).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
    int n = atoi(argv[1]), g = atoi(argv[2]); long steps = atol(argv[3]);
    int m = n * g;
    char line[4096];
    int W = 1 << 22; /* tape width */
    unsigned char *tape = malloc(W);
    while (fgets(line, sizeof line, stdin)) {
        if (strncmp(line, "PASS", 4)) continue;
        line[strcspn(line, "\n")] = 0;
        int mask; char *b = strstr(line, "beta="); if (!b) continue;
        sscanf(line, "PASS mask=%d", &mask);
        int perm[64]; char *p = b + 5;
        for (int i = 0; i < m; i++) { perm[i] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; }
        int dir[8]; for (int i = 0; i < n; i++) dir[i] = (mask >> i & 1) ? +1 : -1;
        for (int st = 0; st < n; st++) for (int ph = 0; ph < 2; ph++) {
            memset(tape, 0, W);
            long h = W / 2; tape[h] = 1; int s = st, phase = ph;
            long maxr = h, minl = h; long tr[64]; int nr = 0; long tl[64]; int nl = 0;
            for (long t = 0; t < steps; t++) {
                if (phase == 1) { h += dir[s]; phase = 0; }
                else { int a = tape[h]; int idx = s * g + a; tape[h] = perm[idx] % g; s = perm[idx] / g; phase = 1; }
                if (h <= 1 || h >= W - 2) break;
                if (h > maxr) { maxr = h; if (nr < 64) tr[nr++] = t + 1; }
                if (h < minl) { minl = h; if (nl < 64) tl[nl++] = t + 1; }
            }
            printf("mask=%d beta=%s start=(%d,%d) right:", mask, b + 5, st, ph);
            /* strip newline in beta printing */
            for (int i = 0; i < nr && i < 24; i++) printf(" %ld", tr[i]);
            printf(" | left:");
            for (int i = 0; i < nl && i < 24; i++) printf(" %ld", tl[i]);
            printf("\n");
        }
    }
    printf("RTM_FRONTIER_DONE\n");
    return 0;
}
```

### `rtm_levels.c` (md5 4d66e86f50ab40b1d5ece108cc8df535)

```c
/* rtm_levels.c -- for one machine, run from an anchored zero tape and tabulate, for each local type
 * tau = (phase, state, head symbol, left symbol, right symbol), the counts n_j(tau) of steps of that type in
 * the prefix [0, t_j), where t_j is the j-th first-visit time of a new cell on the growth side.
 * Then v_j(tau) = n_{j+1}(tau) - 2 n_j(tau) measures the per-level overhead of that type.
 * Lane gq-nv-obstruct, 2026-09-18. MSI only.
 * Usage: rtm_levels n g mask beta_csv start_state start_phase steps
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
    int n = atoi(argv[1]), g = atoi(argv[2]), mask = atoi(argv[3]);
    const char *bs = argv[4]; int s = atoi(argv[5]), phase = atoi(argv[6]); long steps = atol(argv[7]);
    int m = n * g, perm[128]; const char *p = bs;
    for (int i = 0; i < m; i++) { perm[i] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; }
    int dir[16]; for (int i = 0; i < n; i++) dir[i] = (mask >> i & 1) ? +1 : -1;
    long W = 1L << 23; unsigned char *tape = calloc(W, 1); long h = W / 2; tape[h] = 1;
    int NT = 2 * n * g * g * g; long *cnt = calloc(NT, sizeof(long));
    long maxr = h, minl = h; int side = 0; long tj[64], tjl[64]; int nj = 0, njl = 0;
    long (*snap)[4096] = malloc(64 * sizeof *snap); /* counts snapshot at each t_j (NT <= 4096) */
    long (*snapl)[4096] = malloc(64 * sizeof *snapl);
    for (long t = 0; t < steps; t++) {
        int tau = (((phase * n + s) * g + tape[h]) * g + tape[h - 1]) * g + tape[h + 1];
        cnt[tau]++;
        if (phase == 1) { h += dir[s]; phase = 0; }
        else { int a = tape[h]; int idx = s * g + a; tape[h] = perm[idx] % g; s = perm[idx] / g; phase = 1; }
        if (h <= 2 || h >= W - 3) break;
        if (h > maxr) { maxr = h; if (nj < 64) { tj[nj] = t + 1; memcpy(snap[nj], cnt, NT * sizeof(long)); nj++; } }
        if (h < minl) { minl = h; if (njl < 64) { tjl[njl] = t + 1; memcpy(snapl[njl], cnt, NT * sizeof(long)); njl++; } }
    }
    if (njl > nj) { nj = njl; memcpy(tj, tjl, sizeof tj); memcpy(snap, snapl, 64 * sizeof *snap); side = -1; } else side = 1;
    printf("frontier(%s side):", side > 0 ? "right" : "left");
    for (int j = 0; j < nj; j++) printf(" %ld", tj[j]); printf("\n");
    /* overhead vectors */
    for (int tau = 0; tau < NT; tau++) {
        if (snap[nj - 1][tau] == 0) continue;
        int ph = tau / (n * g * g * g), rest = tau % (n * g * g * g);
        int st = rest / (g * g * g), a = (rest / (g * g)) % g, l = (rest / g) % g, r = rest % g;
        printf("tau ph=%d st=%d a=%d l=%d r=%d  n_last=%ld  v:", ph, st, a, l, r, snap[nj - 1][tau]);
        for (int j = 2; j + 1 < nj; j++) printf(" %ld", snap[j + 1][tau] - 2 * snap[j][tau]);
        printf("\n");
    }
    printf("RTM_LEVELS_DONE\n");
    return 0;
}
```

### `rtm_levels_batch.c` (md5 f6942ec175045de46b0c98aa2a445919)

```c
/* rtm_levels_batch.c -- rank machines (lines "PASS mask=M beta=..." on stdin) by the growth of per-local-type
 * level overheads v_j(tau) = n_{j+1}(tau) - 2 n_j(tau) (binary) on the anchored zero tape, for the start with
 * the most frontier advances. A hierarchy with bounded junctions gives bounded v; linear walks give growing v.
 * Output: "RANK maxv_late=<max |v| over the last 3 levels> maxv_mid=<max |v| over 3 levels, 4 earlier>
 *          ratio=<t_last/t_prev> mask=.. beta=..".  Lane gq-nv-obstruct, 2026-09-18. MSI only.
 * Usage: rtm_levels_batch n g steps
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXJ 40
int main(int argc, char **argv) {
    int n = atoi(argv[1]), g = atoi(argv[2]); long steps = atol(argv[3]);
    int m = n * g, NT = 2 * n * g * g * g;
    long W = 1L << 21; unsigned char *tape = malloc(W);
    long *cnt = malloc(NT * sizeof(long));
    long (*snap)[1024] = malloc(MAXJ * sizeof *snap), (*snapl)[1024] = malloc(MAXJ * sizeof *snapl);
    long (*best)[1024] = malloc(MAXJ * sizeof *best);
    char line[4096];
    while (fgets(line, sizeof line, stdin)) {
        if (strncmp(line, "PASS", 4)) continue;
        line[strcspn(line, "\n")] = 0;
        int mask; char *b = strstr(line, "beta="); if (!b) continue; sscanf(line, "PASS mask=%d", &mask);
        int perm[128]; char *p = b + 5;
        for (int i = 0; i < m; i++) { perm[i] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; }
        int dir[16]; for (int i = 0; i < n; i++) dir[i] = (mask >> i & 1) ? +1 : -1;
        int bestn = 0; long bt[MAXJ];
        for (int st = 0; st < n; st++) for (int ph0 = 0; ph0 < 2; ph0++) {
            memset(tape, 0, W); memset(cnt, 0, NT * sizeof(long));
            long h = W / 2; tape[h] = 1; int s = st, phase = ph0;
            long maxr = h, minl = h; int nj = 0, njl = 0; long tj[MAXJ], tjl[MAXJ];
            for (long t = 0; t < steps; t++) {
                int tau = (((phase * n + s) * g + tape[h]) * g + tape[h - 1]) * g + tape[h + 1];
                cnt[tau]++;
                if (phase == 1) { h += dir[s]; phase = 0; }
                else { int a = tape[h]; int idx = s * g + a; tape[h] = perm[idx] % g; s = perm[idx] / g; phase = 1; }
                if (h <= 2 || h >= W - 3) break;
                if (h > maxr) { maxr = h; if (nj < MAXJ) { tj[nj] = t + 1; memcpy(snap[nj], cnt, NT * sizeof(long)); nj++; } }
                if (h < minl) { minl = h; if (njl < MAXJ) { tjl[njl] = t + 1; memcpy(snapl[njl], cnt, NT * sizeof(long)); njl++; } }
            }
            if (nj > bestn) { bestn = nj; memcpy(bt, tj, sizeof tj); memcpy(best, snap, MAXJ * sizeof *snap); }
            if (njl > bestn) { bestn = njl; memcpy(bt, tjl, sizeof tjl); memcpy(best, snapl, MAXJ * sizeof *snapl); }
        }
        if (bestn < 10) continue;
        long late = 0, mid = 0;
        for (int j = bestn - 4; j < bestn - 1; j++) for (int tau = 0; tau < NT; tau++) {
            long v = best[j + 1][tau] - 2 * best[j][tau]; if (v < 0) v = -v; if (v > late) late = v; }
        for (int j = bestn - 8; j < bestn - 5; j++) for (int tau = 0; tau < NT; tau++) {
            long v = best[j + 1][tau] - 2 * best[j][tau]; if (v < 0) v = -v; if (v > mid) mid = v; }
        printf("RANK maxv_late=%ld maxv_mid=%ld ratio=%.3f levels=%d mask=%d beta=%s\n", late, mid,
               (double)bt[bestn - 1] / bt[bestn - 2], bestn, mask, b + 5);
        fflush(stdout);
    }
    printf("RTM_LEVELS_BATCH_DONE\n");
    return 0;
}
```

### `rtm_scan_sym.c` (md5 bdf2a17fd0c906ea6ee0b14205a055c7)

```c
/* rtm_scan_sym.c -- fast scan of mirror-symmetric reversible TMs (SMART format, n even, alphabet g) for
 * BINARY frontier timing on an anchored zero tape, without the cyclic completeness filter.
 * Lane gq-nv-obstruct, 2026-09-18. MSI only; single core.
 * For each machine and each start (state 0 or 2, phase 0), run up to S steps on a tape that is 0 except
 * cell 0 = 1, record first-visit times t_1 < t_2 < ... of new cells (either side, whichever grows).
 * Candidate: at least J advances, and the last 4 ratios t_{j+1}/t_j lie in [1.8, 2.25].
 * Early exit: the head is more than R cells from 0 (linear motion), or no new cell for 4*(t_last+50) steps.
 * Usage: rtm_scan_sym n g S J R [ord_first_filter]   ord_first_filter splits the enumeration (value of ord[0]).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, g;
static int dir[16], betaS[128], betaB[128];

static int next_perm(int *a, int m) {
    int i = m - 2; while (i >= 0 && a[i] >= a[i + 1]) i--; if (i < 0) return 0;
    int j = m - 1; while (a[j] <= a[i]) j--; int t = a[i]; a[i] = a[j]; a[j] = t;
    for (int l = i + 1, r = m - 1; l < r; l++, r--) { t = a[l]; a[l] = a[r]; a[r] = t; }
    return 1;
}

#define W 4096
static unsigned char tape[W];

static int scan(long S, int J, int R, int st0, long *tj, int *njout) {
    memset(tape, 0, W);
    int h = W / 2; tape[h] = 1; int s = st0, phase = 0;
    int maxr = h, minl = h, nr = 0, nl = 0; long tr[64], tl[64]; long lastnew = 0;
    for (long t = 0; t < S; t++) {
        if (phase == 1) { h += dir[s]; phase = 0; }
        else { int a = tape[h]; int idx = s * g + a; tape[h] = betaB[idx]; s = betaS[idx]; phase = 1; }
        if (h - W / 2 > R || W / 2 - h > R) return 0;
        if (h > maxr) { maxr = h; if (nr < 64) tr[nr++] = t + 1; lastnew = t; }
        if (h < minl) { minl = h; if (nl < 64) tl[nl++] = t + 1; lastnew = t; }
        if (t - lastnew > 4 * (lastnew + 50)) break;
    }
    long *T = nr >= nl ? tr : tl; int nj = nr >= nl ? nr : nl;
    if (nj < J) return 0;
    for (int j = nj - 4; j < nj; j++) {
        double r = (double)T[j] / T[j - 1];
        if (r < 1.8 || r > 2.25) return 0;
    }
    for (int j = 0; j < nj; j++) tj[j] = T[j];
    *njout = nj;
    return 1;
}

int main(int argc, char **argv) {
    n = atoi(argv[1]); g = atoi(argv[2]); long S = atol(argv[3]); int J = atoi(argv[4]); int R = atoi(argv[5]);
    int f0 = argc > 6 ? atoi(argv[6]) : -1;
    int h = n / 2, m = h * g;
    long tried = 0, cand = 0; int ord[64];
    for (int i = 0; i < h; i++) { dir[2 * i] = +1; dir[2 * i + 1] = -1; } /* one mask suffices up to relabeling */
    for (int i = 0; i < m; i++) ord[i] = i;
    do {
        if (f0 >= 0 && ord[0] != f0) continue;
        for (int bits = 0; bits < (1 << m); bits++) {
            for (int e = 0; e < m; e++) {
                int i = e / g, a = e % g, orb = ord[e], j = orb / g, b = orb % g, jj = 2 * j + ((bits >> e) & 1);
                betaS[(2 * i) * g + a] = jj;       betaB[(2 * i) * g + a] = b;
                betaS[(2 * i + 1) * g + a] = jj ^ 1; betaB[(2 * i + 1) * g + a] = b;
            }
            tried++;
            for (int st0 = 0; st0 < n; st0 += 2) {
                long tj[64]; int nj;
                if (scan(S, J, R, st0, tj, &nj)) {
                    cand++;
                    printf("PASS mask=%d beta=", 0x5555 & ((1 << n) - 1));
                    for (int x = 0; x < n * g; x++) printf("%d%s", betaS[x] * g + betaB[x], x + 1 < n * g ? "," : "");
                    printf("  start=%d t:", st0);
                    for (int j = 0; j < nj && j < 20; j++) printf(" %ld", tj[j]);
                    printf("\n"); fflush(stdout);
                    break;
                }
            }
        }
    } while (next_perm(ord, m));
    printf("scan n=%d g=%d S=%ld tried=%ld cand=%ld\nRTM_SCAN_DONE\n", n, g, S, tried, cand);
    return 0;
}
```

### `rtm_levels_batch2.c` (md5 8ce68a79f264dc0ca1df7dd097b36957)

```c
/* rtm_levels_batch.c -- rank machines (binary-ratio starts only) (lines "PASS mask=M beta=..." on stdin) by the growth of per-local-type
 * level overheads v_j(tau) = n_{j+1}(tau) - 2 n_j(tau) (binary) on the anchored zero tape, for the start with
 * the most frontier advances. A hierarchy with bounded junctions gives bounded v; linear walks give growing v.
 * Output: "RANK maxv_late=<max |v| over the last 3 levels> maxv_mid=<max |v| over 3 levels, 4 earlier>
 *          ratio=<t_last/t_prev> mask=.. beta=..".  Lane gq-nv-obstruct, 2026-09-18. MSI only.
 * Usage: rtm_levels_batch n g steps
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXJ 40
int main(int argc, char **argv) {
    int n = atoi(argv[1]), g = atoi(argv[2]); long steps = atol(argv[3]);
    int m = n * g, NT = 2 * n * g * g * g;
    long W = 1L << 21; unsigned char *tape = malloc(W);
    long *cnt = malloc(NT * sizeof(long));
    long (*snap)[1024] = malloc(MAXJ * sizeof *snap), (*snapl)[1024] = malloc(MAXJ * sizeof *snapl);
    long (*best)[1024] = malloc(MAXJ * sizeof *best);
    char line[4096];
    while (fgets(line, sizeof line, stdin)) {
        if (strncmp(line, "PASS", 4)) continue;
        line[strcspn(line, "\n")] = 0;
        int mask; char *b = strstr(line, "beta="); if (!b) continue; sscanf(line, "PASS mask=%d", &mask);
        int perm[128]; char *p = b + 5;
        for (int i = 0; i < m; i++) { perm[i] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; }
        int dir[16]; for (int i = 0; i < n; i++) dir[i] = (mask >> i & 1) ? +1 : -1;
        int bestn = 0; long bt[MAXJ];
        for (int st = 0; st < n; st++) for (int ph0 = 0; ph0 < 2; ph0++) {
            memset(tape, 0, W); memset(cnt, 0, NT * sizeof(long));
            long h = W / 2; tape[h] = 1; int s = st, phase = ph0;
            long maxr = h, minl = h; int nj = 0, njl = 0; long tj[MAXJ], tjl[MAXJ];
            for (long t = 0; t < steps; t++) {
                int tau = (((phase * n + s) * g + tape[h]) * g + tape[h - 1]) * g + tape[h + 1];
                cnt[tau]++;
                if (phase == 1) { h += dir[s]; phase = 0; }
                else { int a = tape[h]; int idx = s * g + a; tape[h] = perm[idx] % g; s = perm[idx] / g; phase = 1; }
                if (h <= 2 || h >= W - 3) break;
                if (h > maxr) { maxr = h; if (nj < MAXJ) { tj[nj] = t + 1; memcpy(snap[nj], cnt, NT * sizeof(long)); nj++; } }
                if (h < minl) { minl = h; if (njl < MAXJ) { tjl[njl] = t + 1; memcpy(snapl[njl], cnt, NT * sizeof(long)); njl++; } }
            }
            int okr = nj >= 6 && (double)tj[nj-1]/tj[nj-2] > 1.8 && (double)tj[nj-1]/tj[nj-2] < 2.25;
            int okl = njl >= 6 && (double)tjl[njl-1]/tjl[njl-2] > 1.8 && (double)tjl[njl-1]/tjl[njl-2] < 2.25;
            if (okr && nj > bestn) { bestn = nj; memcpy(bt, tj, sizeof tj); memcpy(best, snap, MAXJ * sizeof *snap); }
            if (okl && njl > bestn) { bestn = njl; memcpy(bt, tjl, sizeof tjl); memcpy(best, snapl, MAXJ * sizeof *snapl); }
        }
        if (bestn < 10) continue;
        long late = 0, mid = 0;
        for (int j = bestn - 4; j < bestn - 1; j++) for (int tau = 0; tau < NT; tau++) {
            long v = best[j + 1][tau] - 2 * best[j][tau]; if (v < 0) v = -v; if (v > late) late = v; }
        for (int j = bestn - 8; j < bestn - 5; j++) for (int tau = 0; tau < NT; tau++) {
            long v = best[j + 1][tau] - 2 * best[j][tau]; if (v < 0) v = -v; if (v > mid) mid = v; }
        printf("RANK maxv_late=%ld maxv_mid=%ld ratio=%.3f levels=%d mask=%d beta=%s\n", late, mid,
               (double)bt[bestn - 1] / bt[bestn - 2], bestn, mask, b + 5);
        fflush(stdout);
    }
    printf("RTM_LEVELS_BATCH_DONE\n");
    return 0;
}
```

### `rtm_induce.c` (md5 053eb09f1c4203a5bc292281e8c8e5bb)

```c
/* rtm_induce.c -- for one machine and start (anchored zero tape), choose Y = the local types tau (phase, state,
 * head cell, two neighbours) whose level overhead v_j(tau) = n_{j+1}(tau) - 2 n_j(tau) vanishes on the last L
 * levels; then report (1) the maximal gap between consecutive Y-times, (2) Y-counts at the frontier times,
 * (3) for k = 1..K and window radius r, whether (window at Y-time) determines the induced index mod 2^k,
 *     counting conflicts (the orbit starts at t = 0, taken as phase 0 at every level).
 * Lane gq-nv-obstruct, 2026-09-18. MSI only.
 * Usage: rtm_induce n g mask beta start_state start_phase steps L K rmul radd  (radius r = rmul*k + radd)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, g, mask, dir[16], perm[128];
static long W = 1L << 23;

static void run(unsigned char *tape, int s0, int ph0, long steps, long *cnt, int NT, int *inY, long *ytimes,
                long *ny, long *tj, int *nj, long (*snap)[1024], int wantY, int K, int rmul, int radd,
                long *conf, long *ndist) {
    memset(tape, 0, W); long h = W / 2; tape[h] = 1; int s = s0, phase = ph0;
    long maxr = h, minl = h; int njr = 0, njl = 0; long tr[64], tl[64];
    static long (*snr)[1024], (*snl)[1024];
    if (!snr) { snr = malloc(64 * sizeof *snr); snl = malloc(64 * sizeof *snl); }
    memset(cnt, 0, NT * sizeof(long));
    long yi = 0, lastY = -1, maxgap = 0;
    /* phase tables: hash (window) -> phase for each k */
    const long HS = 1L << 21;
    static unsigned long long *hk; static int *hv;
    if (wantY && !hk) { hk = malloc(K * HS * sizeof *hk); hv = malloc(K * HS * sizeof *hv); }
    if (wantY) { memset(hk, 0, K * HS * sizeof *hk); for (int k = 0; k < K; k++) conf[k] = ndist[k] = 0; }
    for (long t = 0; t < steps; t++) {
        int tau = (((phase * n + s) * g + tape[h]) * g + tape[h - 1]) * g + tape[h + 1];
        cnt[tau]++;
        if (wantY && inY[tau]) {
            if (lastY >= 0 && t - lastY > maxgap) maxgap = t - lastY;
            lastY = t;
            for (int k = 1; k <= K; k++) {
                int r = rmul * k + radd;
                unsigned long long key = 1469598103934665603ULL ^ (unsigned long long)(phase * n + s);
                for (long c = h - r; c <= h + r; c++) key = (key ^ tape[c]) * 1099511628211ULL;
                key |= 1ULL;
                if (ndist[k - 1] > (HS / 10) * 7) continue;
                long slot = key % HS; unsigned long long *K1 = hk + (k - 1) * HS; int *V1 = hv + (k - 1) * HS;
                int ph = (int)(yi % (1L << k));
                while (K1[slot] && K1[slot] != key) slot = (slot + 1) % HS;
                if (!K1[slot]) { K1[slot] = key; V1[slot] = ph; ndist[k - 1]++; }
                else if (V1[slot] != ph) conf[k - 1]++;
            }
            yi++;
        }
        if (phase == 1) { h += dir[s]; phase = 0; }
        else { int a = tape[h]; int idx = s * g + a; tape[h] = perm[idx] % g; s = perm[idx] / g; phase = 1; }
        if (h <= 64 || h >= W - 64) break;
        if (h > maxr) { maxr = h; if (njr < 64) { tr[njr] = t + 1; memcpy(snr[njr], cnt, NT * sizeof(long)); if (wantY) ytimes[njr] = yi; njr++; } }
        if (h < minl) { minl = h; if (njl < 64) { tl[njl] = t + 1; memcpy(snl[njl], cnt, NT * sizeof(long)); if (wantY) ytimes[32 + njl] = yi; njl++; } }
    }
    if (njr >= njl) { *nj = njr; memcpy(tj, tr, sizeof tr); memcpy(snap, snr, 64 * sizeof *snr); }
    else { *nj = njl; memcpy(tj, tl, sizeof tl); memcpy(snap, snl, 64 * sizeof *snl); if (wantY) memmove(ytimes, ytimes + 32, 32 * sizeof(long)); }
    *ny = maxgap;
}

int main(int argc, char **argv) {
    n = atoi(argv[1]); g = atoi(argv[2]); mask = atoi(argv[3]); const char *bs = argv[4];
    int s0 = atoi(argv[5]), ph0 = atoi(argv[6]); long steps = atol(argv[7]); int L = atoi(argv[8]), K = atoi(argv[9]);
    int rmul = atoi(argv[10]), radd = atoi(argv[11]);
    const char *p = bs; for (int i = 0; i < n * g; i++) { perm[i] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; }
    for (int i = 0; i < n; i++) dir[i] = (mask >> i & 1) ? +1 : -1;
    int NT = 2 * n * g * g * g;
    unsigned char *tape = malloc(W); long *cnt = malloc(NT * sizeof(long));
    long (*snap)[1024] = malloc(64 * sizeof *snap); long tj[64]; int nj; long gap; long ytimes[64];
    int *inY = calloc(NT, sizeof(int)); long conf[32], nd[32];
    run(tape, s0, ph0, steps, cnt, NT, inY, ytimes, &gap, tj, &nj, snap, 0, K, rmul, radd, conf, nd);
    int ny = 0;
    for (int tau = 0; tau < NT; tau++) {
        if (snap[nj - 1][tau] == 0) continue;
        int ok = 1;
        for (int j = nj - 1 - L; j < nj - 1; j++) if (snap[j + 1][tau] - 2 * snap[j][tau] != 0) ok = 0;
        inY[tau] = ok; ny += ok;
    }
    printf("levels=%d  Y types=%d\n", nj, ny);
    run(tape, s0, ph0, steps, cnt, NT, inY, ytimes, &gap, tj, &nj, snap, 1, K, rmul, radd, conf, nd);
    printf("max gap between Y-times: %ld\nY-count at frontier times:", gap);
    for (int j = 0; j < nj && j < 32; j++) printf(" %ld", ytimes[j]); printf("\n");
    for (int k = 1; k <= K; k++) printf("k=%d radius=%d distinct=%ld conflicts=%ld\n", k, rmul * k + radd, nd[k - 1], conf[k - 1]);
    printf("RTM_INDUCE_DONE\n");
    return 0;
}
```

### `rtm_cert.c` (md5 46d061a070b4676baaa6e21ec61a5bd2)

```c
/* rtm_cert.c (from rtm_induce.c; prints the first conflicting pair per k as a certificate) -- for one machine and start (anchored zero tape), choose Y = the local types tau (phase, state,
 * head cell, two neighbours) whose level overhead v_j(tau) = n_{j+1}(tau) - 2 n_j(tau) vanishes on the last L
 * levels; then report (1) the maximal gap between consecutive Y-times, (2) Y-counts at the frontier times,
 * (3) for k = 1..K and window radius r, whether (window at Y-time) determines the induced index mod 2^k,
 *     counting conflicts (the orbit starts at t = 0, taken as phase 0 at every level).
 * Lane gq-nv-obstruct, 2026-09-18. MSI only.
 * Usage: rtm_induce n g mask beta start_state start_phase steps L K rmul radd  (radius r = rmul*k + radd)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, g, mask, dir[16], perm[128];
static long W = 1L << 23;

static void run(unsigned char *tape, int s0, int ph0, long steps, long *cnt, int NT, int *inY, long *ytimes,
                long *ny, long *tj, int *nj, long (*snap)[1024], int wantY, int K, int rmul, int radd,
                long *conf, long *ndist) {
    memset(tape, 0, W); long h = W / 2; tape[h] = 1; int s = s0, phase = ph0;
    long maxr = h, minl = h; int njr = 0, njl = 0; long tr[64], tl[64];
    static long (*snr)[1024], (*snl)[1024];
    if (!snr) { snr = malloc(64 * sizeof *snr); snl = malloc(64 * sizeof *snl); }
    memset(cnt, 0, NT * sizeof(long));
    long yi = 0, lastY = -1, maxgap = 0;
    /* phase tables: hash (window) -> phase for each k */
    #ifndef HSBITS
#define HSBITS 21
#endif
    const long HS = 1L << HSBITS;
    static unsigned long long *hk; static int *hv; static long *T1;
    if (wantY && !hk) { hk = malloc(K * HS * sizeof *hk); hv = malloc(K * HS * sizeof *hv); T1 = malloc(K * HS * sizeof *T1); }
    if (wantY) { memset(hk, 0, K * HS * sizeof *hk); for (int k = 0; k < K; k++) conf[k] = ndist[k] = 0; }
    for (long t = 0; t < steps; t++) {
        int tau = (((phase * n + s) * g + tape[h]) * g + tape[h - 1]) * g + tape[h + 1];
        cnt[tau]++;
        if (wantY && inY[tau]) {
            if (lastY >= 0 && t - lastY > maxgap) maxgap = t - lastY;
            lastY = t;
            for (int k = 1; k <= K; k++) {
                int r = rmul * k + radd;
                unsigned long long key = (1469598103934665603ULL ^ (unsigned long long)(phase * n + s + 101)) * 1099511628211ULL; unsigned long long key2 = (14695981039346656037ULL ^ (unsigned long long)(phase * n + s + 7)) * 6364136223846793005ULL;
                for (long c = h - r; c <= h + r; c++) { key = (key ^ (tape[c] + 1)) * 1099511628211ULL; key2 = (key2 ^ (tape[c] + 3)) * 6364136223846793005ULL + 1442695040888963407ULL; } key ^= key2 >> 1;
                key |= 1ULL;
                if (ndist[k - 1] > (HS / 10) * 7) continue;
                long slot = key % HS; unsigned long long *K1 = hk + (k - 1) * HS; int *V1 = hv + (k - 1) * HS;
                int ph = (int)(yi % (1L << k));
                while (K1[slot] && K1[slot] != key) slot = (slot + 1) % HS;
                if (!K1[slot]) { K1[slot] = key; V1[slot] = ph; T1[(k - 1) * HS + slot] = t; ndist[k - 1]++; }
                else if (V1[slot] != ph) { if (conf[k - 1] == 0) printf("CERT k=%d r=%d t1=%ld t2=%ld phase1=%d phase2=%d\n", k, r, T1[(k - 1) * HS + slot], t, V1[slot], ph); conf[k - 1]++; }
            }
            yi++;
        }
        if (phase == 1) { h += dir[s]; phase = 0; }
        else { int a = tape[h]; int idx = s * g + a; tape[h] = perm[idx] % g; s = perm[idx] / g; phase = 1; }
        if (h <= 64 || h >= W - 64) break;
        if (h > maxr) { maxr = h; if (njr < 64) { tr[njr] = t + 1; memcpy(snr[njr], cnt, NT * sizeof(long)); if (wantY) ytimes[njr] = yi; njr++; } }
        if (h < minl) { minl = h; if (njl < 64) { tl[njl] = t + 1; memcpy(snl[njl], cnt, NT * sizeof(long)); if (wantY) ytimes[32 + njl] = yi; njl++; } }
    }
    if (njr >= njl) { *nj = njr; memcpy(tj, tr, sizeof tr); memcpy(snap, snr, 64 * sizeof *snr); }
    else { *nj = njl; memcpy(tj, tl, sizeof tl); memcpy(snap, snl, 64 * sizeof *snl); if (wantY) memmove(ytimes, ytimes + 32, 32 * sizeof(long)); }
    *ny = maxgap;
}

int main(int argc, char **argv) {
    n = atoi(argv[1]); g = atoi(argv[2]); mask = atoi(argv[3]); const char *bs = argv[4];
    int s0 = atoi(argv[5]), ph0 = atoi(argv[6]); long steps = atol(argv[7]); int L = atoi(argv[8]), K = atoi(argv[9]);
    int rmul = atoi(argv[10]), radd = atoi(argv[11]);
    const char *p = bs; for (int i = 0; i < n * g; i++) { perm[i] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; }
    for (int i = 0; i < n; i++) dir[i] = (mask >> i & 1) ? +1 : -1;
    int NT = 2 * n * g * g * g;
    unsigned char *tape = malloc(W); long *cnt = malloc(NT * sizeof(long));
    long (*snap)[1024] = malloc(64 * sizeof *snap); long tj[64]; int nj; long gap; long ytimes[64];
    int *inY = calloc(NT, sizeof(int)); long conf[32], nd[32];
    run(tape, s0, ph0, steps, cnt, NT, inY, ytimes, &gap, tj, &nj, snap, 0, K, rmul, radd, conf, nd);
    int ny = 0;
    for (int tau = 0; tau < NT; tau++) {
        if (snap[nj - 1][tau] == 0) continue;
        int ok = 1;
        for (int j = nj - 1 - L; j < nj - 1; j++) if (snap[j + 1][tau] - 2 * snap[j][tau] != 0) ok = 0;
        inY[tau] = ok; ny += ok;
    }
    printf("levels=%d  Y types=%d\n", nj, ny);
    { FILE *yf = fopen("yt.txt", "w"); for (int tau = 0; tau < NT; tau++) if (inY[tau]) { int ph = tau / (n * g * g * g), rest = tau % (n * g * g * g); fprintf(yf, "%d %d %d %d %d\n", ph, rest / (g * g * g), (rest / (g * g)) % g, (rest / g) % g, rest % g); } fclose(yf); }
    run(tape, s0, ph0, steps, cnt, NT, inY, ytimes, &gap, tj, &nj, snap, 1, K, rmul, radd, conf, nd);
    printf("max gap between Y-times: %ld\nY-count at frontier times:", gap);
    for (int j = 0; j < nj && j < 32; j++) printf(" %ld", ytimes[j]); printf("\n");
    for (int k = 1; k <= K; k++) printf("k=%d radius=%d distinct=%ld conflicts=%ld\n", k, rmul * k + radd, nd[k - 1], conf[k - 1]);
    printf("RTM_INDUCE_DONE\n");
    return 0;
}
```

### `rtm_certcheck.c` (md5 790ed734669864659ae3f17c20b24cac)

```c
/* rtm_certcheck.c -- independent check of a phase-conflict certificate: re-simulate the machine from the
 * anchored zero tape and print, at times t1 and t2, the state and the cells within radius r of the head, and
 * the number of Y-times strictly before each (the induced index). Y is given as an explicit list of local types
 * (phase,state,head,left,right) read from a file "yt.txt" (one "ph st a l r" per line).
 * Lane gq-nv-obstruct, 2026-09-18. MSI only.
 * Usage: rtm_certcheck n g mask beta start_state start_phase t1 t2 r
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    int n = atoi(argv[1]), g = atoi(argv[2]), mask = atoi(argv[3]); const char *bs = argv[4];
    int s = atoi(argv[5]), phase = atoi(argv[6]); long t1 = atol(argv[7]), t2 = atol(argv[8]); int r = atoi(argv[9]);
    int perm[128]; const char *p = bs; for (int i = 0; i < n * g; i++) { perm[i] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; }
    int dir[16]; for (int i = 0; i < n; i++) dir[i] = (mask >> i & 1) ? +1 : -1;
    int NT = 2 * n * g * g * g; int *inY = calloc(NT, sizeof(int));
    FILE *f = fopen("yt.txt", "r"); int ph, st, a, l, rr, ny = 0;
    while (fscanf(f, "%d %d %d %d %d", &ph, &st, &a, &l, &rr) == 5) { inY[(((ph * n + st) * g + a) * g + l) * g + rr] = 1; ny++; }
    long W = 1L << 23; unsigned char *tape = calloc(W, 1); long h = W / 2; tape[h] = 1; long yi = 0;
    printf("Y types read: %d\n", ny);
    for (long t = 0; t <= t2; t++) {
        int tau = (((phase * n + s) * g + tape[h]) * g + tape[h - 1]) * g + tape[h + 1];
        if (t == t1 || t == t2) {
            printf("t=%ld inY=%d induced_index=%ld mod4=%ld mod8=%ld state=(%d,%d) window:", t, inY[tau], yi, yi % 4, yi % 8, phase, s);
            for (long c = h - r; c <= h + r; c++) printf("%d", tape[c]); printf("\n");
        }
        if (inY[tau]) yi++;
        if (phase == 1) { h += dir[s]; phase = 0; }
        else { int x = tape[h]; int idx = s * g + x; tape[h] = perm[idx] % g; s = perm[idx] / g; phase = 1; }
    }
    printf("RTM_CERTCHECK_DONE\n");
    return 0;
}
```

### `rtm_recur.c` (md5 6a6e4cb121c1d1db9bf82bfb9fbca3d0)

```c
/* rtm_recur.c -- return-time test for a continuous m-adic phase. Simulate from the anchored zero tape; take
 * the configuration y at the first Y-time >= t1 (Y = local types listed in yt.txt), and print every later
 * Y-time whose (state, cells within radius r) equals y's, with the induced index difference n and n mod m^j.
 * If U^n y -> y along returns with n not tending to 0 m-adically, U has no continuous m^j-th-root eigenvalue.
 * Lane gq-nv-obstruct, 2026-09-18. MSI only.
 * Usage: rtm_recur n g mask beta start_state start_phase steps t1 r m maxprint
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    int n = atoi(argv[1]), g = atoi(argv[2]), mask = atoi(argv[3]); const char *bs = argv[4];
    int s = atoi(argv[5]), phase = atoi(argv[6]); long steps = atol(argv[7]), t1 = atol(argv[8]);
    int r = atoi(argv[9]), m = atoi(argv[10]), maxp = atoi(argv[11]);
    int perm[128]; const char *p = bs; for (int i = 0; i < n * g; i++) { perm[i] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; }
    int dir[16]; for (int i = 0; i < n; i++) dir[i] = (mask >> i & 1) ? +1 : -1;
    int NT = 2 * n * g * g * g; int *inY = calloc(NT, sizeof(int));
    FILE *f = fopen("yt.txt", "r"); int ph, st, a, l, rr, ny = 0;
    while (fscanf(f, "%d %d %d %d %d", &ph, &st, &a, &l, &rr) == 5) { inY[(((ph * n + st) * g + a) * g + l) * g + rr] = 1; ny++; }
    long W = 1L << 24; unsigned char *tape = calloc(W, 1); long h = W / 2; tape[h] = 1; long yi = 0;
    unsigned char *ref = malloc(2 * r + 1); int refstate = -1; long refyi = -1, reft = -1; int printed = 0;
    printf("Y types: %d  radius %d  modulus base %d\n", ny, r, m);
    for (long t = 0; t < steps; t++) {
        int tau = (((phase * n + s) * g + tape[h]) * g + tape[h - 1]) * g + tape[h + 1];
        if (inY[tau]) {
            int cur = phase * n + s;
            if (refstate < 0 && t >= t1) { refstate = cur; memcpy(ref, tape + h - r, 2 * r + 1); refyi = yi; reft = t; printf("reference t=%ld induced=%ld\n", t, yi); }
            else if (refstate == cur && memcmp(ref, tape + h - r, 2 * r + 1) == 0) {
                long d = yi - refyi; long mj = 1; printf("return t=%ld n=%ld", t, d);
                for (int j = 1; j <= 6; j++) { mj *= m; printf(" mod%ld=%ld", mj, d % mj); }
                printf("\n");
                if (++printed >= maxp) break;
            }
            yi++;
        }
        if (phase == 1) { h += dir[s]; phase = 0; }
        else { int x = tape[h]; int idx = s * g + x; tape[h] = perm[idx] % g; s = perm[idx] / g; phase = 1; }
        if (h <= r + 2 || h >= W - r - 2) break;
    }
    printf("RTM_RECUR_DONE\n");
    return 0;
}
```
