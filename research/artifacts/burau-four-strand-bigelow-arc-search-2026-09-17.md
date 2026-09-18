# Exhaustive search for Bigelow arc pairs on D_4 with at most 250 crossings

Lane: sw-094 (flagship-2026-09-17), compute-scout on
`zaremsky-3-05-four-strand-burau-faithful`. The scripts are in
`experiments/burau-arc-orbit-search-2026-09-17/`.

## What is computed

- **Setup.**
  - `D_4` is the disk with punctures `q_1, ..., q_4` and a basepoint `p_0` on the boundary.
  - `beta_0` is the straight arc from `p_0` to `q_3`.
  - For an embedded arc `alpha` from `q_1` to `q_2` that is transverse to `beta_0`, Bigelow's pairing is `<alpha, beta_0> = sum_k eps_k t^{e_k}`, where:
    - `k` runs over the crossings;
    - `eps_k` is the sign of crossing `k`;
    - the exponent changes by `±(number of punctures enclosed)` between consecutive crossings (Bigelow, GT 3 (1999), Remark before Figure 3).
- **Search space.** The programs enumerate every configuration `(alpha, beta_0)` in minimal position with `m = i(alpha, beta_0)` crossings, for `1 <= m <= M`.
  - Configurations are taken up to homeomorphisms of `D_4` that preserve `beta_0`.
  - Each configuration is recorded as a crossing sequence in the disk `D'` obtained by cutting `D_4` along `beta_0`.
- **Output.**
  - A **leaf** is a complete configuration.
  - A **hit** is a leaf whose pairing polynomial is identically 0.

## Encoding (as implemented in `arcfast2.c`)

- **The boundary of `D'`.** Read in order, the boundary circle is `J | L | N | R | J`:
  - `J` is the arc of `∂D_4` containing both copies of `p_0`;
  - `L` is the left copy of `beta_0`, with heights ascending;
  - `N` is the notch at `q_3`;
  - `R` is the right copy, with heights descending.
- **Crossings.** Crossing `k` arrives at height `h_k` on one copy and leaves from the other copy at the same height. The pieces of `alpha` between consecutive crossings are pairwise disjoint chords of `D'`.
- **Marks.** A mark is a puncture of `D_4` slid to a gap of the boundary of `D'`:
  - `x_0` is `q_1`, slid along the first piece of `alpha` to the arrival point of crossing 1;
  - `y` is `q_2`, slid along the last piece to the departure point of crossing `m`;
  - `q_4` is slid inside its region to a boundary gap, or to `J`. At `J` it is never enclosed.
- **Minimal position.** Every chord must enclose at least one mark, or `N`.
  - A same-side chord that encloses nothing is exactly an innermost bigon.
  - An L–R chord always encloses `N`.
- **Exponent change.** Along a chord from `cur` to `arr` the exponent changes by `+k` if `arr` precedes `cur` in the boundary order, and by `-k` otherwise. Here `k` is the number of marks enclosed, plus 1 if `N` is enclosed.
  - The sign is `+1` for arrival on `L` and `-1` for arrival on `R`.
  - WLOG crossing 1 arrives on `L`: reflecting in the line of `beta_0` sends `p(t)` to `±t^j p(t^{-1})`. That preserves the zero test and the crossing number.
- **Enumeration.**
  - The boundary is a doubly linked list.
  - At each step the arrival point runs over all gaps of the region containing `cur`. The walk jumps over nested chords, so crossing chords are impossible by construction.
  - The top-level loop runs over three things, giving 28 "starts" for `n = 4`:
    - the side of `q_4` (`J`, `L` or `R`);
    - the height order of the objects `x_0`, `y` and `q_4`;
    - the side of `y`.
- **Pruning.** Each crossing changes one coefficient by `±1`. So a partial configuration with `d` crossings whose coefficient `l^1`-norm exceeds `M - d` cannot finish as a hit with at most `M` crossings. `arcfast2.c` applies this test once before each insertion and once on entry to each node.

## Controls (files in `experiments/burau-arc-orbit-search-2026-09-17/runs/`)

1. **Two independent implementations agree.**
   - The implementations:
     - `arcpairs_np.c` uses a rank array, tests chord crossings explicitly against every earlier chord, and handles one `m` at a time;
     - `arcfast2.c` uses the linked list and walks regions.
   - With pruning off (`NOPRUNE=1` and `noprune=1`), the leaf counts agree exactly:
     - for `n = 4`: `m = 2, 4, 6, 8, 10, 12` give `16, 74, 178, 442, 794, 1226`;
     - for `n = 6`, `m = 8`: `759602` leaves and `60` hits.
   - Files: `ctl_arcpairs_n4_m12_noprune.txt`, `ctl_arcfast2_n4_M14_noprune.txt`, `ctl_arcpairs_n6_m8_noprune.txt`, `ctl_arcfast2_n6_M8_noprune.txt`.
2. **`n = 3` gives no cancellation.**
   - For `n = 3` and every `m <= 40`, every leaf has `||p||_1 = m` and `|p(-1)| = m`, so no pairing ever cancels. File: `ctl_arcmin_n3_M40_noprune.txt`.
   - `arcmin.c` is `arcfast.c` plus these statistics.
   - A wrong exponent or sign rule would show up here as cancellation.
   - The pruned `n = 3` run to `M = 80` finds 0 hits, consistent with the faithfulness of Burau on `B_3`. File: `ctl_arcfast2_n3_M80.txt`.
3. **Positive control at `n = 6`.**
   - `n = 6` has hits at `m = 8`: 60 leaves, which are 3 crossing sequences over the placements of the free punctures. File: `ctl_arcfast2_n6_M8_hits.txt`.
   - Burau is unfaithful for `n = 6` (Long–Paton, Bigelow Figure 4), so the search does find vanishing pairs where they exist.

## Main run

Command: `nice -n 10 timeout 1200 ./arcfast2 4 250 0 5 $s $((s+1))` for `s = 0..27`, each run single-threaded. Output: `runs/n4_M250_s$s.txt`; the log is `runs/n4_M250_log.txt`.

| start | nodes | hits | exit | secs |
|---|---|---|---|---|
| 0 | 7999 | 0 | 0 | 0 |
| 1 | 961870 | 0 | 0 | 0 |
| 2 | 7999 | 0 | 0 | 1 |
| 3 | 961287 | 0 | 0 | 0 |
| 4 | 333499 | 0 | 0 | 0 |
| 5 | 2142068778 | 0 | 0 | 520 |
| 6 | 333499 | 0 | 0 | 1 |
| 7 | 1129669988 | 0 | 0 | 509 |
| 8 | 15749 | 0 | 0 | 0 |
| 9 | 1316891847 | 0 | 0 | 688 |
| 10 | 15749 | 0 | 0 | 0 |
| 11 | 1116055463 | 0 | 0 | 373 |
| 12 | 333499 | 0 | 0 | 0 |
| 13 | 1318758248 | 0 | 0 | 323 |
| 14 | 333499 | 0 | 0 | 0 |
| 15 | 2129417470 | 0 | 0 | 441 |
| 16 | 1129669988 | 0 | 0 | 232 |
| 17 | 1365181278 | 0 | 0 | 293 |
| 18 | 2142068778 | 0 | 0 | 492 |
| 19 | 1365181278 | 0 | 0 | 326 |
| 20 | 1116055463 | 0 | 0 | 234 |
| 21 | 2170161072 | 0 | 0 | 412 |
| 22 | 1316891847 | 0 | 0 | 251 |
| 23 | 2170161072 | 0 | 0 | 469 |
| 24 | 2129417470 | 0 | 0 | 437 |
| 25 | 1169469310 | 0 | 0 | 235 |
| 26 | 1318758248 | 0 | 0 | 228 |
| 27 | 1169469310 | 0 | 0 | 214 |

Total: 27718651557 search nodes over 28 starts, all exit 0, all `total_hits=0`. Wall time 6679 s. Node counts come in pairs of equal size, for example starts 5 and 18. Each start and its mirror image are searched separately, and duplicates are harmless.

Result: **0 hits** for every `m <= 250`.

## Growth

- For the heaviest start (`s = 5`), node counts were:
  - `M = 50`: `4.63e5`
  - `M = 100`: `1.69e7`
  - `M = 150`: `1.43e8`
  - `M = 250`: `2.14e9`
- This fits `~M^{5.3}`.
- Leaves grow like `~0.73 m^3` per `m`.
- The minimum `l^1`-norm over leaves stays at most 7 for `m <= 26`. The near-misses are spiral families whose blocks are `±t^a(1 - t + t^2)`, so no norm-growth obstruction is visible.
- `M = 500`, the bound Bigelow asserts without code, would cost about 40 times the `M = 250` run with this method.

## Reproduction

`sh experiments/burau-arc-orbit-search-2026-09-17/run.sh`. It needs only `gcc`, no libraries.
