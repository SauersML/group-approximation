# Self-blocking sets for lifted domination certificates

This directory supports `research/z8-rips-lifted-domination-certificates-fail-at-scale-8-proof.md`. Notation is
that of `research/z7-rips-contractible-at-scale-10-proof.md`, §3:
- `Lmax_k = { x ∈ Z^k : |x|_1 ≤ r, x ≻ 0 }`;
- `E = e_k`;
- a (D) move `x | w` needs `w ∈ C ∩ hull(0, x, E)`, `w ≠ x` and `N[x] ∩ C ⊆ N[w]`.

A set `K ⊆ Lmax_k` is **self-blocking** if `e_k ∈ K` and every `x ∈ K ∖ {e_k}` and every `w ∈ hull(0, x, E) ∩ Lmax_k`
with `w ≠ x` have a blocker `z ∈ K` with `d(z, x) ≤ r < d(z, w)`. A self-blocking `K ≠ {e_k}` rules out every
(D)-only certificate at `(k, r)` (Lemma B of the route).

## Files

| File | What it is |
|---|---|
| `kchk.cpp` | Independent checker. `./kchk k r Kfile` checks that `K` is self-blocking, using pairwise distances only. |
| `gfp.cpp` | Greatest fixed point. `./gfp k r [outfile] [startfile]` iterates the removal operator. |
| `cores/K{6_6,7_7,7_8,7_9,8_8}.txt.gz` | The self-blocking sets. They are sorted with `LC_ALL=C sort`, one point per line. |
| `results.txt` | The `gfp` logs, the `kchk` outputs and the controls. |
| `ilv4.cpp` | Interleaved lifted (D) greedy that produced the first stage of `K8_8`. |
| `hyb.cpp` | Hybrid orbit/point generator: the dead end at `(8, 8)`, below. |
| `vcert2.cpp` | Point-level certificate verifier, used on the `hyb` output. |

### `kchk`

`kchk` does no search over the ball, and it shares no code with the search programs. It checks:
- every point is in `Lmax_k`, there are no duplicates, `e_k ∈ K`, and `|K| > 1`;
- for each `x ∈ K ∖ {e_k}`, it lists `N[x] ∩ K` by scanning `K`;
- it enumerates every `w` in the integer box `hull(0, x, E)` with `|w| ≤ r`, `w ≻ 0` and `w ≠ x`;
- for each such `w`, it finds a `z` in that list with `d(z, w) > r`.

It prints `OBSTRUCTION VERIFIED`, or the first failing pair `x`, `w`. The number of distance tests depends on the
order of the file. The file order also fixes the counts quoted in the route.

### `gfp`

`gfp` starts from `Lmax_k`, or from a start file with `e_k` always added. It removes in place every `x` that has a
dominator `w ∈ hull(0, x, E) ∩ Lmax_k ∖ {x}` with `N[x] ∩ K ⊆ N[w]`. Here `w` need not lie in `K`.
- It uses exact pruned DFS over the ball for blockers.
- Each blocker found is cached by rank and re-checked for presence before reuse.
- It first checks that its dense ranking of the `l^1` ball is a bijection.

Starting from a subset is sound for the obstruction, because only the final self-blocking property matters, and
`kchk` re-checks that property. Starting from `Lmax_k` gives the greatest self-blocking set `K*(k, r)`.

## How `K8_8` was found

1. `./ilv4 8 8 c8_8.txt - a8_8.txt 1100 400` runs the interleaved (D) greedy on `Lmax_8` (132,864 points).
   - It makes 56,064 phase-A moves and 36,358 greedy (D) moves.
   - It is stuck with 40,442 alive points after 3 passes, in 33 s.
2. `kcore 8 8 a8_8.txt k8_8.txt kc8_8.txt 64 1100` works on that set with (D) moves plus link-collapse (K) moves.
   - It makes 11,075 (D) moves and 13,253 (K) moves.
   - It is stuck with 16,114 points after 6 passes, in 422 s.
   - `kcore.cpp` is the one in `experiments/zn-rips-lifted-interleaved-2026-09-18/`, byte-identical.
3. `./gfp 8 8 K8_8.txt k8_8.txt` removes 0 points in one pass (267 s). So the stuck set is already self-blocking.
   `cores/K8_8.txt.gz` is this set, sorted. The md5 of the unzipped file is `a3ca6240392e6716ea8629d10acea995`.

The full iteration from `Lmax_8` does not finish in the 20-minute budget. After pass 1 (850 s) it had 40,496 points
left. It is not needed, since any self-blocking set suffices.

Step 2 is not part of the proof. Its (K) moves removed many points of `a8_8.txt` and then got stuck exactly on a
self-blocking set. That happened for one greedy with at most 64 bad points per link. So the question whether (K)
moves close `(8, 8)` is still open.

## Dead end: hybrid orbit/point certificates at `(8, 8)`

`./hyb 8 8 h8_8.txt 400 1100` works level by level for `m = 8, 7, …`.
- It first tries equivariant orbit moves, as in Lemma O of `z7-rips-contractible-at-scales-11-13-15-17-proof`.
- It then tries point moves on the alive points of a deferred orbit.

It timed out after 1,100 s. By then it had made 212 orbit moves and 6,378 point moves, giving 62,442 point-level
lines, and 70,422 points were left. The deferred orbits included `[2 2 1 1 1 1 0 0]`, `[3 1 1 1 1 1 0 0]` and
`[2 1 1 1 1 2 0 0]`.

The point-level verifier (`./vcert2 8 8 h8_8.txt`) accepted all 62,442 moves and reported that the end set is not
`{e_8}`. Lemma B shows that no run of this kind can finish: every orbit move expands to (D) moves, and no sequence of
(D) moves can delete a point of `K8_8`.

## Controls

These are in `results.txt`.
- `K8_8` at `r = 9` fails.
- `K8_8` minus `e_8` fails.
- `K8_8` plus the non-positive point `−e_8` fails.
- `K6_6` at `r = 7` fails.
- `K6_6` thinned to 707 points fails.

Self-blocking is not preserved under taking subsets, but it can survive thinning. Deleting every fifth line of the
sorted `K8_8` (keeping `e_8`) leaves 12,891 points that are still self-blocking. So `K8_8` is not a minimal
obstruction. That thinned set is listed as a data point, not as a control.
