# Layered orbit certificates for the lifted peeling links of VR(Z^n, d_1; r)

Proof route: `research/z7-rips-contractible-at-scales-11-13-15-17-proof.md`. It covers the orbit move (Lemma O) and
membership in `H_j C` (Lemma P). The reduction to `Lmax_k` is §1–§3 of
`research/z7-rips-contractible-at-scale-10-proof.md`.

Both programs are single-threaded C++17. Build each with `g++ -O2 -o <name> <name>.cpp`.

## overv.cpp: verifier

Usage: `./overv k r cert [-x expanded]`. It reads lines of the form `D x | w`.

For each line, with `j` the layer of `x`, it checks every hypothesis of Lemma O:
- membership of `x` and `w`, and the distance `d(x, w)`;
- `w ∈ hull(0, x, e_k)`, and `layer(w) ≥ j`;
- explicit enumeration of `H_j x` and `H_j w`: the two orbits are disjoint and present;
- an exhaustive search over the ball for `z ∈ H_j C` with `d(z, x) ≤ r < d(z, w)`.

It then deletes the whole orbit. The run succeeds only if exactly `{e_k}` remains.

`-x` writes the expanded point-level (D) moves `D hx | hw`.

Memory is one bit per point of the `l^1` ball of radius `r` in `Z^k`. At `(7, 17)` that is about 1.9 MB.

## lcs2.cpp: generator (not part of the proof)

Usage: `./lcs2 k r certfile [maxCand]`. It never enumerates points. It works on orbit representatives
`x_0 ≥ … ≥ x_{j−1} ≥ 0`, `x_j ≥ 1` and processes the levels `m = r, …, 2`.

A candidate `w` must satisfy:
- `w ∈ hull(0, x, e_k)`;
- `layer(w) ≥ j`;
- `|w| ≤ m − 1`;
- `d(x, w) ≤ r`.

Candidates are sorted by `|2|w| − r|`, then by `d(x, w)`.

Hypothesis 4 is tested against a superset of `H_j C`, made of two parts:
- **(a)** all `z` with `|z| ≤ M` and (`z ≻ 0` or `layer(z) < j`). This is an exact dynamic program over coordinates,
  with state (started, `|z|`, `d(z, x)`) mapped to the maximum of `d(z, w)`.
- **(b)** `H_P y` for each alive orbit `y` of larger or equal norm, where `P = max(layer(y), j)`. This is an exact
  dynamic program over signed assignments of the coordinates of `y`.

The run at each level has three steps:
1. The level test: (a) with `M = m`, plus (b) against the deferred orbits.
2. Greedy passes over the rest: (a) with `M = m − 1`, plus (b) against the deferred orbits and the rest.
3. The leftovers are deferred. Greedy passes over the deferred orbits then try dominators of norm `≤ m − 1`.

Final lines are `e_i | e_k`. The runs are deterministic: each was repeated and gave a byte-identical file.

## Files

- `certs/c<k>-<r>.txt.gz`: orbit certificates for `k = 2..7` and `r = 11, 13, 15, 17`. Together they take 296 KB.
- `results.txt`: the generator summaries, then the verifier output for all 24 pairs, all `VERIFIED: ends at {e_k}`.
  The slowest pair is `(7, 17)`: 9.26·10^9 search nodes, 189 s.
- `negative-controls.txt`: four one-line corruptions of `c6-13`, each rejected at the expected line.

## n = 8

`lcs2` stalls at `k = 8` for every `8 ≤ r ≤ 14` tried. An exact orbit greedy with a point bitmap (not included) also
stalls at `r = 11..13`.

While all lower norms are still present, the stuck orbits have no `H_j`-equivariant dominator. Every candidate `w` is
blocked by `H_j` images, with negative entries, of positive lower-layer points of smaller norm.

For example, at `r = 8` take `x = (2,2,1,1,1,1,0,0)`, with `j = 5`. Its best candidate `(1,1,1,1,1,1,0,0)` has 347
blockers. The first is `z = (2,2,0,0,−3,0,0,0)`, the `H_5` image of `(2,2,0,0,3,0,0,0)`, and every other candidate
has more.

For the image `hx = (2,2,1,1,−1,1,0,0)`, the real point `(2,2,0,0,3,0,0,0)` blocks `hw = (1,1,1,1,−1,1,0,0)`. It does
not block `(1,1,1,1,0,1,0,0)`. So the natural dominators of different points of one orbit are not images of each
other. `n = 8` needs moves that split orbits, or a point-level residual.
