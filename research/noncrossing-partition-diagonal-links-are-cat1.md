---
rg: 2
id: noncrossing-partition-diagonal-links-are-cat1
kind: claim
title: For every n the diagonal link of the noncrossing partition complex is CAT(1)
distinct_from:
  every-braid-group-is-cat0: that claim is about braid groups acting on CAT(0) spaces; this one is the curvature statement about the complexes |NCP_n| that implies it (Brady–McCammond's conjecture)
---

For every `n >= 3`, the diagonal link `X_n = LK(e_01, |NCP_n|)` of the orthoscheme complex of the
noncrossing-partition lattice, with the spherical orthoscheme metric, is CAT(1). By Brady–McCammond this makes every
`|NCP_n|` CAT(0) and every braid group CAT(0) (route `every-braid-group-is-cat0-via-diagonal-links`); Brady–McCammond
conjecture that braid groups are CAT(0) (their Conjecture 8.4, as cited by HKS).

Known: `n = 3, 4` directly (HKS Remark 4.1), `n = 5` (Brady–McCammond, computer-assisted; HKS Corollary 4.11 by hand),
`n = 6` (HKS Theorem 4.17), `n = 7` (Jeong, arXiv:2009.09350, preprint; an exhaustive search of this lane agrees
with his Theorem 1). Open from `n = 8`.

## Attempts

- **Turning-face search (Theorem R).** In
  `research/artifacts/zp-braid-cat0-turning-face-reduction-2026-09-13.md`: if `X_m` is CAT(1) for `m < n` and no
  chain `F` of `NCP_n` has both `F` and its Kreweras dual satisfying conditions I, II, III', IV, then `X_n` is CAT(1)
  (route `diagonal-links-cat1-from-turning-face-conditions`). An exhaustive search gives no such chain for
  `n = 5, 6, 7`, and 22268 at `n = 8`, e.g. `({18} < {18, 26})`, checked by hand in
  `some-noncrossing-chain-satisfies-turning-face-conditions`. So the method as stated cannot reach `n = 8`.
- **Weakening IV with more universal pairs.** The shrinking argument of HKS Theorem 4.17 needs only some pair of
  opposite universal vertices `(v, w)` with apartments containing `F, v, w` and `C, v, w`. Opposite universal pairs
  are two cyclic intervals covering the circle and meeting in one point, and apartments are noncrossing spanning trees
  (HKS Proposition 4.4). The search with all `n(n-2)` such pairs (Theorem R_all in
  `research/artifacts/zp-braid-cat0-pivot-obstructions-2026-09-16.md`) leaves 17212 of the 22268 candidates at `n = 8`
  (`experiments/zaremsky-3-06-braid-groups-cat0-frontier-2026-09-16/out_n8.txt`), so this weakening does not reach `n = 8` either.
- **Using the loop geometry.** The midpoint `y` can be replaced by any point splitting the loop into two arcs shorter
  than `π`, and any turning point can serve as `x`. A condition quantified over those choices is weaker than IV and
  could exclude the remaining candidates, but it depends on the loop, not only on `F`.
- **Refuting through the rotation pair (dead).** If `X_n` is CAT(1) then `d_X(P, ρP) >= π` for `P = {12, 34, ...}`:
  `ρ` swaps `P` and `ρP` and fixes no point of `X_n`, so it would fix the midpoint of the unique geodesic. A path
  of length `< π` would therefore refute the claim. Paths whose consecutive pivot faces share a noncrossing spanning
  tree all stay above `π`. Vertex pivots give `1.0412π` at `n = 8`, and a barycentric grid on faces gives `1.0348π`.
  Continuous optimisation gives `1.0312π` at `n = 8` (`P → [{34,56} < {1278,34,56}] → [{18} < {18,234567}] → ρP`),
  `1.0225π` at `n = 10` and `1.0170π` at `n = 12` for the same two-face pattern, and a local minimum of `1.0432π`
  at `n = 6`. The gain over one pivot shrinks with `n`: the excess is `0.76, 0.84, 0.87` of the one-pivot excess.
  These are upper bounds only, found by numerical search, and are reproducible with
  `experiments/braid-cat0-pivot-paths-2026-09-17/`.
- **Refuting through involution midpoints (dead).** This generalises the rotation pair to the whole isometry group
  `<ρ, r, Φ>` (order `4n`, with `Φ` the Kreweras isometry). Suppose `X_n` is CAT(1), `g` is an isometry, `g²z = z`
  and `d_X(z, gz) < π`. Then the midpoint of `[z, gz]` is `g`-fixed and lies within `π/2` of `z`. So a point `z`
  with `d_B(z, Fix g) >= π/2` and a path from `z` to `gz` shorter than `π` refutes the claim. For vertices `z` the
  far condition is finite:
  - if `g` preserves order, `cos d_B(z, v) <= 0` for every `g`-fixed vertex `v`;
  - if `g` reverses order, `cos d_B(z, v) + cos d_B(z, gv) <= 0` whenever `v < gv`.

  The exhaustive run over all `g` and vertices `z`, with tree-sharing vertex paths as upper bounds, never gets below
  `π` for `n = 4, …, 7`. The minimum is exactly `π`, at antipodal pairs.

  At `n = 8` there are 4816 far pairs and still no refutation. The 28 far non-antipodal pairs form two families.
  The first is `P ↔ ρP` and its images under `Φ` (`1.0412π`). The second is new:
  `{123,48,567} ↔ {178,26,345}` with `g = ρ²`, `d_B = 0.6310π`. Its paths give `1.0625π` through vertices,
  `1.0489π` on a face grid, and `1.0481π` continuously (through `{23,56}` and `[{2356} < {178,23456}]`). What
  remains open is the case of non-vertex `z`. Reproducible with `experiments/braid-cat0-involution-midpoint-2026-09-17/`.
