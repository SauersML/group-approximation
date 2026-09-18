---
rg: 2
id: r-mod-k-partition-posets-truncations-highly-connected
kind: claim
title: Partitions of n points into blocks of size r mod k with at least L blocks form a poset whose connectivity grows linearly in n, for every r
distinct_from:
  one-mod-k-partition-posets-are-highly-connected: that is the pure case r = 1 mod k, where the poset has a top and a bottom and rank selection applies; this is every residue r, where the poset is nonpure (for gcd(r,k) strictly between 1 and k), has no bottom, and is truncated by block count rather than rank-selected.
---

**ESTABLISHED by citation plus a short derivation (route `r-mod-k-partition-posets-truncations-highly-connected-proof`;
unreviewed).**

Fix integers `k >= 1` and `r_0` with `1 <= r_0 <= k`. Put `g = gcd(r_0, k)`, `k' = k/g`, and
`T = {r_0, r_0 + k, r_0 + 2k, ...}`, the positive integers `≡ r_0 mod k`.

For a finite set `S`, let `Π^T(S)` be the set of partitions of `S` all of whose block sizes lie in `T`, ordered by
refinement. For `n in T` and `L >= 2`, let `Z(n, L) ⊆ Π^T([n])` be the partitions with at least `L` blocks.

1. **Covers.** If `y` is coarser than `x` in `Π^T(S)`, every block of `y` is a union of `j ≡ 1 mod k'` blocks of `x`.
   `y` covers `x` if and only if it merges exactly `k' + 1` blocks of `x` into one. When `|S| in T`, every member of
   `Π^T(S)` has `≡ 1 mod k'` blocks, and every maximal chain from `x` to the one-block partition has
   `(b(x) − 1)/k'` covers, where `b(x)` is the number of blocks.
2. **Atoms.** Every `t in T` with `t >= (k' + 1) r_0` is a sum of `k' + 1` elements of `T`. So every minimal element
   of `Π^T(S)` has fewer than `(k' + 1) r_0` points in each block, hence more than `|S| / ((k' + 1) r_0)` blocks.
3. **Whole poset.** For `s in T`, the order complex of `Π^T([s])` minus its one-block partition is
   `κ(s)`-connected, where `κ(s) = ⌊s / c⌋ − 3` and `c = (k' + 1) r_0 k'`.
4. **Truncation.** The order complex of `Z(n, L)` is `κ(⌈n/(L − 1)⌉)`-connected. In particular, for fixed `L` its
   connectivity tends to infinity as `n -> ∞` in `T`.

**Cases.**

- `r_0 = 1` (so `g = 1`, `k' = k`): the `1 mod k` partition lattice, which is pure.
- `r_0 = k` (so `g = k`, `k' = 1`): the `k`-divisible partition lattice, which is pure.
- `1 < g < k`: the poset is nonpure. For example, with `k = 6` and `r_0 = 4` a block of size `10` has no refinement
  into blocks of sizes in `T = {4, 10, 16, ...}`. So both `10 | 4 | 4 | 4 | 4 | ...` and `4 | 4 | ... | 4` occur as
  minimal elements.

The only external input is Wachs's shellability theorem for restricted block size partition posets (Wachs, *Whitney
homology of semipure shellable posets*, J. Algebraic Combin. 9 (1999), Theorem 3.14 with Example 3.8). It is read in
full text in the route.

**Use.** `rover-nekrashevych-vdr-sigma-full-via-type-r-partitions` uses item 4 to show that the poset of partitions
of `C_r` into clopen sets of type `r` is contractible. That poset is not directed when `gcd(r, d − 1) > 1`.

## Attempts

- 2026-09-18 (w6-101): proved from Wachs 1999 (nonpure shellability via a recursive atom ordering), the
  Björner–Wachs wedge-of-spheres theorem for nonpure shellable complexes, Quillen's join formula for products minus a
  top, and vertex removal in block-count order. See the route.
