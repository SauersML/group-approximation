---
rg: 2
id: nv-finite-kazhdan-subgroups-via-af-by-zn
kind: route
title: "nV sits in the full group of an AF-by-Z^n groupoid, so the AF-by-Z^k finiteness statement gives it directly"
target: kazhdan-subgroups-of-brin-thompson-groups-are-finite
requires:
  - brick-groupoid-has-zn-cocycle-with-af-kernel
  - af-by-zk-full-groups-have-finite-kazhdan-subgroups
---

Let `n ≥ 1` and let `K ≤ nV` have property (T).

1. By `brick-groupoid-has-zn-cocycle-with-af-kernel`, the brick groupoid `G_2^n` is
   second countable, Hausdorff, ample with Cantor unit space, minimal and effective, it
   carries the continuous cocycle `c^{(n)} : G_2^n → Z^n` with AF kernel `R_2^n`, and
   `nV ≤ [[G_2^n]]`. So `G_2^n` is AF-by-`Z^n` in the sense of
   `af-by-zk-full-groups-have-finite-kazhdan-subgroups`.
2. `K` is then a property (T) subgroup of `[[G_2^n]]`, so (S_n) makes it finite.

This is a **one-hole route**: the only open input is the general statement (S_k), and
that statement can fail on its own, on a groupoid unrelated to `nV`
(see "Ways it can fail on its own" there).

**Independence from the other routes to the same target.** The recorded routes go through
the Haagerup property of `nV` (`brin-thompson-nv-lack-property-t-from-a-t-menability` and
the triangular split), which is strictly stronger and is blocked by the cocycle class
kills recorded on `brin-thompson-groups-nv-are-a-t-menable`. This route asks only for the
finiteness of Kazhdan subgroups and it is stated at the groupoid level, so none of the
cnd-function obstructions (extractable cocycles, gap-class vanishing `H^1`, integrated
measured walls, brick-size functionals) applies to it: they all constrain functions on
`nV`, while (S_k) constrains groupoids.

**Calibration.** For `n = 1` the conclusion is already established
(`thompson-v-has-haagerup-property`), and the hypothesis holds, so the route is
consistent there. The `k = 1` case of (S_k) is **not** established in general
(corrected 2026-09-18, referee lens 3): `input-encoded-sft-groupoid-hosts-are-not-universal`
item 2 covers irreducible one-sided SFT groupoids only, a proper subclass, and every free
minimal Cantor `Z^k`-system also satisfies the hypothesis list of (S_k). So the single open
input of this route is genuinely open even for `k = 1`, and it carries the degenerate
members recorded under "Calibration" in
`af-by-zk-full-groups-have-finite-kazhdan-subgroups`. The route itself is unaffected: it
asserts only that (S_n) implies the target.
