---
rg: 2
id: z8-rips-scale-10-reduces-to-top-shell-link-collapses
kind: claim
title: At scale 10 the k = 8 lifted certificate for Z^8 reduces to deleting an explicit 18,816-point top-shell set by link collapses
distinct_from:
  zn-rips-contractible-at-every-scale-r-ge-n: that is Zaremsky's conjecture; this is a verified reduction of the single case n = 8, r = 10 to one explicit finite deletion problem, and does not settle that case
  z8-rips-contractible-at-scale-8: that certifies (8, 8) completely; this is the scale r = 10, where only the domination parts of the certificate are complete
  z8-rips-lifted-domination-certificates-fail-at-scale-8: that proves domination moves alone cannot certify (8, 8); this measures where domination stalls at (8, 10) and shows that domination finishes the job once one explicit set is gone
  z7-rips-contractible-at-scale-10: that is dimension 7 at the same scale, whose k = 2..7 certificates are reused here; this is the missing k = 8 certificate at r = 10, reduced but not finished
---

Work in the lifted reduction of `z7-rips-contractible-at-scale-10-proof` (§3), with `k = 8`, `r = 10`:
- `Lmax_8 = { x ∈ Z^8 : |x|_1 ≤ 10, x ≻ 0 }`, where `x ≻ 0` means the last nonzero coordinate is positive. It has
  628,232 points.
- `E = e_8`, and `N[v]` is the closed `d_1`-ball of radius 10.
- A **(D) move** `x | w` deletes `x` from the current set `C` when `x, w ∈ C`, `w ≠ x`, `w ∈ hull(0, x, E)` and
  `N[x] ∩ C ⊆ N[w]`. A **(K) move** is the link-collapse move of `z8-rips-contractible-at-scale-8-proof` (§1).

Let `O ⊆ Lmax_8` be the 186,146-point set in `experiments/zn-rips-link-collapse-scale-10-2026-09-18/sets/O-8-10.txt.gz`.
Let `T` be the set of points `x ∈ Lmax_8` with all three of the following:
- `|x|_1 = 10`;
- `x_8 = 0`;
- the nonzero `|x_i|`, as a multiset, form a partition of 10 into 7 parts, or the partition `(3, 2, 2, 1, 1, 1)`.

There are three 7-part partitions of 10: `(4, 1^6)`, `(3, 2, 1^5)` and `(2^3, 1^4)`.

**Claim.**
1. A sequence of 442,086 (D) moves takes `C = Lmax_8` to `C = O`.
2. `T ⊆ O` and `|T| = 18,816`. Also, `T = { x ∈ O : |x|_1 = 10, x_8 = 0 }`.
3. A sequence of 167,329 (D) moves takes `C = O ∖ T` to `C = {e_8}`.

**Consequence.** Suppose some sequence of lifted moves takes `C = O` to `C = O ∖ T`. That is, it deletes exactly
the points of `T`, in some order, by (D) and (K) moves. Then (1), that sequence and (3) together form a lifted
certificate on `Lmax_8` at `r = 10` that ends at `{e_8}`. The certificates for `k = 2, …, 7` at `r = 10` are those of
`z7-rips-contractible-at-scale-10-proof`. So the theorem there gives that `VR(Z^8, d_1; 10)` is contractible.

So the whole of `(8, 10)` is now one explicit deletion problem: remove the 18,816 points of `T` from `O`. By the
consequence, that problem can use (K) moves, which the verifiers re-check exactly.

This is the same pattern as at `(8, 8)` and `(8, 9)`. There, too, the (K) moves are needed only on top-shell points
with `x_8 = 0`. At `(8, 10)` the survivors in `O` have at least 6 nonzero coordinates, and their magnitude
profiles are the ones listed above. Every point of `Lmax_8` with such a profile survives.

Partial progress on the deletion problem (not part of the claim): `T` is split into four blocks, and each block has
its own chain of (K) moves. Together the chains delete 15,242 of the 18,816 points. The last chain starts from `O`
minus the first three blocks, finishes its block, and ends at exactly `O ∖ T`. The details and verification tiers are
in §6 of the proof route.

Proof: route `z8-rips-scale-10-reduces-to-top-shell-link-collapses-proof`.
