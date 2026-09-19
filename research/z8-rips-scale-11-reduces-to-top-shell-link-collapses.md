---
rg: 2
id: z8-rips-scale-11-reduces-to-top-shell-link-collapses
kind: claim
title: At scale 11 the k = 8 lifted certificate for Z^8 reduces to deleting an explicit 53,312-point top-shell set by link collapses
distinct_from:
  zn-rips-contractible-at-every-scale-r-ge-n: that is Zaremsky's conjecture; this is a verified reduction of the single case n = 8, r = 11 to one explicit finite deletion problem, and does not settle that case
  z8-rips-scale-10-reduces-to-top-shell-link-collapses: that is the same reduction at r = 10, with an 18,816-point set of 6- and 7-part profiles of 10; this is r = 11, where the set is 53,312 points and has three 6-part profiles of 11
  z8-rips-contractible-at-scale-10: that finishes (8, 10) with (K) chains; this is the next scale, where only the domination parts are complete
  z7-rips-contractible-at-scales-11-13-15-17: that is dimension 7 at scale 11 (and 13, 15, 17), whose k = 2..7 certificates are reused here; this is the missing k = 8 certificate at r = 11, reduced but not finished
---

Work in the lifted reduction of `z7-rips-contractible-at-scale-10-proof` (§3), with `k = 8`, `r = 11`:
- `Lmax_8 = { x ∈ Z^8 : |x|_1 ≤ 11, x ≻ 0 }`, where `x ≻ 0` means the last nonzero coordinate is positive. It has
  1,242,912 points.
- `E = e_8`, and `N[v]` is the closed `d_1`-ball of radius 11.
- A **(D) move** `x | w` deletes `x` from the current set `C` when `x, w ∈ C`, `w ≠ x`, `w ∈ hull(0, x, E)` and
  `N[x] ∩ C ⊆ N[w]`. A **(K) move** is the link-collapse move of `z8-rips-contractible-at-scale-8-proof` (§1).

Let `O ⊆ Lmax_8` be the 399,702-point set in `experiments/zn-rips-link-collapse-scale-11-2026-09-19/sets/O-8-11.txt.gz`.
Let `T` be the set of points `x ∈ Lmax_8` with all three of the following:
- `|x|_1 = 11`;
- `x_8 = 0`;
- the nonzero `|x_i|`, as a multiset, form one of the seven partitions of 11 below.

The seven partitions are the four 7-part partitions `(4,2,1^5)`, `(3,3,1^5)`, `(3,2,2,1^4)`, `(2^4,1^3)` (all 7-part
partitions of 11 except `(5,1^6)`), and the three 6-part partitions `(4,2,2,1^3)`, `(3,3,2,1^3)`, `(3,2,2,2,1,1)`.

**Claim.**
1. A sequence of 843,210 (D) moves takes `C = Lmax_8` to `C = O`.
2. `T ⊆ O` and `|T| = 53,312`. Also, `T` is `{ x ∈ O : |x|_1 = 11, x_8 = 0 }` minus its 48 points of profile
   `(5,1^6)`.
3. A sequence of 346,389 (D) moves takes `C = O ∖ T` to `C = {e_8}`.

**Consequence.** Suppose some sequence of lifted moves takes `C = O` to `C = O ∖ T`. That is, it deletes exactly
the points of `T`, in some order, by (D) and (K) moves. Then (1), that sequence and (3) together form a lifted
certificate on `Lmax_8` at `r = 11` that ends at `{e_8}`. The certificates for `k = 2, …, 7` at `r = 11` are those of
`z7-rips-contractible-at-scales-11-13-15-17-proof`. So the theorem of `z7-rips-contractible-at-scale-10-proof` gives
that `VR(Z^8, d_1; 11)` is contractible.

So the whole of `(8, 11)` is one explicit deletion problem: remove the 53,312 points of `T` from `O`, by (D) and
(K) moves, which the verifiers re-check exactly.

This is the pattern of `(8, 8)`, `(8, 9)` and `(8, 10)`: the (K) moves are needed only on top-shell points with
`x_8 = 0`. In the sense of `zn-rips-slack-sphere-criterion`, the partitions of 11 with fewer than 8 parts that are
unbalanced are exactly the seven profiles of `T` and `(5,1^6)`. So `T` is the unbalanced part of the top sphere with
`x_8 = 0`, minus the one class `(5,1^6)`, which the (D) moves delete. The same holds at `r = 10`: the profiles of
`T` in `z8-rips-scale-10-reduces-to-top-shell-link-collapses` are exactly the unbalanced partitions of 10 with fewer
than 8 parts. These are the zero-coordinate unbalanced sphere points that the "limit of the method" paragraph of
that criterion predicts to be stuck. Every point of the seven classes with `x_8 = 0` survives the prefix.

Not part of the claim: a sample of 21 points of `T` all admit (K) moves against `C = O` (search `kzs2`). The
search found `w = e_7 + e_8` for 13 of the 18 with `x_7 ≠ 0`. For the others it found `u` with its largest
coordinate moved towards 0, plus `e_8`. The proof route (§5) records this, the formula-witness tests and the cost of
the (K) phase.

Proof: route `z8-rips-scale-11-reduces-to-top-shell-link-collapses-proof`.
