---
rg: 2
id: z8-rips-lifted-domination-certificates-fail-at-scale-8
kind: claim
title: At scale 8 no sequence of lifted domination moves peels Lmax_8 down to e_8, because a 16,114-point set blocks every move into it
distinct_from:
  z7-rips-contractible-at-scales-11-13-15-17: that closes four n = 7 scales with domination-only (orbit) certificates; this shows the same kind of certificate cannot exist at k = 8, r = 8
  zn-rips-contractible-at-every-scale-r-ge-n: that is Zaremsky's conjecture; this is a no-go theorem for one proof method (lifted (D)-only certificates) at one scale, and says nothing against the conjecture
  z7-rips-contractible-at-scales-7-and-8: that reports that a D-move greedy leaves about 6.7k and 10.4k survivors at (7,7), (7,8) and closes those scales with link collapses; this proves that such survivors are forced for every order of (D) moves, via a self-blocking set, and does so at (8,8)
---

Work in the lifted reduction of `z7-rips-contractible-at-scale-10-proof` (§3):
- `Lmax_k = { x ∈ Z^k : |x|_1 ≤ r, x ≻ 0 }`, where `x ≻ 0` means the last nonzero coordinate is positive;
- `E = e_k`;
- a **(D) move** `x | w` deletes `x` from the current set `C` when `x, w ∈ C`, `w ≠ x`, `w ∈ hull(0, x, E)` and
  `N[x] ∩ C ⊆ N[w]`. Here `N[v]` is the closed `r`-ball in `d_1`.

**Claim.** For `k = 8`, `r = 8` there is no sequence of (D) moves that starts at `C = Lmax_8` and ends at
`C = {e_8}`.

The reason is an explicit set `K ⊆ Lmax_8` of 16,114 points, with `e_8 ∈ K`, that is **self-blocking**: for every
`x ∈ K ∖ {e_8}` and every `w ∈ hull(0, x, E) ∩ Lmax_8` with `w ≠ x`, some `z ∈ K` has `d(z, x) ≤ 8 < d(z, w)`. The
dominator `w` ranges over all of `Lmax_8`, not only over the current set.

Consequences:
- The theorem of `z7-rips-contractible-at-scale-10-proof` cannot be fed a (D)-only certificate at `(k, r) = (8, 8)`.
- This covers every orbit certificate in the sense of `z7-rips-contractible-at-scales-11-13-15-17-proof`, since
  those expand to (D) moves, and every order of deletion.
- So `VR(Z^8, d_1; 8)` needs the link-collapse (K) moves, or a new move, in this framework.

The same computation gives exact self-blocking sets, the greatest ones, of sizes 883, 6,720, 10,392 and 23,830 at
`(k, r) = (6, 6)`, `(7, 7)`, `(7, 8)` and `(7, 9)`. Those four scales are closed on main by other means. At `(6, 7)`,
`(6, 8)` and `(6, 9)` the greatest self-blocking set is `{e_6}`, so this obstruction is absent there. That absence does
not by itself give a certificate. The sizes at `(7, 7)` and `(7, 8)` are one less than the survivor counts 6,721 and
10,393 that `z7-rips-contractible-at-scales-7-and-8` reports for its unlifted (D) greedy.

Proof: route `z8-rips-lifted-domination-certificates-fail-at-scale-8-proof`.
