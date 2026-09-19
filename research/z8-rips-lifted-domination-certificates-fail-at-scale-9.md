---
rg: 2
id: z8-rips-lifted-domination-certificates-fail-at-scale-9
kind: claim
title: At scale 9 no sequence of lifted domination moves peels Lmax_8 down to e_8, because a 113,321-point set blocks every move into it
distinct_from:
  z8-rips-lifted-domination-certificates-fail-at-scale-8: that is the same obstruction at (k, r) = (8, 8), with a 16,114-point set, and it leaves r ≥ 9 open; this settles r = 9
  zn-rips-contractible-at-every-scale-r-ge-n: that is Zaremsky's conjecture; this is a no-go theorem for one proof method (lifted (D)-only certificates) at one scale, and says nothing against the conjecture
  z8-rips-contractible-at-scale-8: that certifies (8, 8) with link-collapse moves; this shows that at (8, 9) those moves, or some other new move, are needed as well
---

Work in the lifted reduction of `z7-rips-contractible-at-scale-10-proof` (§3), with the notation of
`z8-rips-lifted-domination-certificates-fail-at-scale-8`:
- `Lmax_k = { x ∈ Z^k : |x|_1 ≤ r, x ≻ 0 }`;
- `E = e_k`;
- a (D) move `x | w` deletes `x` from the current set `C` when `x, w ∈ C`, `w ≠ x`, `w ∈ hull(0, x, E)` and
  `N[x] ∩ C ⊆ N[w]`.

**Claim.** For `k = 8`, `r = 9` there is no sequence of (D) moves that starts at `C = Lmax_8` and ends at
`C = {e_8}`.

The reason is an explicit set `K ⊆ Lmax_8` of 113,321 points, with `e_8 ∈ K`, that is self-blocking at `r = 9`:
for every `x ∈ K ∖ {e_8}` and every `w ∈ hull(0, x, E) ∩ Lmax_8` with `w ≠ x`, some `z ∈ K` has
`d(z, x) ≤ 9 < d(z, w)`. The dominator `w` ranges over all of `Lmax_8`, not only over the current set.

`K` is exactly the set where the deterministic (D) peeling of `experiments/zn-rips-lifted-domination-core-2026-09-18/ilv4.cpp`
stalls at `(8, 9)`. So at this scale the first stall of that greedy is already a self-blocking set. That is unlike
`(8, 8)`, where the stall set has 40,442 points and the self-blocking set found inside it has 16,114.

Consequences:
- The theorem of `z7-rips-contractible-at-scale-10-proof` cannot be fed a (D)-only certificate at `(8, 9)`, in any
  order of deletion and with any dominators. That includes orbit certificates.
- So `VR(Z^8, d_1; 9)` needs the link-collapse (K) moves of `z8-rips-contractible-at-scale-8-proof`, or another new
  move, in this framework. Together with the scale-8 node, the two sharpest open-at-the-time scales `r = 8, 9` for
  `n = 8` both lie outside (D)-only certificates.

Proof: route `z8-rips-lifted-domination-certificates-fail-at-scale-9-proof`.
