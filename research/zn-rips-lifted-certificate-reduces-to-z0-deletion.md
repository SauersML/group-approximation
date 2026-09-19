---
rg: 2
id: zn-rips-lifted-certificate-reduces-to-z0-deletion
kind: claim
title: Off the zero-coordinate top shell every point of Lmax_k is within r of e_k, so a lifted certificate exists as soon as Z_0 can be deleted
distinct_from:
  zn-rips-top-shell-sign-hull-certificates: its Claim 6 needs certificates for the unbalanced points of Z_0 and of Top minus Z_0, then the Stage 2 (D) moves; this shows that once Z_0 is gone every other point is deleted by x | e_k in any order, so condition (b) and Stage 2 are not needed
  zn-rips-top-shell-formula-link-collapse: that records that 824 unbalanced points of Top minus Z_0 with x_7 = 1 have no Top-certificate at (7, 7); this shows those points never need a certificate
  zn-rips-sphere-balanced-dominator-criterion: that deletes every top-sphere point by a (D) move and needs every partition of r into at most n parts to be balanced; this needs nothing off Z_0, and on Z_0 only the unbalanced partitions of r into at most k - 1 parts
  zn-rips-contractible-at-every-scale-r-ge-n: that is Zaremsky's conjecture; this is a strict reduction of the lifted-certificate route to it, not a proof
---

Notation is that of `zn-rips-top-shell-sign-hull-certificates`. Fix `n ≥ 2`, `r ≥ 3` and a level
`k ∈ {2, …, n}`. Put `E = e_k` and `Lmax = Lmax_k = { x ∈ Z^k : 1 ≤ |x|_1 ≤ r, x ≻ 0 }`, where `x ≻ 0` means the
last nonzero coordinate is positive. `N[v]` is the closed `d_1`-ball of radius `r`. The zero-coordinate top
shell is `Z_0 = Z_0(k, r) = { x ∈ Lmax : |x| = r, x_k = 0 }`. The moves (D) and (K) and the lifted certificates are
those of `z8-rips-contractible-at-scale-8-proof` §1.

**Claim.**
1. *(Cone lemma.)* For `b ∈ Lmax`, `d(b, E) = |b| − 1` if `b_k ≥ 1`, and `d(b, E) = |b| + 1` if `b_k = 0`.
   So `Lmax ∖ N[E] = Z_0`.
2. *(Cone ending.)* Let `C ⊆ Lmax` with `E ∈ C` and `C ∩ Z_0 = ∅`. Then the (D) moves `x | E`, for the points
   `x ∈ C ∖ {E}` in any order, take `C` to `{E}`.
3. *(Reduction.)* Suppose that for every `k ∈ {2, …, n}` some sequence of lifted moves takes `C = Lmax_k` to a
   set that contains `E` and meets no point of `Z_0(k, r)`. Then `VR(Z^n, d_1; r)` is contractible.
4. *(Z_0-certificates suffice.)* Fix `k`. Suppose every unbalanced `u ∈ Z_0(k, r)` has a `Z_0`-certificate in the
   sense of `zn-rips-top-shell-sign-hull-certificates`. Then there is a lifted certificate on `Lmax_k` at scale `r`
   that ends at `{e_k}`, namely:
   - the (K) moves `K u | w` of the certificates, one for each unbalanced `u ∈ Z_0`, in any order;
   - the (D) moves `u | w` of that node's Claim 3, one for each balanced `u ∈ Z_0`, in any order;
   - the (D) moves `x | E`, one for each remaining `x ≠ E`, in any order.

   So if this holds for every `k ∈ {2, …, n}`, then `VR(Z^n, d_1; r)` is contractible.

So Claim 6 of `zn-rips-top-shell-sign-hull-certificates` holds with its condition (b) removed. Condition (b) is
the one that fails at `(7, 7)`: the 824 unbalanced points with `x_7 = 1` recorded in
`zn-rips-top-shell-formula-link-collapse` have no `Top`-certificate. Under 4 they are deleted by `x | E` after `Z_0`,
and they need no certificate.

So the whole top shell off `Z_0`, and every lower norm, is deleted with the one witness `E`, and Stage 2 of
`zn-rips-sphere-balanced-dominator-criterion-proof` is not needed either. What is left of the lifted route to
Zaremsky's conjecture is one condition per level: the unbalanced points of `Z_0(k, r)`. Their magnitude profiles are
the unbalanced partitions of `r` into at most `k − 1` parts, since `x_k = 0`. For fixed `(n, r)` this is a finite
local check. It is order-free, and each point is verified on its own.

Proof: route `zn-rips-lifted-certificate-reduces-to-z0-deletion-proof`.

Applied in `z8-rips-contractible-at-scale-11`.
