---
rg: 2
id: zn-rips-top-shell-sign-hull-certificates
kind: claim
title: Sign-hull certificates make top-shell link collapses order-free in the lifted Rips reduction, so each scale reduces to certifying its unbalanced top-shell points
distinct_from:
  zn-rips-sphere-balanced-dominator-criterion: that criterion deletes each top-sphere point by a (D) move, so it needs every partition of r into at most n parts to be balanced; this deletes the unbalanced top-sphere points by (K) moves, each certified by a finite local test, and uses the criterion's Lemmas 3–4 only for the balanced ones
  zn-rips-slack-sphere-criterion: that criterion still uses (D) moves, with slack-one dominators; this uses (K) link collapses whose steps are dominations by sign-hull points of three balls
  z8-rips-scale-11-reduces-to-top-shell-link-collapses: that is a per-scale computation that leaves an explicit set T to delete; this is a scale-free sufficient condition and an order-free deletion scheme for such sets
---

Notation is that of `z8-rips-contractible-at-scale-8-proof` (§1) and `zn-rips-sphere-balanced-dominator-criterion-proof`.
Fix `n ≥ 2`, `r ≥ 3` and a level `k ∈ {2, …, n}`. Put `E = e_k` and
`Lmax = Lmax_k = { x ∈ Z^k : 1 ≤ |x|_1 ≤ r, x ≻ 0 }`, where `x ≻ 0` means the last nonzero coordinate is positive.
`N[v]` is the closed `d_1`-ball of radius `r`. The **top shell** is `Top = { x ∈ Lmax : |x| = r }`. Its
**zero-coordinate part** is `Z_0 = { x ∈ Top : x_k = 0 }`. A top-shell point is **balanced** when its magnitude
partition is balanced in the sense of `zn-rips-sphere-balanced-dominator-criterion`.

The **sign hull** of a finite set `A ⊂ Z^k` is `sh(A) = { v : ⟨σ,v⟩ ≥ min_{a∈A} ⟨σ,a⟩ for all σ ∈ {±1}^k }`.

**Certificates.** Let `F ⊆ Top` and `u ∈ F`. An **`F`-certificate** for `u` is a point `w ∈ Lmax ∖ F` with
`w ≠ u`, `d(u,w) ≤ r` and `w ∈ hull(0,u,E)`, together with a point `v_b` for each `b` in the **bad set**
`Bad(u,w) = { b ∈ Lmax : b ≠ u, d(b,u) ≤ r, d(b,w) > r }`, such that each `v_b` satisfies all of:
- `v_b ∈ Lmax ∖ F`;
- `v_b ∈ hull(0,u,b,E)`;
- `d(v_b,w) ≤ r`;
- `v_b ∈ sh{0,u,b}`.

**Claim.**
1. *(Sign-hull lemma.)* If `v ∈ sh(A)`, then `∩_{a∈A} N[a] ⊆ N[v]`, for every radius.
2. *(Order-free (K) moves.)* Suppose `u` has an `F`-certificate. Then `K u | w` is a valid (K) move in every current set
   `C` with `Lmax ∖ F ⊆ C ⊆ Lmax` and `u ∈ C`. Its steps remove the points of `Bad(u,w) ∩ C`, in any order, each `b`
   with `v_b`. The only points the move needs present, besides `u`, are `w` and the `v_b`. They all lie outside `F`,
   so no order on `F` is needed.
3. *(Balanced points.)* A balanced `u ∈ Top` has a `Top`-certificate with empty bad set: the dominator of Lemma 4 of
   `zn-rips-sphere-balanced-dominator-criterion-proof`.
4. *(Bad sets of norm-two witnesses.)* Let `u ∈ Z_0`, `i < k` with `u_i ≠ 0`, `s = sgn(u_i)` and `w = s e_i + e_k`.
   Then `w ∈ Lmax ∖ Top`, `w ∈ hull(0,u,E)` and `d(u,w) = r`. Also `b ∈ Bad(u,w)` if and only if `b ∈ Lmax`, `b ≠ u`,
   `d(b,u) ≤ r`, `b_k = 0`, `s b_i ≤ 0` and `|b| ∈ {r − 1, r}`.
5. *(Balanced bad points certify themselves.)* In 4, let `r ≥ 4`. Every `b ∈ Bad(u,w)` whose magnitude partition is
   balanced has a point `v_b` as in the definition, for `F = Top`. So `w` is a `Z_0`-certificate for `u` as soon
   as the **unbalanced** bad points have one. These have magnitude profiles that are unbalanced partitions of `r − 1`
   or `r` into at most `k − 1` parts.
6. *(Reduction.)* Suppose that for every `k ∈ {2, …, n}`:
   - (a) every unbalanced `u ∈ Z_0` has a `Z_0`-certificate; and
   - (b) every unbalanced `u ∈ Top ∖ Z_0` has a `Top`-certificate.

   Then `VR(Z^n, d_1; r)` is contractible. On each level, the certificate deletes `Z_0` by (K) moves in any order,
   then `Top ∖ Z_0` in any order, then the lower norms by the (D) moves of Stage 2 of that criterion.

By 3 and 5, only the unbalanced top-shell points, and among their bad points only the unbalanced ones, need a
search. The unbalanced partitions are listed in `zn-rips-sphere-balanced-dominator-criterion`. So the test is a
finite, local check around each unbalanced top-shell point. It is order-free, and a verifier can replay it one point
at a time. At `(n, r) = (8, 11)`, the set `T` of `z8-rips-scale-11-reduces-to-top-shell-link-collapses` lies in `Z_0`.
Its (D) prefix and tail never use a point of `T`. So by 2, `Z_0`-certificates for the points of `T` would finish
`(8, 11)`: run the (K) moves first, from all of `Lmax_8`, then the prefix and the tail unchanged.

The conditions hold for `2 ≤ n ≤ r ≤ 6` and for `n ≤ 6`, `r = 7`. Condition (b) fails at level 7 for `r = 7`:
824 unbalanced points with `x_7 = 1` have no `Top`-certificate (Claim 3′ of `zn-rips-top-shell-formula-link-collapse`).
So Claim 6 alone does not give a uniform route.

Proof: route `zn-rips-top-shell-sign-hull-certificates-proof`. The computations (which witnesses certify at which
scales, and where they fail) are in `zn-rips-top-shell-formula-link-collapse`.

## Attempts
- 2026-09-19 (w11-103): built this scheme to replace the formula link collapses of
  `z8-rips-scale-11-reduces-to-top-shell-link-collapses`, since those cannot be proved one bad point at a time.
  It certifies `Z_0` at every scale tested, and it reduces `(8, 11)` to `Z_0`-certificates for the 53,312 points
  of `T`. For the unbalanced points of `Top ∖ Z_0` with `x_k = 1`, it stops at `(7, 7)`.
  Open: a uniform witness rule for `Z_0`, and another deletion for those points.
