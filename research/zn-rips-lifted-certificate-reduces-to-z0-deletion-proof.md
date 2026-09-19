---
rg: 2
id: zn-rips-lifted-certificate-reduces-to-z0-deletion-proof
kind: route
title: The last coordinate of a point of Lmax_k is nonnegative, so only Z_0 lies outside the ball about e_k
target: zn-rips-lifted-certificate-reduces-to-z0-deletion
requires: [zn-rips-top-shell-sign-hull-certificates]
artifacts: [research/z8-rips-contractible-at-scale-8-proof.md, research/z7-rips-contractible-at-scale-10-proof.md, research/zn-rips-top-shell-sign-hull-certificates-proof.md]
---

Notation is that of the target. `|·| = |·|_1` and `d(x,y) = |x − y|`. The moves (D) and (K) are those of
`z8-rips-contractible-at-scale-8-proof` §1. There `hull(A)` is the smallest integer box containing `A`, so
`E ∈ hull(0, x, E)` for every `x`. The Theorem quoted there (from `z7-rips-contractible-at-scale-10-proof` §1–§3)
says: if for each `k = 2, …, n` some sequence of moves takes `C = Lmax_k` to `C = {e_k}`, then `VR(Z^n, d_1; r)`
is contractible.

## 1. The cone lemma (Claim 1)

Let `b ∈ Lmax`. Its last nonzero coordinate is positive. So either `b_k ≥ 1`, or `b_k = 0`. Now
`d(b, E) = Σ_{i<k} |b_i| + |b_k − 1|`.
- If `b_k ≥ 1`, then `|b_k − 1| = b_k − 1`, so `d(b, E) = |b| − 1 ≤ r − 1`.
- If `b_k = 0`, then `|b_k − 1| = 1`, so `d(b, E) = |b| + 1`. This is at most `r` if and only if `|b| ≤ r − 1`.

So `b ∉ N[E]` if and only if `b_k = 0` and `|b| = r`, that is, `b ∈ Z_0`. ∎

## 2. The cone ending (Claim 2)

Let `C ⊆ Lmax` with `E ∈ C` and `C ∩ Z_0 = ∅`. Delete the points of `C ∖ {E}` one at a time, in any order, by
`x | E`. Let `C'` be the current set when `x` is deleted. Then `x, E ∈ C'` and `x ≠ E`. Also
`E ∈ hull(0, x, E)`. Finally `C' ⊆ C ⊆ Lmax ∖ Z_0 ⊆ N[E]` by Claim 1, so `N[x] ∩ C' ⊆ N[E]`. So each move is a
valid (D) move, and the moves end at `{E}`. ∎

## 3. The reduction (Claim 3)

Fix `k`. Follow the given sequence from `Lmax_k` to a set `C` with `E ∈ C` and `C ∩ Z_0 = ∅`. Then apply
Claim 2. The result is a sequence of moves from `Lmax_k` to `{e_k}`. This holds for every `k = 2, …, n`, so the
Theorem gives the claim. ∎

## 4. Z_0-certificates (Claim 4)

Fix `k`, and start from `C = Lmax_k`.

*The unbalanced points.* Run `K u | w`, for the unbalanced `u ∈ Z_0` in any order, where `w` is the witness of the
`Z_0`-certificate of `u`. Before each move, `C` contains `u`, and it contains `Lmax ∖ Z_0`, since only points of
`Z_0` have been deleted. So by Claim 2 of `zn-rips-top-shell-sign-hull-certificates` each move is a valid (K) move.
It deletes `u`.

*The balanced points.* Let `u ∈ Z_0` be balanced. By Claim 3 of `zn-rips-top-shell-sign-hull-certificates`, it has a
`Top`-certificate `w` with empty bad set. So `w ∈ Lmax ∖ Top`, `w ≠ u`, `w ∈ hull(0, u, E)` and `d(u, w) ≤ r`.
An empty bad set means that every `b ∈ Lmax` with `b ≠ u` and `d(b, u) ≤ r` has `d(b, w) ≤ r`. So
`N[u] ∩ C ⊆ N[w]` for every `C ⊆ Lmax`. The point `w` is not in `Top`, so it has not been deleted. So `u | w` is a
valid (D) move in every current set that contains `u`. Run these moves for all balanced `u ∈ Z_0`, in any order.

Now `C = Lmax ∖ Z_0`. It contains `E`, because `|E| = 1 < r` and `E_k = 1`. So Claim 2 takes it to `{e_k}`,
and the three groups of moves form a lifted certificate on `Lmax_k` that ends at `{e_k}`. If this holds for every
`k = 2, …, n`, the Theorem gives contractibility. ∎

## 5. Remarks

- The profile of `u ∈ Z_0(k, r)` is a partition of `r` into at most `k − 1` parts, because `u_k = 0`. So the
  hypothesis of Claim 4 concerns only the unbalanced partitions of `r` into at most `k − 1 ≤ n − 1` parts.
- Claim 6 of `zn-rips-top-shell-sign-hull-certificates` deletes `Top ∖ Z_0` by certificates and then uses Stage 2
  of `zn-rips-sphere-balanced-dominator-criterion-proof`. Claim 2 above replaces both. In particular, its condition
  (b), which fails at `(7, 7)` for 824 points with `x_7 = 1`, is not needed.
- The same argument applies to any class `F` with `Z_0 ⊆ F ⊆ Top`: once `F` is deleted, `x | E` deletes the rest.
  So the only real obstruction to finishing a lifted certificate is the zero-coordinate top shell.
