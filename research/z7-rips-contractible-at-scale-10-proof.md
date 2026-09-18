---
rg: 2
id: z7-rips-contractible-at-scale-10-proof
kind: route
title: Lifted peeling links, one domination and cone-collapse certificate per link dimension k = 2..7, replayed by an exhaustive verifier
target: z7-rips-contractible-at-scale-10
requires: []
artifacts: [research/z6-rips-contractible-at-scales-6-to-9-proof.md, experiments/zn-rips-lifted-interleaved-2026-09-18/README.md, experiments/zn-rips-lifted-interleaved-2026-09-18/ilv2.cpp, experiments/zn-rips-lifted-interleaved-2026-09-18/kcore.cpp, experiments/zn-rips-lifted-interleaved-2026-09-18/vcert.cpp, experiments/zn-rips-lifted-interleaved-2026-09-18/results.txt, experiments/zn-rips-lifted-interleaved-2026-09-18/certs/cert-7-10-k2.txt.gz, experiments/zn-rips-lifted-interleaved-2026-09-18/certs/cert-7-10-k3.txt.gz, experiments/zn-rips-lifted-interleaved-2026-09-18/certs/cert-7-10-k4.txt.gz, experiments/zn-rips-lifted-interleaved-2026-09-18/certs/cert-7-10-k5.txt.gz, experiments/zn-rips-lifted-interleaved-2026-09-18/certs/cert-7-10-k6.txt.gz, experiments/zn-rips-lifted-interleaved-2026-09-18/certs/cert-7-10-k7.txt.gz]
---

Notation is as in `research/z6-rips-contractible-at-scales-6-to-9-proof.md`:
- `N[v]` is the closed neighbourhood at distance `≤ r`;
- `x ≻ 0` means the last nonzero coordinate of `x` is positive;
- `hull(S)` is the smallest integer box containing `S`.

Here `n = 7` and `r = 10`, but §1–§3 hold for every `(n, r)`.

## 1. Peeling (from the z6 route)

Lemmas 1–3 and §2 of `z6-rips-contractible-at-scales-6-to-9-proof` hold for all `(n, r)`. They show that
`VR(Z^n, d_1; r)` is contractible as soon as every `Flag(L(I))` is contractible, where:
- `L(I) = { x ∈ I ∩ Z^n : |x|_1 ≤ r, x ≻ 0 }`;
- `I = Π_i [−a_i, b_i]` ranges over the integer boxes with `a_i, b_i ≥ 0` and some `b_i ≥ 1`.

Lemma 2 (vertex deletion with a contractible link) and Lemma 3 (a dominated vertex `N[u] ⊆ N[w]`, `u ≠ w`, has a cone
link) are used below.

## 2. The lift

**Lemma L.** Let `k = max{ i : b_i ≥ 1 }`. Every `x ∈ L(I)` has `x_i = 0` for `i > k`. Hence
`L(I) = L_k(I') × {0}`, where:
- `I' = Π_{i ≤ k} [−a_i, b_i] ⊂ Z^k`;
- `L_k(I') = { x ∈ I' : |x|_1 ≤ r, x ≻ 0 }`.

The map `x ↦ (x, 0)` is an isometry for `d_1`. The box `I'` contains `0` and `e_k`, since `b_k ≥ 1`.

*Proof.* Suppose `x ≠ 0` has a nonzero coordinate at some index `> k`. Let `j` be the last such index. Since `x ≻ 0`,
we get `x_j > 0`. But `x_j ≤ b_j = 0`, a contradiction. ∎

So it suffices to show the following for each `k = 1, …, n`: `Flag(L_k(I'))` is contractible for every box
`I' ∋ 0` in `Z^k` whose last upper bound `b_k` is at least `1`.

All these sets lie in `Lmax_k = L_k([−r, r]^{k−1} × [0, r])`.

The case `k = 1` is immediate. `L_1(I') = {1, …, min(b_1, r)}` has diameter `≤ r − 1`, so it spans a simplex.

## 3. Lifted certificates

Fix `k ≥ 2` and put `E = e_k`. A certificate is a sequence of moves on a current set `C`, which starts as
`C = Lmax_k`. There are two kinds of move.

- **(D) x | w.** Conditions:
  - `x, w ∈ C` and `w ≠ x`;
  - `w ∈ hull(0, x, E)`;
  - `N[x] ∩ C ⊆ N[w]`.

  Then delete `x`.

- **(K) u | w ; (b_1 | v_1), …, (b_m | v_m).** Put `S = N(u) ∩ C`. For each `j` in order:
  - `b_j` and `v_j` lie in the current `S`, and `v_j ≠ b_j`;
  - `v_j ∈ hull(0, u, b_j, E)`;
  - `N[b_j] ∩ S ⊆ N[v_j]`.

  Then remove `b_j` from `S`. After step `m`, we need:
  - `w ∈ S` and `w ∈ hull(0, u, E)`;
  - `S ⊆ N[w]`.

  Then delete `u` from `C`. The removals of the `b_j` from `S` are temporary: the `b_j` stay in `C`.

**Lemma 4L.** Let `I' ∋ 0` be a box in `Z^k` with `b_k ≥ 1`. Put `C_{I'} = C ∩ L_k(I')`. Then each move changes
`Flag(C_{I'})` only up to homotopy equivalence.

*Proof.* If the deleted point is not in `I'`, then `C_{I'}` does not change. Otherwise the box `I'` contains
`0`, `E` and the deleted point, so it contains the hull of any subset of them. Every point a move uses lies in
`Lmax_k`, so it is `≻ 0` and has norm `≤ r`. Hence any such point inside `I'` lies in `L_k(I')`.

(D) We have `w ∈ hull(0, x, E) ⊆ I'`, so `w ∈ C_{I'}`. Also `N[x] ∩ C_{I'} ⊆ N[x] ∩ C ⊆ N[w]`. Lemma 3 of the z6
route applies in `Flag(C_{I'})`.

(K) The link of `u` in `Flag(C_{I'})` is `Flag(S ∩ I')`. Run only the steps with `b_j ∈ I'`.

- The current set in the restricted run is always (current `S`) `∩ I'`.
- For such a step, `v_j ∈ hull(0, u, b_j, E) ⊆ I'`, so `v_j` lies in the restricted current set.
- The inclusion `N[b_j] ∩ (S ∩ I') ⊆ N[v_j]` follows from the unrestricted one.

So each restricted step deletes a dominated vertex (Lemma 3). At the end the restricted set is `S ∩ I'`. It contains
`w`, because `w ∈ hull(0, u, E) ⊆ I'`, and it lies in `N[w]`. Therefore `Flag(S ∩ I')` is a cone with apex `w`, and
Lemma 2 deletes `u`. ∎

**Lemma 5L.** Suppose a certificate ends with `C = {E}`. Then `Flag(L_k(I'))` is contractible for every box
`I' ∋ 0` with `b_k ≥ 1`.

*Proof.* By Lemma 4L, `Flag(L_k(I')) ≃ Flag({E} ∩ L_k(I'))`. This is a point, since `E ∈ I'`, `|E| = 1 ≤ r` and
`E ≻ 0`. ∎

**Theorem.** Suppose that for each `k = 2, …, n` there is a lifted certificate on `Lmax_k` at scale `r` that ends at
`{e_k}`. Then `VR(Z^n, d_1; r)` is contractible.

*Proof.* Combine §1, Lemma L, the case `k = 1`, and Lemma 5L. ∎

What is new compared with the z6 and z7 certificates:
- **Hulls.** The earlier certificates use dominators in `hull(0, x)` and must end at the full set `{e_1, …, e_n}`.
  Here the dominators may use the extra direction `E`, and a certificate must end at `{e_k}`. The price is one
  certificate per dimension `k ≤ n`, but the small `k` are cheap.
- **Cone ending.** The K-move ends at a cone on `w` rather than at a single point, which is a weaker requirement.

## 4. The certificate at (n, r) = (7, 10)

The file `experiments/zn-rips-lifted-interleaved-2026-09-18/certs/cert-7-10-k<k>.txt.gz` holds the certificate for
`k = 2, …, 7`. Each line `D x | w` or `K u | w m` is followed, for `K`, by `m` lines `b | v`. The generator labels
some (D) moves by how it found them:
- `A`: balanced sphere dominator, from Lemma 4 of `zn-rips-sphere-balanced-dominator-criterion-proof`;
- `S`: slack-one dominator;
- `B`: lower-norm point deleted against the current set.

For the proof, `A`, `S` and `B` lines are plain (D) moves. The verifier checks each one directly, so the proof does
not depend on those lemmas.

| k | `|Lmax_k|` | A | S | B | D | K (link steps) | end |
|---|---|---|---|---|---|---|---|
| 2 | 110 | 20 | 0 | 88 | 1 | 0 | `{e_2}` |
| 3 | 780 | 201 | 0 | 576 | 2 | 0 | `{e_3}` |
| 4 | 4,180 | 1,360 | 0 | 2,816 | 3 | 0 | `{e_4}` |
| 5 | 18,182 | 7,001 | 0 | 11,176 | 4 | 0 | `{e_5}` |
| 6 | 67,122 | 27,444 | 1,920 | 37,752 | 5 | 0 | `{e_6}` |
| 7 | 216,952 | 86,065 | 0 | 85,023 | 43,943 | 1,920 (40,756) | `{e_7}` |

**Verification.** `vcert.cpp` replays a certificate against an explicit presence bitmap of `Lmax_k`. It shares no
code with the generators `ilv2.cpp` and `kcore.cpp`, and it does not use their bitset adjacency. For every move it
checks the following.
- Membership. The points involved are present (for K steps: present, within `r` of `u`, and not yet removed from
  the link). Also `w ≠ x` and `d(x, w) ≤ r`.
- Hulls. The required hull condition holds, with `e_k` included in the hull.
- Domination. It searches exhaustively over all `z ∈ Lmax_k` for a violating `z`. This is a depth-first search over
  coordinates with the pruning bound `|z_i − w_i| ≤ min(|z_i| + |w_i|, |z_i − x_i| + |x_i − w_i|)`:
  - (D): a present `z` with `d(z,x) ≤ r < d(z,w)`;
  - K step: `z` in the current link with `d(z,b) ≤ r < d(z,v)`;
  - end of K: `z` in the final link with `d(z,w) > r`.
- End state. After the last move, the present set is exactly `{e_k}`.

Output (`results.txt`): `VERIFIED: ends at {e_k}` for every `k = 2, …, 7`. The `k = 7` run takes about 50 s and
explores 2.2·10^9 search nodes.

Sanity checks on the verifier, all of which were rejected:
- a (D) line whose `w` does not dominate (`A -9 1 0 | 0 1 0` at `k = 3`): rejected with "domination fails";
- a certificate missing its last move: rejected, the end set is not `{e_k}`;
- the first K move at `k = 7` with one link step deleted: rejected with "final link not a cone on w";
- a certificate with one move duplicated: rejected with "x not present" at the second copy.

With `n = 7` and `r = 10`, the Theorem of §3 gives the claim. ∎
