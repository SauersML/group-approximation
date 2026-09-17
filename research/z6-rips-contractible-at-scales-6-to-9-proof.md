---
rg: 2
id: z6-rips-contractible-at-scales-6-to-9-proof
kind: route
title: Anti-lexicographic peeling plus one uniform domination and link-collapse certificate per scale
target: z6-rips-contractible-at-scales-6-to-9
requires: []
artifacts: [experiments/zn-rips-sharp-scale-2026-09-17/README.md, experiments/zn-rips-sharp-scale-2026-09-17/uniform.cpp, experiments/zn-rips-sharp-scale-2026-09-17/verify.py, experiments/zn-rips-sharp-scale-2026-09-17/verify_fast.cpp, experiments/zn-rips-sharp-scale-2026-09-17/results.txt, experiments/zn-rips-sharp-scale-2026-09-17/certs/cert-6-6.txt.gz, experiments/zn-rips-sharp-scale-2026-09-17/certs/cert-6-7.txt.gz, experiments/zn-rips-sharp-scale-2026-09-17/certs/cert-6-8.txt.gz, experiments/zn-rips-sharp-scale-2026-09-17/certs/cert-6-9.txt.gz]
---

Notation. `X_r = VR(Z^n, d_1; r)` is the flag complex on `Z^n` in which `x ~ y` iff `d_1(x,y) ≤ r`.
For a vertex set `V`, `Flag(V)` is the induced flag complex. `N(v)` is the set of neighbours of `v`,
and `N[v] = N(v) ∪ {v}`. `x ≻ 0` means that the last nonzero coordinate of `x` is positive.
`hull(S)` is the smallest integer box containing `S`.

## 1. Reduction to boxes

**Lemma 1.** If `Flag([0,m]^n)` is contractible for every `m`, then `X_r` is contractible.

*Proof.* A map `S^k → X_r` has compact image, which lies in a finite subcomplex. That subcomplex lies
in `Flag(v + [0,m]^n)` for some `v` and `m`. Translation is an isometry, so this complex is
contractible and the map is null-homotopic. Hence all `π_k(X_r)` vanish, and Whitehead's theorem
applies to the CW complex `X_r`. ∎

**Lemma 2 (vertex deletion).** Let `v` be a vertex of a flag complex `X = Flag(V)`. If
`lk(v) = Flag(N(v))` is contractible, then `Flag(V − v) → X` is a homotopy equivalence.

*Proof.* `X = Flag(V − v) ∪ st(v)`, and the two pieces intersect in `lk(v)`. The star `st(v)` is a
cone. Gluing a cone along a contractible subcomplex does not change the homotopy type. ∎

**Lemma 3 (domination).** Suppose `u ≠ w` and `N[u] ⊆ N[w]`. Then `w ∈ N(u)` and `Flag(N(u))` is a
cone with apex `w`. So Lemma 2 applies to `u`. ∎

## 2. Anti-lexicographic peeling

Order `[0,m]^n` anti-lexicographically: `x ≺ y` iff `x_i < y_i` at the largest index where they
differ. List the points as `v_1 ≺ … ≺ v_M` and put `X_k = Flag({v_k, …, v_M})`. The link of `v_k`
in `X_k` is `Flag` on `{y ≻ v_k : d_1(y, v_k) ≤ r}`. The order is translation invariant, so
translating by `−v_k` identifies it with `Flag(L(I_k))`, where

`L(I) = { x ∈ I ∩ Z^n : |x|_1 ≤ r, x ≻ 0 }`, and `I_k = Π_i [−a_i, b_i]` with
`a_i = min(δ_i, r)`, `b_i = min(m − δ_i, r)` and `δ = v_k`.

Coordinates can be truncated at `r` because `|x_i| ≤ |x|_1 ≤ r`. If `k < M`, then `δ ≠ (m,…,m)`, so
some `b_i ≥ 1`. By Lemma 2 applied `M − 1` times, `Flag([0,m]^n)` is contractible as soon as every
`Flag(L(I))` is contractible, for every box `I ∋ 0` with some `b_i ≥ 1`.

## 3. Uniform reduction

Every such `L(I)` is a subset of `Lmax = L([−r,r]^{n−1} × [0,r])`, because `x ≻ 0` forces `x_n ≥ 0`.
A **certificate** is a finite sequence of moves on a current set `C`, which starts as `C = Lmax`.

- **(D) x | w.** Here `x, w ∈ C`, `w ≠ x`, `w ∈ hull(0, x)`, and `N[x] ∩ C ⊆ N[w]`. Then delete `x`.
- **(K) x | p ; (y_1|w_1), …, (y_m|w_m).** Put `S = N(x) ∩ C`. We need `p ∈ S ∩ hull(0,x)`. For each `j`,
  `y_j, w_j` lie in the current `S`, `w_j ≠ y_j`, `w_j ∈ hull(0, x, y_j)`, and `N[y_j] ∩ S ⊆ N[w_j]`.
  After deleting `y_j`, and once all `m` steps are done, `S = {p}`. Then delete `x`.

Let `K` be the final `C`.

**Lemma 4.** Given a certificate, `Flag(L(I)) ≃ Flag(L(I) ∩ K)` for every box `I ∋ 0`.

*Proof.* Put `C_I = C ∩ L(I)`. We show that each move changes `Flag(C_I)` only up to homotopy. If
`x ∉ I`, then `C_I` is unchanged. Otherwise `x ∈ I`, and since `I` is a box containing `0` and `x`,
`hull(0,x) ⊆ I`. Every point used by a move lies in `Lmax`, so it has `|·|_1 ≤ r` and is `≻ 0`. Hence
any such point lying in `I` lies in `L(I)`.

(D) We have `w ∈ C ∩ hull(0,x) ⊆ C_I` and `N[x] ∩ C_I ⊆ N[x] ∩ C ⊆ N[w]`. Lemma 3 applies in `Flag(C_I)`.

(K) The link of `x` in `Flag(C_I)` is `Flag(S_I)` with `S_I = S ∩ L(I)`. Run the link steps restricted to
the `y_j ∈ I`. For such `j`, `w_j ∈ hull(0, x, y_j) ⊆ I`, so `w_j` lies in the current `S_I`, and the
domination inclusion only gets weaker on subsets. Each step is a Lemma 3 deletion in `Flag(S_I)`, and it
ends at `{p} ∩ L(I) = {p}` because `p ∈ hull(0,x) ⊆ I`. So `Flag(S_I)` is contractible, and Lemma 2 deletes `x`. ∎

**Lemma 5.** If `K = {e_1, …, e_n}`, then every `Flag(L(I))` with some `b_i ≥ 1` is contractible.

*Proof.* `L(I) ∩ K = {e_i : b_i ≥ 1}` is nonempty, and its points are pairwise at distance `2 ≤ r`.
So it spans a simplex. Now apply Lemma 4. ∎

**Theorem.** Fix `(n, r)`. If a certificate on `Lmax` ends with `K = {e_1, …, e_n}`, then `X_r` is contractible.
This follows from Lemmas 1, 5 and §2.

## 4. The certificates

`experiments/zn-rips-sharp-scale-2026-09-17/uniform.cpp` searches for certificates greedily. It removes
points in order of decreasing norm, using D-moves first and K-moves once D-moves are exhausted, and repeats
passes until nothing changes. `verify.py` is a separate numpy program. It regenerates `Lmax` from its
definition and replays the certificate, checking every condition of §3 by explicit `d_1` computations.
It accepts only if `K = {e_1..e_n}`.

For `n = 6` and `r ∈ {6, 7, 8, 9}`, both programs report `K = {e_1, …, e_6}`, and the verifier prints ACCEPT.
The outputs are in `results.txt`.

| r | `|Lmax|` | D-moves | K-moves | K link steps |
|---|---|---|---|---|
| 6 | 4494 | 4408 | 80 | 30536 |
| 7 | 9912 | 9782 | 124 | 51132 |
| 8 | 20040 | 20034 | 0 | 0 |
| 9 | 37758 | 37752 | 0 | 0 |

The certificates are committed gzipped in `certs/`. Reproduce with `gunzip -k certs/cert-6-r.txt.gz && python3 verify.py 6 r certs/cert-6-r.txt`,
or regenerate them with `g++ -O2 -o uniform uniform.cpp && ./uniform 6 r 1 K.txt cert.txt`. The search is
deterministic (compare the sha256 in `results.txt`) and each run takes minutes.

**Calibration.** At `r = n − 1` (`n = 3..6`) the search ends with `K = {0,1}^n ∖ {0, 1^n}`, and the verifier rejects. For the full box
`I` this set spans the boundary of a cross-polytope, so no certificate exists and none is claimed. This agrees
with the known non-contractibility at `r = n − 1`.

**Relation to GSS.** The coordinate-clipping and λ-domination lemmas of Gupta–Sarkar–Shukla
(arXiv:2511.04238, Lemmas 3.3–3.12) are D-moves of exactly this uniform kind: their dominators
`λ^{[x;S]}` lie in `hull(0,x)`. The two new ingredients here are the link-collapse move (K) and the
exhaustive search. D-moves alone leave 884 survivors at `(6,6)` and 1099 at `(6,7)`.
