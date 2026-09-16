# Pivot obstructions for the CAT(1) diagonal links of NCP_n (swarm frontier, 2026-09-16)

Status: written derivations, unreviewed. They extend
`research/artifacts/zp-braid-cat0-turning-face-reduction-2026-09-13.md` (cited below as *the 2026-09-13 artifact*;
notation, conditions I, II, III', IV and Theorem R are taken from there) and quote Haettel–Kielak–Schwer,
arXiv:1304.5990v2 (HKS): Definition 4.5 (universal points), Proposition 4.4 (apartments of `B_n` inside `X_n` are
noncrossing spanning trees), Lemma 4.7 (`X_n` is `π`-star-shaped at universal points), Lemma 4.8 (short loops through
universal points shrink), Theorems 2.32, 2.33 (Bowditch). Scripts live in
`experiments/zaremsky-3-06-braid-groups-cat0-frontier-2026-09-16/`.

Feeds: `diagonal-links-cat1-from-all-pair-turning-conditions`, `some-noncrossing-chain-defeats-all-pair-pivots-proof`,
`pairs-partition-and-rotation-admit-no-universal-pivot-proof`, `pairs-partition-and-rotation-are-pi-apart-in-x8`.

## 0. Conventions

- `U_n = Z/n`, points `1, ..., n` on a circle; partitions are written by their non-singleton blocks; `b(x)` counts
  blocks including singletons; `rk x = n - b(x)`; `m = n - 1`.
- `V = {y in R^n : sum y = 0}`, `f(x) = {y in V : sum_{i in Q} y_i = 0 for every block Q of x}`, `dim f(x) = rk x`.
  For a cyclic interval (or any set) `I`, write `f(I)` for `f` of the one-block partition with block `I`, the vectors
  of `V` supported on `I`.
- `B_n` is the spherical building of `S(V)` (type `A_{n-2}`, apartments = frames of `m` lines), `X_n ⊆ B_n` the diagonal
  link of `|NCP_n|`. In an apartment with frame `l_1, ..., l_m`, the vertex spanned by `{l_k : k in S}` is the unit
  vector `normalize(1_S - (|S|/m) 1)` of the sum-zero hyperplane of `R^m`, and a point of the face of a chain of
  vertices is a normalised nonnegative combination of their vectors. Hence for vertices `U, W` of ranks `a, b` with
  `k = dim U ∩ W` (they always share an apartment):

  `cos d_B(U, W) = (k - ab/m) / sqrt((a - a^2/m)(b - b^2/m))`,     `k(x, z) = n - b(x) - b(z) + b(x v_P z)`,

  where `v_P` is the join in the full partition lattice (the constraint system of `f(x) ∩ f(z)` has rank
  `b(x) + b(z) - b(x v_P z)` on `R^n`).
- `ρ` is the rotation `i ↦ i + 1`; it is an automorphism of `NCP_n`, so a simplicial isometry of `X_n` and of `B_n`
  (it permutes coordinates of `V`).
- For even `n`: `P_n = {12, 34, ..., (n-1)n}` and `ρP_n = {23, 45, ..., n1}`. For `n = 8` write `P`, `Q = ρP`.

## 1. Opposite universal pairs and the cut criterion

Two universal vertices `f(I), f(J)` (cyclic intervals) are opposite in `B_n` iff `f(I) ∩ f(J) = 0` and
`dim f(I) + dim f(J) = m`, i.e. iff `|I ∩ J| <= 1` and `|I| + |J| = n + 1`, i.e. iff `I ∩ J = {p}` and `I ∪ J = U_n`.
So opposite universal pairs are indexed by `π = (p, c)`, `p in U_n`, `1 <= c <= n - 2`:

`A_1 = {p+1, ..., p+c}`, `A_2 = {p+c+1, ..., p-1}`, `v = A_1 ∪ {p}`, `w = A_2 ∪ {p}`   (`n(n-2)` pairs).

The pairs used by HKS Theorem 4.17 and by condition IV are the *adjacent* ones, `c in {1, n-2}`: `(p, 1)` is
`v = {p, p+1}`, `w = {{p+1}, U_n \ {p+1}}`.

**Lemma C (cut criterion).** Let `F` be a chain of `NCP_n` and `π = (p, c)`. Then `F ∪ {v, w}` lies in one apartment of
`B_n` iff every block of every vertex of `F` that does not contain `p` lies inside `A_1` or inside `A_2`. Write
`compat(F)` for the set of such `π`; `compat(F) = ∩_{x in F} compat(x)`.

*Proof.* (a) A flag `F` of `S(V)` and a complementary pair `(U, W)` lie in a common frame iff every member `R` of `F`
splits: `R = (R ∩ U) ⊕ (R ∩ W)`. If they share a frame, `U, W` are spans of complementary subsets `S, S^c` of it and
`R` of a subset `T`, so `R ∩ U`, `R ∩ W` are spanned by `T ∩ S`, `T ∩ S^c`. Conversely, if every `R_j` splits, choose a
basis of `U` adapted to the flag `(R_j ∩ U)_j` and a basis of `W` adapted to `(R_j ∩ W)_j`; their union is a frame
spanning every `R_j`, `U` and `W`.
(b) For a set `I` and a partition `x`, `f(x) ∩ f(I) = {y in R^I : sum_{Q ∩ I} y = 0 for every block Q of x meeting I}`,
whose constraints have disjoint supports, so `dim f(x) ∩ f(I) = |I| - #{blocks of x meeting I}`.
(c) With `U = f(A_1 ∪ {p})`, `W = f(A_2 ∪ {p})`, the sum `(R ∩ U) + (R ∩ W)` is direct, so `R = f(x)` splits iff the
dimensions add up. The block containing `p` meets both `A_1 ∪ {p}` and `A_2 ∪ {p}`; every other block meets one or
both of `A_1`, `A_2`. So `#meet(A_1 ∪ {p}) + #meet(A_2 ∪ {p}) = b(x) + 1 + t`, where `t` is the number of blocks not
containing `p` that meet both `A_1` and `A_2`, and by (b) `dim(R ∩ U) + dim(R ∩ W) = (n + 1) - (b(x) + 1 + t) =
rk x - t`. So `R` splits iff `t = 0`. ∎

Condition IV of the 2026-09-13 artifact is exactly: *some chamber `C` of `X_n` has `compat(F) ∩ compat(C)` free of
adjacent pairs.* Indeed for `π = (p, 1)` (`i = p + 1`, `j = p`) the cut criterion says that every block containing `i`
contains `j`, i.e. `j in F_i`; the case `c = n - 2` is the mirror image `j = i + 1`.

## 2. Theorem R_all

**Condition IV_all.** There is a chamber `C` of `X_n` with `compat(F) ∩ compat(C) = ∅`.

`IV_all` implies `IV`. **Theorem R_all.** Theorem R of the 2026-09-13 artifact holds with IV replaced by IV_all.

*Proof.* Steps 0–4 and 6 are unchanged. Step 5: suppose IV_all fails for the turning face `F` of the turning point `t`
with image `x`, let `y = l(t + L/2)` and `C` a chamber of `X_n` containing `y`. Some `π = (p, c)` is in
`compat(F) ∩ compat(C)`, so by Lemma C there are apartments of `B_n` containing `F, v, w` and `C, v, w`. In each of
them `v, w` are antipodal, so `d_B(x, v) + d_B(x, w) = π = d_B(y, v) + d_B(y, w)`, and one of `v, w`, say `v`, has
`d_B(x, v) + d_B(v, y) <= π`. The pivot lemma (§3) with the universal point `v` shrinks `l`, a contradiction. ∎

Unlike step 5 of Theorem R, apartments of `B_n` suffice here: `X_n`-apartments (HKS Lemma 4.15) are replaced by HKS
Lemma 4.7.

(sections 3–7 follow)
