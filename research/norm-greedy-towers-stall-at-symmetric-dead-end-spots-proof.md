---
rg: 2
id: norm-greedy-towers-stall-at-symmetric-dead-end-spots-proof
kind: route
title: A placed symmetric rim spot at a dead end is pulled inside the tested region by the dead end, while geometric tests translate with the copy
target: norm-greedy-towers-stall-at-symmetric-dead-end-spots
requires: []
---

Notation as in the target and in `greedy-maximal-margin-towers-never-stall`.
Two facts are used throughout.
- Right multiplication by `w` changes length by at most `|w|`, so
  `|xw| ≤ |x| + |w|`.
- `w_{R_n}(q,c) = p` means `q(μc) = p(μ)` for every `μ ∈ B(R_n)`, which is
  defined when `B(R_n)c ⊆ B(R)`, in particular when `|c| ≤ R − R_n`.

**Lemma 0 (dead-end descent).** Let `y` be a right dead end of depth `k` and
`|w| > k`. Then `|yw| ≤ |y| + |w| − k`.

*Proof.* Split a geodesic word for `w` as `w = w_1 w_2` with `|w_1| = k` and
`|w_2| = |w| − k`. Then `|yw| ≤ |yw_1| + |w_2| ≤ |y| + |w| − k`. ∎

**Proof of Theorem 1.** Fix an admissible `R ≥ R_n + 2(n+1)` and suppose
`q ∈ F_n(R)`. By (K) there is `c` with `|c| ≤ R − R_n` and
`w_{R_n}(q,c) = p`.

*Step 1: `|yc| ≤ R − R(s) − |s|`.*
- If `|c| ≤ k`, then `|yc| ≤ |y|` by hypothesis 3, and
  `|y| ≤ R_n + (2n+2) − R(s) − |s| ≤ R − R(s) − |s|` by hypothesis 4.
- If `|c| > k`, Lemma 0 and hypothesis 4 give
  `|yc| ≤ |y| + |c| − k ≤ |y| + R − R_n − k ≤ R − R(s) − |s|`.

*Step 2: the test `(s, yc)` fails.* By Step 1, clause (A) of `F_n(R)` applies
to `(s, yc)`. Let `μ ∈ B(R(s))`. By hypothesis 1, `μy ∈ B(R_n)` and
`μsy ∈ B(R_n)`. So

`q(μ·yc) = p(μy) = p(μsy) = q(μs·yc)`,

where the middle equality is hypothesis 2. No `μ` separates, so `q` violates
(A). This contradicts `q ∈ F_n(R)`. Hence `F_n(R) = ∅` for every admissible
`R`. ∎

**Proof of Proposition 2.** Since `n ≥ 1`, `p ∈ L_n = F_{n−1}(R_n)`. Clause
(A) of `F_{n−1}(R_n)` tests `(s, y)` whenever `|y| ≤ R_n − R(s) − |s|`, and
hypothesis 2 says that test fails. So `|y| > R_n − R(s) − |s|`. Combined with
hypothesis 4, `R_n − R(s) − |s| < R_n + min(k, 2n+2) − R(s) − |s|`, so
`min(k, 2n+2) ≥ 1` and `k ≥ 1`. Without dead ends, every `y` has a generator
`a` with `|ya| = |y| + 1 > |y|`, so no `y` has depth `≥ 1`. ∎

**Proof of Theorem 3.**

*Item 1.* Suppose `|c| ≤ R − R(s) − |s|` and `μ ∈ B(R(s))`. Then
`|μc| ≤ R(s) + |c| ≤ R` and `|μsc| ≤ R(s) + |s| + |c| ≤ R`, so
`Q_c(s) ⊆ B(R)`. Every test of (A) is therefore a test of (A_geo).

For decidability:
- `Q_c(s) ⊆ B(R)` forces `c ∈ B(R)` (take `μ = 1`) and `sc ∈ B(R)`, so
  `s ∈ B(2R)`. Only finitely many pairs `(s, c)` occur.
- For each pair, `R(s)` is computable and `Q_c(s)` is a computable finite
  list. Membership in `B(R)` is decidable by the word problem.
- (C) and (K) are unchanged.
- At level `0` no pair qualifies, since `Q_c(s) ⊆ B(0) = {1}` would need
  `c = sc = 1`. So `L^geo_0 = L_0`, the single letters.

*Item 2 (coherence).* Let `Q_{c'}(s) ⊆ B(R_n)c` and put `x = c' c^{-1}`.
Right multiplication by `c` is a bijection with
`B(R(s))x·c = B(R(s))c'` and `B(R(s))sx·c = B(R(s))sc'`, so
`Q_{c'}(s) = Q_x(s)c` and `Q_x(s) ⊆ B(R_n)`. By (A_geo) for `p` with radius
`R_n`, some `μ ∈ B(R(s))` has `p(μx) ≠ p(μsx)`. Both points lie in `B(R_n)`,
so `q(μc') = q(μxc) = p(μx) ≠ p(μsx) = q(μsxc) = q(μsc')`. ∎

*Item 3.*
- For `n ≥ 1`, every member of `L^geo_n = F^geo_{n−1}(R_n)` satisfies (A_geo)
  with radius `R_n`. Take `Q_y(s) ⊆ B(R_n)`. The test `(s, y)` is then one of
  its tests, so `p` is not `s`-symmetric at `y`. So hypotheses 1 and 2 of
  Theorem 1 cannot hold together in the (A_geo) recursion.
- For `n = 0`, `B(0)` contains no `Q_y(s)`.
- The windows supplied by (K) and (C) of `q ∈ F^geo_n(R)` are placed at `c`
  with `|c| ≤ R − R_n`, so `B(R_n)c ⊆ B(R)`. Item 2 applies to each of them.
  So a test of `q` can fail only when its read set lies in no single placed
  copy. ∎

**Why the norm clause is not coherent.** Under (A), `p ∈ L_n` is tested only
at `x` with `|x| ≤ R_n − R(s) − |s|`. After placement at `c`, the copy of the
spot `x = y` sits at `yc`. A dead end at `y` keeps `|yc|` at most
`R − R(s) − |s|` for every allowed `c` (Step 1). So the new ball tests
positions that the old ball, measured by norm, left untested. (A_geo)
measures tested positions by containment of the read set. Containment is
preserved by right translation, so the tested positions of a copy are exactly
the translates of its own tested positions.
