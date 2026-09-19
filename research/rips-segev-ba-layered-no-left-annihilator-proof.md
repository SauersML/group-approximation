---
rg: 2
id: rips-segev-ba-layered-no-left-annihilator-proof
kind: route
title: A Greendlinger exterior arc of a face with at least 42 b-edges and b-runs of length at most 2 reads at least 18 b-edges, so visits of up to 13 edges suffice; for b-degree d >= 3 an edge of the copy cycle between two good untouched lines has a middle endpoint whose other b-edge carries level 2 into an I position or level d-2 out of an O position, so it ends at a touched coset or the bridge end and visits have at most 11 edges; for d <= 2 the row bound leaves at most 2 bad lines per copy and visits have at most 10 edges
target: rips-segev-ba-layered-elements-have-no-left-annihilator
requires: [rips-segev-rank-two-ba-elements-have-no-left-annihilator, rips-segev-ab-layered-elements-have-no-left-annihilator, rips-segev-two-layer-elements-have-no-left-annihilator, rips-segev-two-layer-cycles-split-over-copies, rips-segev-two-copy-configurations-carry-no-zero-divisors, rips-segev-one-copy-configurations-carry-no-zero-divisors, rips-segev-steenbock-few-line-a-supports-are-regular]
---

**Conventions.**
- [RT] is `rips-segev-rank-two-ba-no-left-annihilator-proof`.  Its §1 (normalization, levels, port
  polynomials), §2 (port graph `S`, Lemma 1), §3 (flow cycle, Lemmas 2–4, middle and bad lines) and §4 (row
  bound, Corollary 7) are used verbatim.
- [AB] is `rips-segev-ab-layered-no-left-annihilator-proof` (Fact M, Theorem A, Proposition 9).
- [NL] is `rips-segev-two-layer-no-left-annihilator-proof` (Lemma 1 on cycle graphs, the visit construction,
  the relation `W`, the Greendlinger step of its §1).
- [2C] is `rips-segev-two-copy-configurations-carry-no-zero-divisors-proof` (Lemma 6: Greendlinger's lemma for
  `Gr'_*(1/8)`; Corollary 3: distinct copies meet at most 3 common cosets).  [1C] is
  `rips-segev-one-copy-configurations-carry-no-zero-divisors-proof`.  [SP] is
  `rips-segev-two-layer-cycles-split-over-copies-proof` (Step 0: from `G` to `K`).
- [FL] is `rips-segev-steenbock-few-line-a-supports-are-regular-proof` (§1 gluing table, Lemma A,
  `girth(Phi) >= 42`).
- Positions on a line of `Gamma` are `0 < I_1 < I_2 < O_1 < O_2 < C`.  Sources of `b`-edges sit at
  `0, O_1, O_2, C`, targets at `0, I_1, I_2, C`, and the middles are `0, C`.
- *Fact M* ([AB]).  At a middle `p` of `Gamma`, the `b`-edge into `p` starts at an `O` position and the
  `b`-edge out of `p` ends at an `I` position.
- *Runs* ([FL] Lemma A(b)).  A maximal run of consecutive `b`-edges of one orientation along a reduced cycle of
  `Gamma` has 1 or 2 edges.  A 2-run passes through a middle.

## 1. Setting

Let `beta = sum_{j=0}^d b^j v_j`, `v_j in k[t^{±1}]` evaluated at `a`, and `alpha beta = 0` with `alpha != 0`.
Normalize as in [RT] §1: `alpha in k[K]`, `k` infinite, `d >= 1`, `v_0 != 0 != v_d`, and `n = dim span(v_j)`.
- `n <= d + 1`.  So `d = 1` forces `n <= 2`, and `d = 2` forces `n <= 3`.
- [RT] §2–§3 give the port graph `S` (minimum degree 2), the leaf block `B` with bridge end `T_B` (possibly
  undefined), the nonzero cycle `c` on `E(B)`, and the splitting `c = sum_{i <= N} c_i` over distinct copies
  `C_i` with cycle graphs `Lambda_i`.
- A coset `T` is *touched for `C_i`* if some `c_j`, `j != i`, is nonzero on an edge with an endpoint in `T`.
  An untouched vertex of `Lambda_i` lies in `V(B)` ([RT] Lemma 2.1), so if it is not `T_B` it is *good*.
- Recall [RT] Lemmas 2–4 at a good untouched vertex `T` of `Lambda_i`, with line `l` of `C_i`:
  - the edges of `S` at `T` are exactly the edges of `Lambda_i` at `T`, each a `b`-edge of `C_i` with an
    endpoint on `l`;
  - every covered point of `T` lies on `l`; at `I_1, I_2` it has `L(x) = {d}`, at `O_1, O_2` it has
    `L(x) = {0}`;
  - two middle lines are never adjacent in `Lambda_i`, and a copy has at most `n - 1` bad lines.
- *Levels along `b`.*  For `j >= 1`, `j in L(x b)` iff `j - 1 in L(x)`.  An edge `[x -> x b]` lies in `S` iff
  `L(x)` meets `[0, d-1]`, iff `L(x b)` meets `[1, d]`.

## 2. The long arc

**Lemma G (18 edges).**  Let `M` be a face of a minimal diagram as in [NL] §1, with a connected exterior arc
`s` with `|omega(s)|_* > (5/8) |omega(∂M)|_*` ([2C] Lemma 6).  Then `s` reads at least 18 `b`-edges.

*Proof.*  `∂M` reads a reduced cycle `c_M` of `Gamma`.  Let `E` be its number of `b`-edges and `beta_M` its
number of `b`-runs (maximal `b`-syllables, taken cyclically).  Let `rho = E - beta_M` be the number of 2-runs.
- *`E >= 42`.*  Map `c_M` to `Phi` (lines to vertices, `b`-edges to edges).  This gives a closed walk of
  length `E`.  It does not backtrack, cyclically.  Consecutive `b`-edges of `c_M` with the same image are the
  same `b`-edge of `Gamma` crossed back, and the `a`-segment between them is empty, so `c_M` would backtrack.
  A line of `Gamma` is a path, so `E >= 1`.  So the walk contains a cycle of `Phi`, and `E >= girth(Phi) >= 42`.
- *Syllables.*  The cyclic word `omega(∂M)` alternates `a`- and `b`-syllables, so `|omega(∂M)|_* = 2 beta_M`.
  Runs have at most 2 edges, so `E <= 2 beta_M` and `beta_M >= 21`.
- Let `beta_s` be the number of `b`-syllables of `omega(s)`.  The syllables of `omega(s)` alternate, so
  `|omega(s)|_* <= 2 beta_s + 1`.  Hence `beta_s > (5 beta_M / 4 - 1)/2 = 5 beta_M / 8 - 1/2`.
- Let `rho_s` be the number of `b`-syllables of `omega(s)` with 2 edges, and `E_s` the number of `b`-edges
  read along `s`.  Each `b`-syllable has 1 or 2 edges, so `E_s = beta_s + rho_s`.
- *Counting 2-runs.*  Interior `b`-syllables of `omega(s)` are whole runs of `c_M`.  Only the first and the last
  syllable of `omega(s)` can be proper parts of a run.
  - *No wrap* (the syllables of `omega(s)` lie in `beta_s` distinct runs).  At most 2 runs are cut, and
    `beta_M - beta_s` runs meet no syllable.  So `rho <= rho_s + 2 + (beta_M - beta_s)`.
  - *Wrap* (the first and last syllables are the two edges of one 2-run).  Then `beta_s - 1` runs meet `s`, one
    of them cut, and `beta_M - beta_s + 1` meet no syllable.  So `rho <= rho_s + 1 + (beta_M - beta_s + 1)`.
  - Either way `rho_s >= rho - 2 - beta_M + beta_s >= 40 - 2 beta_M + beta_s`, using
    `rho = E - beta_M >= 42 - beta_M`.
- *Case `beta_M >= 29`.*  `beta_s > 5 * 29/8 - 1/2 = 17.625`, so `E_s >= beta_s >= 18`.
- *Case `21 <= beta_M <= 28`.*  `E_s >= 2 beta_s + 40 - 2 beta_M > 5 beta_M / 4 - 1 + 40 - 2 beta_M
  = 39 - 3 beta_M / 4 >= 18`. ∎

- The bound is attained by the inequalities at `beta_M = 29` (`beta_s = 18`, `rho_s = 0`).  The old count
  ([NL] §1) used only `beta_s >= 13` from `|omega(∂M)|_* >= 42`.
- `experiments/rips-segev-greendlinger-arc-2026-09-19/arc_edges.py` recomputes `min E_s` over `21 <= beta_M <= 200`.

**Proposition H (visits of up to 13 edges).**  Suppose that from every state `(i, v, e)` ([NL] §1) there is a
non-backtracking walk in `Lambda_i` of length `l in [3, 13]`, starting at `v` along an edge `!= e` and ending at
a coset touched for `C_i`.  Then the splitting `c = sum_{i <= N} c_i` cannot exist.

*Proof.*  Modify the visit construction of [NL] §1 in one point.  The visit from `(i, v, e)` is the least such
walk, first by length, then lexicographically in the fixed order of the edges of `Q`.  If it ends at `v_l`,
the next state is `(j, v_l, e_l)` with `j` the least index `!= i` such that `v_l in V(Lambda_j)` ([NL]
Lemma 1.3).
- The rest of [NL] §1 is unchanged.  The states cycle, and the visits form a cyclically non-backtracking closed
  walk `ell` with `p >= 2` visits, consecutive visits in distinct copies.  Its lift is a cyclically reduced
  relation `W != 1` of `K`.  A visit is a path through distinct cosets ([NL] Lemma 1.1, `13 <= 41`).
- *Four cosets pin a copy* ([NL] §1, [2C] Corollary 3).  Three consecutive edges of a visit in `Lambda_i`
  lying in `C_M` force `C_i = C_M`.
- *One face.*  All of `ell` lies in `C_M`, and the first three edges of two consecutive visits give
  `C_i = C_M = C_j` with `i != j`.
- *Two or more faces.*  By Lemma G, `ell` has 18 cyclically consecutive edges in `C_M`, at distinct positions
  of `ell`.  Let the first `j >= 1` of them be the last `j` edges of the visit `A`.
  - If `j >= 3`, three edges of `A` lie among them, followed by `min(|A'|, 18 - j) >= 3` first edges of the
    next visit `A'`, since `18 - j >= 18 - 13 = 5`.
  - If `j <= 2`, the next visit `A'` lies entirely among the 18, since `j + |A'| <= 15`.  At least
    `18 - 2 - 13 = 3` further edges follow, and they start the visit `A''` after `A'`.  `A'' = A` is allowed
    when `p = 2`.
  - Either way two consecutive visits, in distinct copies, have three consecutive edges in `C_M`.  Both copies
    equal `C_M`, a contradiction. ∎

## 3. Coefficient rank at most 4

**Lemma 8' (windows of 11).**  Assume `n <= 4`.  Let `v_0, ..., v_13` be a non-backtracking walk in
`Lambda_i`.  Then one of `v_3, ..., v_13` is touched for `C_i`.

*Proof.*  These are 11 distinct cosets ([NL] Lemma 1.1), vertices of `Lambda_i`.  Suppose all are untouched.
- At most one is `T_B`.  The others are good, hence middle or bad lines, and at most `n - 1 <= 3` are bad
  ([RT] Corollary 7).  So at least 7 are middle lines.
- Consecutive terms are adjacent in `Lambda_i`, so no two middle lines are consecutive ([RT] Lemma 4).
- 7 pairwise non-consecutive terms need at least 13 consecutive terms, but there are 11. ∎

**Corollary 8'.**  For `n <= 4` the hypothesis of Proposition H holds.
- From `(i, v, e)` take `e_1 != e` at `v` in `Lambda_i` (degree `>= 2`) and continue without backtracking to
  `v_0 = v, ..., v_13`.  Stop at the first touched `v_t`, `3 <= t <= 13`, from Lemma 8'. ∎

- For `n = 3` the same count on `v_3, ..., v_10` (8 terms, at most 3 not middle lines, so 5 middle lines
  needing 9 terms) gives visits of at most 10 edges.  This is the case left open in [RT] §6.
- For `n = 5` a window of 11 can hold `T_B`, four bad lines and six alternating middle lines, so windows alone
  stop at `n = 4`.  Section 4 does not use the row bound.

## 4. b-degree at least 3

**Lemma P (middle ports).**  Assume `d >= 3`.  Let `e` be an edge of `Lambda_i` joining two good untouched
vertices `T, T'`.  Then an endpoint `U in {T, T'}` of `e` has a second edge `e' != e` of `Lambda_i` whose far
end `Y` is touched for `C_i` or equals `T_B`.  Moreover `Y notin {T, T'}`.

*Proof.*  Let `l, l'` be the lines of `C_i` in `T, T'`.  Orient `e = [p -> p b]` with `p in T` and
`q = p b in T'`.  By §1, `e in S`, so `p` and `q` are covered, `p` sits at a source position of `l` and `q` at a
target position of `l'`.
- *Not `O -> I`.*  Then `L(p) = {0}` and `L(q) = {d}`.  But `d in L(q)` means `d - 1 in L(p)`, so `d = 1`.
- *Not middle to middle.*  `e` is a `b`-edge of `C_i`, and Fact M forbids it.
- *Case `p` at `O`, `q` a middle; `U = T'`.*  `L(p) = {0}`, so `p in supp alpha`, and `1 in L(q)`,
  `2 in L(q b)` (`2 <= d`).  As `1 <= d - 1`, `e' := [q -> q b]` lies in `S`, and it is at `T'`, so it is an edge
  of `Lambda_i` and a `b`-edge of `C_i` (§1).  It is the `b`-edge of `C_i` out of the middle `q`, so by Fact M
  `q b` sits at an `I` position of the line of `C_i` in its coset `Y`.  If `Y` were good and untouched, §1 would
  give `L(q b) = {d}`, so `d = 2`.  Hence `Y` is touched or `Y = T_B`.
- *Case `p` a middle, `q` at `I`; `U = T`.*  `L(q) = {d}` gives `d - 1 in L(p)`, and `d - 2 in L(p b^{-1})`.
  As `d - 1 >= 1`, `e' := [p b^{-1} -> p]` lies in `S`, at `T`, so it is an edge of `Lambda_i` and the `b`-edge
  of `C_i` into the middle `p`.  By Fact M, `p b^{-1}` sits at an `O` position of the line of `C_i` in its coset
  `Y`.  If `Y` were good and untouched, `L(p b^{-1}) = {0}`, so `d - 2 = 0`.  Hence `Y` is touched or `Y = T_B`.
- `e' != e` in both cases (they are the two distinct `b`-edges of `Cay` at the middle).  `Y != U`, since `Q` has
  no loops ([2C] Lemma 6).  `Y` is not the other endpoint of `e`, since `Lambda_i` embeds in the simple graph
  `Phi` ([NL] Lemma 1.1). ∎

**Lemma 9 (short visits for `d >= 3`).**  Assume `d >= 3`.  From every state `(i, v, e)` there is a
non-backtracking walk in `Lambda_i` of length `l in [3, 11]`, starting along an edge `!= e`, ending at a coset
touched for `C_i`.

*Proof.*  Take any non-backtracking walk `v_0 = v, v_1, ..., v_11` in `Lambda_i` with first edge `!= e`
(minimum degree 2).  If some `v_t`, `3 <= t <= 11`, is touched, stop at the first one.  Otherwise all of
`v_3, ..., v_11` are untouched.
- *Tree.*  `Lambda_i` embeds in `Phi`, of girth `>= 42`.  So the `v_t` are distinct, and a vertex adjacent to
  two walk vertices `v_s, v_u` would close a cycle of length `<= 11 + 2 = 13`.  A walk vertex `v_s` adjacent to
  `v_u` is `v_{u ± 1}`, else a cycle of length `<= 12` closes.
- *Placing `T_B`.*  `T_B` is undefined, or equals one walk vertex `v_s`, or is off the walk and adjacent to at
  most one walk vertex `m_0`.  Call `t in [4, 9]` *admissible* if `T_B notin {v_{t-1}, v_t, v_{t+1}, v_{t+2}}`
  and `m_0 notin {v_t, v_{t+1}}` (when `m_0` is defined).
  - `T_B = v_s` excludes at most the 4 values `t in [s-2, s+1]`, and `m_0` excludes at most 2 values.  Only one
    of these happens, and `[4, 9]` has 6 values.  So an admissible `t` exists.
- Fix an admissible `t`.  `v_t, v_{t+1}` are untouched (indices in `[4, 10]`) and not `T_B`, so good.  Apply
  Lemma P to the edge `f = v_t v_{t+1}`: some `U in {v_t, v_{t+1}}` has an edge `e'` to `Y notin {v_t, v_{t+1}}`,
  touched or equal to `T_B`.
  - *`Y` on the walk.*  Then `Y` is a walk neighbour of `U` other than the far end of `f`: `Y = v_{t-1}` if
    `U = v_t`, and `Y = v_{t+2}` if `U = v_{t+1}`.  Both indices lie in `[3, 11]`, so `Y` is untouched, hence
    `Y = T_B`.  Admissibility excludes this.
  - *`Y` off the walk.*  If `Y = T_B`, then `U = m_0`, excluded.  So `Y` is touched.
  - With `U = v_u`, `u in {t, t+1} ⊆ [4, 10]`, the walk `v_0, ..., v_u, Y` does not backtrack (`Y` is off the
    walk), starts along an edge `!= e`, and has length `u + 1 in [5, 11]`. ∎

- No row bound is used in this section: `d >= 3` alone makes the other `Lambda_i`-neighbour of a middle port
  leave the good untouched part.  The bridge end `T_B` is the only escape, and girth handles it.

## 5. Proof of the theorem

**Theorem R' (all ranks).**  If `beta = sum_{j=0}^d b^j v_j(a) != 0`, then `alpha beta = 0` forces `alpha = 0`.

*Proof.*  Suppose `alpha != 0`, and normalize as in §1.  The splitting exists ([RT] §3 Step 1).
- *`d <= 2`.*  Then `n <= 3`, and Corollary 8' gives the hypothesis of Proposition H.
- *`d >= 3`.*  Lemma 9 gives it, for every `n`.
- Proposition H is a contradiction. ∎

**Corollary (two-sided).**  Every nonzero element supported in `<a><b>` or in `<b><a>` is a non-zero-divisor
on both sides of `k[G]`, for every field `k`.

*Proof.*  As in [RT] §5, with Theorem R' in place of Theorem R.  The involution `g -> g^{-1}` fixes `k[<a>]`.
- `x = sum_j b^j v_j`: left by Theorem R'; right, since `x gamma = 0` gives
  `gamma^* (sum_j v_j^* b^{d-j}) = 0`, which [AB] Theorem A excludes unless `gamma = 0`.
- `x = sum_j u_j b^j`: left by [AB] Theorem A; right, since `x gamma = 0` gives
  `(gamma^* b^{-d})(sum_j b^{d-j} u_j^*) = 0`, and Theorem R' gives `gamma = 0`. ∎

- Negative `b`-exponents are included: `sum_{j=-m}^{d} b^j v_j = b^{-m} beta'` and `alpha b^{-m}` is nonzero.
  The corollary is stated for `G`; [SP] Step 0 reduces it to `K` as in [RT] §1.

## 6. Checks and what is open

- *Where `d >= 3` enters.*  Only Lemma P.  For `d = 2` the case `O -> middle` gives level 2 at an `I` position,
  which purity allows (`L = {2} = {d}`).  So a chain `O -> middle -> I` of good untouched lines is possible, and
  there the row bound does the work.  For `d = 1` also `O -> I` edges occur.
- *Where the rank enters.*  Only for `d <= 2`, through Corollary 8', and then `n <= 3 <= 4`.  So the
  determinant-and-Rado row bound is needed only in rank 3 and below, and never for large `n`.
- *Where Steenbock's graph enters.*  Fact M and the runs of length `<= 2` (the gluing table of [FL] §1),
  `girth(Phi) >= 42` (Lemma G, Lemma 9 tree argument, Lemma 1.1 of [NL]), rows (Corollary 7), and
  `Gr'_*(1/8)` with 3 common cosets for distinct copies ([2C]).
- *Calibration.*  In `H_{m,n} = <a, b | (a^m b)^n>` the element `sum_{j<n} (b a^m)^j` kills `1 - b a^m`, with
  `d = 1`.  The row bound fails there ([RT] §6).  Lemma P rests on Fact M, which fails for relators with
  `b`-runs of length `>= 3`: in `<a, b | (a^m b^d)^n>` the element `sum_{j<n} (b^d a^m)^j` kills `1 - b^d a^m`.
- *Open.*  Mixed-layer supports, where `beta` is not of the form `sum b^j v_j` or `sum u_j b^j`.  Beyond
  layering, the port graph uses that every `b`-edge of a segment is an edge of `S`.  For general `beta`, the
  `a`-parts between `b`-letters vary, and the covered points at `I`/`O` positions are no longer confined to one
  level.
