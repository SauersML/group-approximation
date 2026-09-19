---
rg: 2
id: rips-segev-two-layer-no-left-annihilator-proof
kind: route
title: A walk through the copy cycles that leaves each copy after 3 to 5 cosets closes into a cyclically reduced relation whose Greendlinger arc would put 4 consecutive cosets of two distinct copies into one copy; a nowhere-zero flow on a leaf block of the port graph gives a copy cycle with at most two untouched lines per copy, one pure line by rows plus the bridge end
target: rips-segev-two-layer-elements-have-no-left-annihilator
requires: [rips-segev-two-layer-cycles-split-over-copies, rips-segev-three-copy-configurations-carry-no-zero-divisors, rips-segev-two-copy-configurations-carry-no-zero-divisors, rips-segev-one-copy-configurations-carry-no-zero-divisors, rips-segev-core-large-gap-two-layer-elements-are-regular]
---

**Conventions.**
- [SP] is `rips-segev-two-layer-cycles-split-over-copies-proof` (splitting, cycle lines, purity).
- [3C] is `rips-segev-three-copy-no-zero-divisors-proof` (rank-one lemma; Lemma 8, the face arc).
- [2C] is `rips-segev-two-copy-configurations-carry-no-zero-divisors-proof` (Corollary 3: distinct copies meet at
  most 3 common cosets; Lemma 6, Greendlinger for `K`).
- [1C] is `rips-segev-one-copy-configurations-carry-no-zero-divisors-proof` (a coset meets a copy in at most one
  line).  [LG] is `rips-segev-core-large-gap-two-layer-elements-are-regular-proof` (Lemma 3, minimal diagrams).
- Chains and cycles on `Cay` are as in [SP].  Copies are distinct if their vertex sets differ.
- The *coset graph* `Q` has the left `<a>`-cosets as vertices and one edge for each `b`-edge `[z -> z b]` of `Cay`,
  joining `z <a>` to `z b <a>`.
  - A walk in `Q` is *non-backtracking* if no edge is followed by the same edge.
  - A closed walk is *cyclically non-backtracking* if, in addition, its last and first edges differ.
- For a copy `C`, `V_C` is its vertex set.  `C` *meets* a coset `T` if `V_C ∩ T != ∅`.

## 1. The hopping lemma (Theorem 1)

Let `c = sum_{i <= N} c_i` be as in Theorem 1.

**Lemma 1 (cycle graphs).**  Let `Lambda_i ⊆ Q` be the subgraph formed by the `b`-edges of `supp c_i` and their end
cosets.
1. `Lambda_i` is isomorphic to a subgraph of `Phi` of minimum degree `>= 2`.  So a non-backtracking walk of
   length `<= 41` in `Lambda_i` visits pairwise distinct cosets.
2. Its vertices are the cosets of the cycle lines of `C_i`.
3. If a coset `T` is touched for `C_i`, that is, some `c_j` with `j != i` is nonzero on an edge with an endpoint
   in `T`, then `T in V(Lambda_j)`.

*Proof.*
1. By [1C], distinct lines of `C_i` lie in distinct cosets.  So `Lambda_i` is the image of the `b`-part of
   `supp c_i`, a subgraph of `Phi`, under a map that is injective on vertices and edges.
   - By [SP] Step 3, that subgraph has no vertex of degree 1.  It has no vertex of degree 0 by construction.
   - `girth(Phi) >= 42`, so a non-backtracking walk of length `<= 41` in it is a path.
2. This is the definition of cycle lines ([SP] Step 3).
3. Let `e` be the edge.
   - If `e` is a `b`-edge, then `e in supp c_j`, so `T in V(Lambda_j)`.
   - If `e` is an `a`-edge, it lies on the line `l` of `C_j` in `T`.  If no `b`-edge of `supp c_j` met `l`, then
     `c_j` restricted to `l` would be a chain on a finite path with zero boundary, hence zero.  So `l` is a
     cycle line of `C_j`. ∎

So the untouched cycle lines of `C_i` are the vertices of `Lambda_i` lying in no other `Lambda_j`.

*Proof of Theorem 1.*  Suppose every `C_i` has at most two untouched cycle lines.

**Visits.**  A *state* is a triple `sigma = (i, v, e)`, with `v in V(Lambda_i)` and `e` an edge of `Q` at `v`.
Fix a total order on the edges of `Q` and on the indices.  The *visit* from `sigma` is defined as follows.
- Let `e_1` be the least edge of `Lambda_i` at `v` other than `e`.  It exists, since `deg_{Lambda_i} v >= 2`.
- For `t >= 1`, let `e_{t+1}` be the least edge of `Lambda_i` at the far end `v_t` of `e_t` other than `e_t`.
  This gives a non-backtracking walk `v = v_0, v_1, ..., v_5` in `Lambda_i`.
- The cosets `v_3, v_4, v_5` are distinct (Lemma 1.1), and at most two of them are untouched.  Let `v_l` be the
  first touched one, `l in {3, 4, 5}`.  By Lemma 1.3, `v_l in V(Lambda_j)` for some `j != i`.  Take the least such
  `j`.
- The visit is `e_1, ..., e_l`, of length `l in {3, 4, 5}`, and it is followed by the state
  `sigma' = (j, v_l, e_l)`.

**The closed walk.**
- Start at any state and iterate `sigma -> sigma'`.  There are finitely many states, so the sequence is
  eventually periodic: `sigma_{s+p} = sigma_s` for some `s` and `p >= 1`.
- The copy index changes at every step, so `p >= 2`.
- Concatenate the visits from `sigma_s, ..., sigma_{s+p-1}`.  This gives a closed walk `ell` in `Q` at the coset
  of `sigma_s`, cut into `p >= 2` visits.  Each visit has 3 to 5 edges and lies in one `Lambda_i`, and consecutive
  visits, cyclically, lie in distinct copies.
- `ell` is cyclically non-backtracking.
  - Inside a visit this holds by construction.
  - At the junction into the visit from `(j, v, e)`, the arriving edge is `e`, and `e_1 != e` by construction.
    This includes the junction that closes the loop, since `sigma_{s+p} = sigma_s`.

**The relation.**  Lift `ell` to a closed path `pi` in `Cay`.
- Each edge of `ell` is a `b`-edge of `Cay`, crossed forward (label `b`) or backward (label `b^{-1}`).
- Between two consecutive `b`-edges, `pi` runs inside their common coset along the `a`-edges from the arrival point
  to the departure point.
- `pi` closes, because `ell` returns to its first coset and `pi` is closed inside that coset.
- Let `W = a^{n_1} b^{eps_1} a^{n_2} b^{eps_2} ... a^{n_L} b^{eps_L}` be its label, read cyclically, with
  `L = |ell|` and `n_t in Z`.
- `W` is cyclically reduced in `F`.
  - Each point `x` of `Cay` has exactly two `b`-edges, `[x b^{-1} -> x]` and `[x -> x b]`.
  - If `n_{t+1} = 0` and `eps_{t+1} = -eps_t`, then `pi` would leave `x` along the edge it arrived by, and `ell`
    would backtrack there.
  - So no cancellation occurs, cyclically.
- `W != 1` in `F`, since `L >= 6`, and `W = 1` in `K`, since `pi` is closed.

**Greendlinger.**  Take a minimal van Kampen diagram `D` for `W`, in the standing reading of [LG] Lemma 3, whose
faces lift to reduced cycles of `Gamma`.
- By [2C] Lemma 6 (the case analysis of [LG] Lemma 3), `D` has a face.
- *One face `M`.*  Then `∂M = ∂D`.  As in [3C] Lemma 8, the image of `∂M` in `Cay` lies in the copy
  `C_M = h_M g(Gamma)`, so all of `pi` lies in `C_M`.
- *Two or more faces.*  Some face `M` has a connected exterior arc `s` with `|omega(s)|_* > 5 gamma/8 >= 26.25`
  ([2C] Lemma 6; [3C] Lemma 8, first bullet).  So `omega(s)` has at least 27 syllables.
  - The part of `pi` read along `s` is `h_M g(c_s)` for a subpath `c_s` of a cycle of `Gamma`, so it lies in the
    copy `C_M = h_M g(Gamma)`.
  - The syllables of `omega(s)` alternate between `a` and `b`.  So at least 13 of them are `b`-syllables, each
    containing at least one `b`-edge of `pi`.
  - `s` is a subpath of the boundary cycle.  Hence `pi` has at least 13 cyclically consecutive `b`-edges in
    `C_M`, that is, 13 cyclically consecutive edges of `ell` that are edges of `C_M`.

**Contradiction.**
- *Four cosets pin a copy.*  Let three consecutive edges of one visit lie in `C_M`, and let that visit lie in
  `Lambda_i`.
  - They form a non-backtracking walk in `Lambda_i` through 4 distinct cosets (Lemma 1.1).
  - Both `C_i` and `C_M` contain the endpoints of these `b`-edges, so both meet all 4 cosets.
  - By [2C] Corollary 3, two distinct copies meet at most 3 common cosets.  So `C_M = C_i`.
- *One face.*  All edges of `ell` lie in `C_M`.  Applied to the first three edges of each of two consecutive
  visits, in copies `C_i != C_j`, this gives `C_i = C_M = C_j`.
- *Two or more faces.*  Take 13 cyclically consecutive edges of `ell` in `C_M`.
  - Let `A` be the visit containing the first of them.  At most 5 of the 13 lie in `A`.
  - The next visit `B` has at most 5 edges, so it lies entirely among the 13, and at least `13 - 5 - 5 = 3` of the
    13 edges follow `B`.
  - These are the first 3 edges of the visit `B'` after `B`, since `|B'| >= 3`.  Here `B' = A` is allowed when
    `p = 2`.
  - So three consecutive edges of `B` and three of `B'` lie in `C_M`.  With `B` in `C_i` and `B'` in `C_j`,
    `i != j`, this gives `C_i = C_M = C_j`.
- Both cases contradict the distinctness of the copies `C_1, ..., C_N`.  So some `C_i` has at least three
  untouched cycle lines. ∎

*Remarks.*
- `N = 1` is included.  Then no coset is touched, and the hypothesis "at most two untouched cycle lines" already
  fails at `v_3, v_4, v_5`.
- Only three inputs are used: `girth(Phi) >= 6`, at most 3 common cosets for distinct copies, and a Greendlinger
  arc of at least 26 syllables.

## 2. No left annihilators (Theorem 2)

Let `alpha (u + w b) = 0`, with `alpha != 0` and `w != 0`.
- By [SP] Step 0 we may take `alpha in k[K]`.
- Replace `k` by `k(s)`.  The relation persists and every lemma cited holds over every field.  So `k` is infinite.
- `u != 0`: otherwise `alpha w b = 0`, so `alpha w = 0`.  Then `alpha_T w = 0` on every coset, and `k[t^{±1}]` is a
  domain.
- Put `X = alpha u` and `Y = alpha w`.  Then `X(z b) = -Y(z)` ([SP] Step 1).  On a coset `T`, `P_T = f_T u` and
  `Q_T = f_T w` as in [SP].  `T` is *active* if `f_T != 0`, equivalently `P_T != 0`, equivalently `Q_T != 0`.

**Step 1 (port graph).**  Let `S ⊆ Q` consist of the edges `[y -> y b]` with `Y(y) != 0`.
- Its end cosets are active: `y <a>` because `Q_{y<a>} != 0`, and `y b <a>` because `X(y b) = -Y(y) != 0`.
- At an active `T`, some `y in T` has `Y(y) != 0`, which gives an edge of `S` leaving `T`.  Some `x in T` has
  `X(x) != 0`, which gives the edge `[x b^{-1} -> x]` of `S` entering `T`.
- These two edges are distinct, since `Q` has no loops ([2C] Lemma 6: `b a^n` is not a relation).  So every vertex
  of the finite graph `S` has degree `>= 2`.

**Step 2 (leaf block).**  Take a connected component of `S` and its 2-edge-connected blocks, joined by bridges
into a tree.
- If there is one block, let `B` be the component and `T_B` be undefined.
- Otherwise let `B` be a leaf block, and `T_B` the end of its unique bridge in `B`.  `B` is not a single vertex,
  since that vertex would have degree 1 in `S`.
- Call `T in V(B)` *good* if `T != T_B`.  Every edge of `S` at a good `T` lies in `B`.  A non-bridge edge at `T`
  lies in the block of `T`.  A bridge at `T` would be a second bridge at the leaf block `B`.

**Step 3 (flow cycle).**
- *Flow.*  `B` is 2-edge-connected with at least one edge, so every edge `e` of `B` lies on a cycle.  Hence
  `{F in Z_1(B; k) : F(e) = 0}` is a proper subspace of the cycle space `Z_1(B; k)`.
  - `k` is infinite, so the finitely many such subspaces do not cover `Z_1(B; k)`.
  - This gives a nowhere-zero flow `F` on `B`: `F(e) != 0` for every edge `e` of `B`, and at every vertex
    inflow equals outflow.
- *Lift.*  Put `c_b = sum F(y) [y -> y b]` over the edges `[y -> y b]` of `B`.
  - At each coset `T`, the part of `∂ c_b` on `T` is a finite 0-chain on the line `T` with coefficient sum 0,
    by conservation of `F` at `T`.
  - So it is `∂ phi_T` for a unique finite chain `phi_T` on the `a`-edges of `T`.
  - Then `c = c_b - sum_T phi_T` is a finite 1-cycle on `Cay`.  It is nonzero, since `c_b != 0`.
- *Key property.*  The `b`-edges on which `c` is nonzero are exactly the edges of `B`.
- By [SP] Step 2, which holds for every finite cycle, `c = sum_{i <= N} c_i` with distinct copies `C_i` and
  `0 != c_i in Z_1(C_i; k)`.

**Step 4 (good untouched lines are pure).**  Let `l` be an untouched cycle line of `C_i`, in the coset `T`.
- *In `B`.*  `c_i` is nonzero on a `b`-edge `e` of `C_i` at `l`.  As `T` is untouched, `c(e) = c_i(e) != 0`.  So
  `e in E(B)` and `T in V(B)`.
- Suppose `T` is good.  Then `T` is active, since `V(B) ⊆ V(S)`.
- *Out-ports.*  Let `z in T` with `Y(z) != 0`.
  - Then `[z -> z b] in S` is at the good coset `T`, so it lies in `B`, and `c` is nonzero on it.
  - As `T` is untouched, `c_i` is nonzero on it.  So it is a `b`-edge of `C_i` with source `z in C_i ∩ T = l`,
    at a position in `Out_l`.
- *In-ports.*  Let `x in T` with `X(x) != 0`.  Then `Y(x b^{-1}) != 0`, and in the same way `[x b^{-1} -> x]` is a
  `b`-edge of `C_i` with target `x`, at a position in `In_l`.
- Taking the start of `l` as base point, `S_T = supp P_T ∪ supp Q_T ⊆ D_r`, where `r` is the row of `l`.  This is
  the conclusion of [SP] Step 4, reached here without `u(1) + w(1) = 0`.

**Step 5 (at most two untouched lines per copy).**
- Two good untouched cycle lines of one copy `C_i` lie in distinct cosets ([SP] Step 3) and have distinct rows,
  because `phi` is injective.
- By [SP] Step 4, `(D_r - D_r) ∩ (D_{r'} - D_{r'}) = {0}` for `r != r'`.  So the rank-one lemma of [3C], applied
  to these two active cosets, gives `alpha = 0`, which is a contradiction.
- So each copy has at most one good untouched cycle line, and at most one more, in `T_B`.  This contradicts
  Theorem 1.  Hence `alpha (u + w b) = 0` with `w != 0` forces `alpha = 0`.

**Step 6 (the other orientation, and the involution).**
- `u + w b^{-1} = (w + u b) b^{-1}`.  So `alpha (u + w b^{-1}) = 0` gives `alpha (w + u b) = 0`.
  - If `u != 0`, Step 5 gives `alpha = 0`.
  - If `u = 0`, then `alpha w = 0`, and `alpha = 0` as in the preliminaries.
- The involution `x -> x^*` of `k[G]`, induced by `g -> g^{-1}`, reverses products.  It sends `u + w b^{±1}` to
  `u^* + b^{∓1} w^*`.  So `(u' + b^{±1} w') beta = 0` with `w' != 0` forces `beta = 0`. ∎

## 3. What is not covered

- *Right annihilators.*  Let `(u + w b) alpha = 0`.  Put `X = u alpha` and `Y = w alpha`.  Then `X(b z) = -Y(z)`.
  - The natural cosets are now the right cosets `<a> z`, joined by `z -> b z`.
  - The copies, though, are left translates `h g(Gamma)`, whose lines lie in left cosets.  So neither the port
    graph nor the walk of §1 transfers.
  - By the involution this is the same as left annihilators of `w' + b u'`.
- *Higher `b`-degree.*  For `alpha (u_0 + u_1 b + ... + u_d b^d) = 0` with `d >= 2`, the port graph is no longer
  a graph on cosets with one edge per port.  Step 1 has no direct analogue.
- *Calibration.*  In `<a, b | (a^m b)^n>` the relation `sum_j (a^m b)^j (1 - a^m b) = 0` gives a single relator
  loop as flow cycle, with `n` untouched lines of one port pattern.  Theorem 1 holds.  Step 5 is what fails:
  without distinct rows the rank-one lemma separates nothing.
