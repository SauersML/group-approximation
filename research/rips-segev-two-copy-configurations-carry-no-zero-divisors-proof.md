---
rg: 2
id: rips-segev-two-copy-configurations-carry-no-zero-divisors-proof
kind: route
title: A zero-face two-link lemma makes two translates of g(Gamma) meet in one bridge or in at most three cosets joined by shared b-runs; the one-copy port argument then leaves at most one clean active line per copy, so the active cosets close a positive relation of free-product length at most 10, which the graphical small cancellation lemma forbids
target: rips-segev-two-copy-configurations-carry-no-zero-divisors
requires: [rips-segev-one-copy-configurations-carry-no-zero-divisors, rips-segev-witness-supports-carry-no-zero-divisors]
---

**Conventions.**
- [EE] is `rips-segev-witness-supports-carry-no-zero-divisors-proof`, [OC] is
  `rips-segev-one-copy-configurations-carry-no-zero-divisors-proof`, [LG] is
  `rips-segev-core-large-gap-two-layer-elements-are-regular-proof`, [FL] is
  `rips-segev-steenbock-few-line-a-supports-are-regular-proof`.
- `F = <a> * <b>`, `K = F/<<R>>` with `R` the cycle labels of Steenbock's graph `Gamma`, `Gr'_*(lambda)`,
  `lambda = 1/8`, maximal piece length `Lambda < lambda gamma`, least cycle length `gamma >= 41` ([EE],
  "Coverage"; [FL] gives `gamma >= girth(Phi) >= 42`).  `|.|_*` is free-product length.
- `g : V(Gamma) -> K` as in [OC].  A *copy* is `C = h g(Gamma)`, the image in the Cayley graph of `K` (w.r.t.
  `a`, `b`) of `Gamma` under `v -> h g(v)`, with vertex set `V_C = h g(V)`.  By [EE] 1(a) this is an embedded
  labelled graph isomorphic to `Gamma`.  Two copies are *distinct* if their vertex sets differ.
- `Gamma` is reduced: every vertex has at most one incoming and one outgoing edge of each label ([FL] Lemma A).
  So a backtrack-free path has a freely reduced label, and a path is determined by its start and its label.
- *Rigidity* ([EE] "Coverage", the Rips--Segev condition): the differences of distinguished positions, over all
  lines and ordered pairs, are nonzero and pairwise distinct.  Hence a word `b^e a^n b^{e'}` with
  `n, e, e' != 0` is the label of at most one path of `Gamma`: the `a^n` segment joins two distinguished
  positions at distance `n` of one line, and that (line, pair) is unique.
- `b`-runs of `Gamma` have at most 2 edges, and the only 2-runs are `(l, O_2) -> (i, 0) -> (k, I_1)` and
  `(l', O_1) -> (i, C) -> (k', I_2)` ([FL] Lemma A).  `b`-edges of `Gamma` correspond bijectively to edges of the
  8-regular graph `Phi`, whose girth is at least 42 ([FL] Lemma C).

## 1. The two-link lemma

A *link* between copies `C_1 != C_2` is a pair `(x_1, x_2)` with `x_m in V_{C_m}` and
`x_1^{-1} x_2 in <a> ∪ <b>`.  Write `x_1^{-1} x_2 = c` with `c` the unique power `a^n` or `b^n` (both have
infinite order in `K`).

**Lemma 1.**  Let `(x_1, x_2)` and `(y_1, y_2)` be links with connectors `c`, `d`.  Then there are
backtrack-free paths `q_m` in `C_m` from `x_m` to `y_m` with `omega(q_1) = c omega(q_2) d^{-1}` in `F`.

*Proof.*
- `Gamma` is connected, so paths exist.  For any `q_1`, `q_2`, `omega(q_1)^{-1} c omega(q_2) d^{-1} = 1` in
  `K`.  Choose backtrack-free `q_1`, `q_2` and a van Kampen diagram `D` for this word with the least number of
  faces, and let `D̃` be as in [EE] Lemma 1 (originating edges deleted).
- The boundary cycle is `q̄_1^{-1} e_c q̄_2 e_d^{-1}`, with connector edges `e_c`, `e_d` of free-product length
  at most 1.
- *No face originates with `q_1` or `q_2`.*  Such a face is removed and the arc of `q_m` rerouted along its
  complementary arc inside `C_m`, exactly as in [EE] Lemma 1(b).  This lowers the face count.
- *Exterior arcs are short.*  A connected exterior arc `s` of a face `M` meets `q̄_1 ∪ q̄_2` in at most three
  arcs, since it contains at most two connector edges.  Each of those arcs has two distinct immersions into
  `Gamma` (through `M`, and as a subpath of `q_m`), so it is a piece.  Hence
  `|omega(s)|_* < 3 lambda |omega(∂M)|_* + 2`.
- *One face.*  All of `∂M` is exterior, so `|omega(∂M)|_* < 2/(1 - 3 lambda) < 4 < gamma`.
- *Two faces.*  The common arc is a piece.  So the exterior arc of either face has length
  `> (1 - lambda)|omega(∂M)|_*`, and `|omega(∂M)|_* < 2/(1 - 4 lambda) = 4 < gamma`.
- *More than two faces.*  The graphical small cancellation lemma gives a face with connected exterior arc of
  length `> (1 - 3 lambda)|omega(∂M)|_*`.  So `|omega(∂M)|_* < 2/(1 - 6 lambda) = 8 < gamma`.
- So `D̃` has no face and the identity holds in `F`. ∎

A *bridge* is a `b`-edge `z -> z b` with `z in V_{C_m} \ V_{C_{m'}}` and `z b in V_{C_{m'}} \ V_{C_m}`
(`{m, m'} = {1, 2}`).

**Corollary 2 (a bridge is the only link).**  If `z -> z b` is a bridge from `C_1` to `C_2`, then
`V_{C_1} ∩ V_{C_2} = ∅`, no `<a>`-coset meets both copies, and there is no other bridge in either direction.

*Proof.*  Any other such configuration is a link `(y_1, y_2)` with `d in {1} ∪ <a> ∪ {b, b^{-1}}`, different
from `(z, z b)`.  Apply Lemma 1 to `(z, zb)` (so `c = b`) and `(y_1, y_2)`, and reduce `W = b omega(q_2) d^{-1}`:
- If `omega(q_2)` starts with `b^{-1}`, then `q_2` begins with the edge `z -> z b` traversed backwards, so
  `z in V_{C_2}`.  Contradiction.
- Otherwise `b omega(q_2)` is reduced and starts with `b`.  Right multiplication by the single syllable
  `d^{-1}` changes only the last syllable.  The first letter `b` survives unless `b omega(q_2) = b^m` is one
  syllable, with `m >= 1`, and `d = b^{n}` with `m - n <= 0`.  Since `n <= 1`, this forces `m = n = 1`, so
  `q_2` is empty, `y_2 = z b`, `d = b` and `y_1 = z`: the same link.
- So `omega(q_1)` is reduced and starts with `b`.  Then `q_1` begins with the `b`-edge leaving `z` in `C_1`,
  which ends at `z b`.  So `z b in V_{C_1}`, a contradiction. ∎

**Corollary 3 (shared cosets).**  Let `S` be the set of left `<a>`-cosets meeting both `V_{C_1}` and
`V_{C_2}`.  Any two distinct `T, T' in S` are joined by a `b`-run `z, z b^{±1}, ..., z b^{e}`, `1 <= |e| <= 2`,
whose vertices and edges lie in both copies.  Consequently `|S| <= 3`.

*Proof.*
- Take links `(x_1, x_2)` in `T` and `(y_1, y_2)` in `T'`, so `c, d in <a>`, and apply Lemma 1.
- `q_2` joins different cosets, so `omega(q_2) = a^{p} B a^{p'}` with `B` beginning and ending in a
  `b`-syllable.  With `c = a^n` and `d = a^{n'}`, the reduced form of the right side is `a^{n+p} B a^{p'-n'}`.
  This is also the reduced word `omega(q_1)`.
- So `q_1` and `q_2` contain subpaths labelled `B` starting at the same element `z = x_1 a^{n+p}` of `T`.
- If `B` had two `b`-syllables, it would contain `b^e a^m b^{e'}` with `m != 0`.  By rigidity both subpaths
  come from the same path of `Gamma`, through one vertex `v`, with `h_1 g(v) = h_2 g(v)`.  Then `h_1 = h_2`,
  contradicting `C_1 != C_2`.
- So `B = b^e` is a `b`-run read in both copies from `z`.  `b`-runs of `Gamma` have at most 2 edges.
- *Count.*  In `C_1` the cosets of `S` are distinct lines, pairwise joined by `b`-paths of length `<= 2`,
  which project to paths of length `<= 2` in `Phi`.  Four such lines span a connected subgraph with at most 12
  edges.  Since `girth(Phi) > 12` it is a tree of diameter `<= 2`, so all four lines are within distance 1 of a
  centre line `i_0`.  Two neighbours of `i_0` can only be joined through a 2-run with middle vertex on `i_0`,
  and there are just two such runs (middles `0` and `C`).  But four lines include at least three pairs of
  neighbours of `i_0`.  This is a contradiction. ∎

## 2. The two-copy port system

Let `alpha in k[K]`, `alpha != 0`, `u, w in k[<a>]`, `w != 0`, with `alpha (u + w b) = 0` and
`supp(alpha u) ∪ supp(alpha w) ⊆ V_1 ∪ V_2`, where `V_m = h_m g(V)` for distinct copies `C_1`, `C_2`.
(If the copies coincide, this is [OC].)
- Put `X = alpha u` and `Y = alpha w`, so `X(z b) = - Y(z)` for every `z`.  If `u = 0` then `Y b = 0`, so
  `Y = 0`, which is impossible because `k[<a>]` is a domain and `alpha, w != 0`.  So `u != 0`.
- Split `alpha = sum_T alpha_T` over left `<a>`-cosets and call `T` *active* if `alpha_T != 0`.
  - Fix a base point `z_T in T` and write `alpha_T = z_T f_T(a)`.  Put `P_T = f_T u` and `Q_T = f_T w`, so that
    `X(z_T a^p) = P_T(p)` and `Y(z_T a^p) = Q_T(p)`.
  - For active `T`, both `P_T` and `Q_T` are nonzero.
- **Commutation.**  `P_T Q_{T'} = f_T f_{T'} u w = P_{T'} Q_T` for all `T`, `T'`.

**Lemma 4 (ports).**  If `Y(z) != 0`, then `z, z b in V_1 ∪ V_2`.  Moreover `z -> z b` is either an edge of a
copy `C_m`, or a bridge.  Symmetrically, if `X(z) != 0`, then `z b^{-1} -> z` is a copy edge or a bridge.

*Proof.*  `X(z b) = - Y(z) != 0`, so `z b in V_1 ∪ V_2`.
- If `z` and `z b` lie in one `V_m`, then [EE] 1(b), translated by `h_m`, makes `z = h_m g(v')` with `v'`
  non-hanging.  Its `b`-edge `v' -> v''` has `h_m g(v'') = z b` by [EE] 1(a), so `z -> z b` is an edge of `C_m`.
- Otherwise `z in V_m \ V_{m'}` and `z b in V_{m'} \ V_m`, which is a bridge.
- The second statement is the same argument at `z b^{-1}`. ∎

Call a coset *dirty* if it lies in `S` (Corollary 3) or contains an endpoint of a bridge, and *clean*
otherwise.
- A clean coset meeting `V_1 ∪ V_2` meets exactly one `V_m`, in one line `i` of `C_m` ([OC] §1, translated).
- Take `z_T = h_m g(v_{i,0})` as base point.  By Lemma 4, all edges at the ports of a clean `T` are edges of
  `C_m`.  So [OC] Lemma 2 holds verbatim: `supp Q_T ⊆ Out_i` and `supp P_T ⊆ In_i`.
- The matching `X(z b) = - Y(z)` holds along every `b`-edge, whatever the cosets.

## 3. At most one clean active line per copy

**Lemma 5.**  For `m = 1, 2`, at most one clean active coset meets `V_m`.

*Proof.*  Suppose two do, say `T` and `T'`, on lines `i != j` of `C_m`.
- *Row separation.*  All four ports are nonzero and are supported in `D_i` and `D_j` in the base points
  `h_m g(v_{i,0})` and `h_m g(v_{j,0})`.  Commutation and [OC] Lemmas 5 and 6 then give
  `supp P_T = supp Q_T ⊆ {0, C_i}`.  The same holds for every clean active coset meeting `V_m`.
- *The flanking lines.*  Say `0 in supp Q_T = supp P_T`; the case `C` is identical, with `x_3`, `x_2`,
  `O_1`, `I_2` in place of `x_4`, `x_1`, `O_2`, `I_1`.  Let `z = h_m g(v_{i,0})`.
  - `Q_T(z) != 0`, and the edge at `z` lies in `C_m`.  It is the `x_1`-edge to `v_{k, I_1}`, and by matching
    `X(h_m g(v_{k,I_1})) != 0`.
  - `P_T(z) != 0`, and the edge into `z` is the `x_4`-edge from `v_{l, O_2}`, so `Y(h_m g(v_{l,O_2})) != 0`.
  - So the cosets `T_k ∋ h_m g(v_{k, I_1})` and `T_l ∋ h_m g(v_{l, O_2})` are active.
  - If `T_k` were clean, the first bullet would put its port `I_1` inside `{0, C_k}`.  If `T_l` were clean,
    its port `O_2` would lie in `{0, C_l}`.  So both are dirty.
  - `l != k`, since otherwise the `x_4`- and `x_1`-edges at `i` would form a 2-cycle of `Phi`.  So `T_l != T_k`.
- *Bridge case.*  By Corollary 2 there is one bridge and `S = ∅`.  So exactly one dirty coset meets `V_m`,
  namely the coset of the bridge endpoint in `V_m`.  But `T_l != T_k` are both dirty and meet `V_m`.
- *No bridge.*  Then `T_l, T_k in S`.  By Corollary 3 they are joined by a `b`-run `R` of length `<= 2` lying in
  both copies.  Read `R` in `C_m`.
  - If `R` is the run `v_{l,O_2} -> v_{i,0} -> v_{k,I_1}`, then `z in V_1 ∩ V_2`, so `T in S`, contradicting
    cleanness.
  - Otherwise `R` and that run are distinct `b`-paths of `Gamma` between lines `l` and `k`, of lengths `<= 2`.
    They project to distinct reduced edge paths of `Phi` with the same ends, whose union contains a cycle of
    length `<= 4 < girth(Phi)`. ∎

## 4. A short positive relation

**Lemma 6 (short relations are trivial).**  A cyclically reduced word `W != 1` of `F` with `W = 1` in `K`
has `|W|_* > 5 gamma/8 - 1 > 24`.

*Proof.*  Run the case analysis of [LG] Lemma 3 on a minimal diagram for `W`.
- No face is impossible.  With one face, `∂M = ∂D` and `|W|_* >= gamma`.
- With two faces, or with more than two, some face has a connected exterior arc `s` with `|omega(s)|_*`
  greater than `7 gamma/8` or `5 gamma/8`, respectively.
- `s` is a subpath of the boundary cycle reading `W`.  Its normal form is a run of syllables of `W`, cut at
  both ends, so `|omega(s)|_* <= |W|_* + 1`. ∎

**Conclusion.**
- By Lemma 5 at most two active cosets are clean.  The dirty ones number at most `|S| <= 3` without a bridge
  (Corollary 3), or at most 2 with a bridge (Corollary 2).  So there are at most 5 active cosets.
- Every active `T` has some `z in supp Q_T`.  Then `X(z b) != 0`, so the coset of `z b` is active.
- Hence the directed graph on active cosets with edges `T -> T'` (for `z in supp Q_T`, `z b in T'`) has out-degree
  at least 1.  So it has a directed cycle `T_0 -> ... -> T_{L-1} -> T_0` through `L <= 5` distinct cosets.
- Choose witnesses `z_j in supp Q_{T_j}` with `z_j b in T_{j+1}`.  Then `z_j b a^{n_j} = z_{j+1}`, indices
  mod `L`, so `W = b a^{n_0} b a^{n_1} ... b a^{n_{L-1}} = 1` in `K`.
- `W` has `b`-exponent sum `L >= 1`, so its cyclic reduction is nontrivial in `F`, with `|.|_* <= 2L <= 10`.
  This contradicts Lemma 6. ∎

**In `k[G]`.**  Let `alpha in k[G]` and `h_1, h_2 in G`.
- Split `alpha` over left `K`-cosets `sK`.  Since `u + w b in k[K]`, each piece satisfies
  `alpha_s (u + w b) = 0`, with supports inside `sK ∩ (h_1 g(V) ∪ h_2 g(V))`.
- Take `alpha_s != 0`.  Then `h_m g(V) ⊆ h_m K`.  If only one of `h_1 K`, `h_2 K` equals `sK`, this is the
  one-copy case [OC].  Otherwise translate by `s^{-1}` and apply the argument above in `K`.

**Consistency check.**  With one copy, there are no dirty cosets.  Lemma 5 forbids even two active cosets, and a
single active coset gives the relation `b a^{n} = 1` of length 2.  This re-proves [OC].

## 5. Calibration

`experiments/rips-segev-two-copy-2026-09-18/two_copy_ports.py` (output `ports_results.txt`, 442 s, exit 0).
- *Model.*  A 6-line reduced graph with four random `b`-derangements `x_1..x_4` (seed 1).  Line `i` has five
  distinguished positions scaled by `M = 6^i` ("separated rows"), or all lines share positions `0..5`
  ("degenerate").
- *Gluing.*  Two copies are glued by identifying cosets with a shift, sharing `b`-edges or 2-runs, or adding
  bridges.  A gluing that puts two `b`-edges of one label at one vertex is rejected as inconsistent.
- *Search.*  All `(T_0, a)` port systems are solved exhaustively by Gaussian elimination, with `T_0` the first
  active coset in a fixed order and at most 12 (`F_2`) or 9 (`F_3`) free support bits.
- *Separated rows.*  21 valid two-copy models were searched: 16 allowed by §1 and 5 excluded by it.  Six further
  gluings were inconsistent.  All 21 give 0 consistent systems over `F_2`, and so do the 7 also run over `F_3`.
  - Allowed types: disjoint, 5 bridges, 2 shared cosets, 4 shared `b`-edges (two of them coincide), 4 shared 2-runs.
  - Excluded types: 3 double bridges, 2 double shared cosets without a shared run.
- *Degenerate control.*  The disjoint model has 32 (`F_2`) and 92 (`F_3`) consistent systems.  Every sample
  has 4 to 6 clean active cosets in one copy, so it breaks Lemma 5 exactly where row separation is dropped.  The
  one-bridge model gives the same counts.
- *Limits.*  The excluded gluings also have no solutions, so in this model the port algebra alone kills them.
  The computation does not show that Corollaries 2 and 3 are load-bearing.  The model graph has short cycles, so
  it does not test Lemma 6.

## 6. Three or more copies: where the argument stops

Let the supports lie in `V_1 ∪ ... ∪ V_N`, pairwise distinct copies, `N >= 3`.  Call `z -> z b` a *bridge*
if it is an edge of no copy, and call a coset *dirty* if it meets two copies or contains a bridge endpoint.
- *What survives.*  Lemma 1 and Corollaries 2 and 3 are statements about a pair of copies, so they hold for
  every pair `{m, m'}`.  Lemma 4 holds with "bridge" as above.  In Lemma 5, row separation and the flanking
  step hold verbatim: two clean active cosets in `C_m` force `supp P_T = supp Q_T ⊆ {0, C_i}` and two distinct
  dirty active flanking cosets `T_l`, `T_k` meeting `V_m`.
- *Same-copy flanks die.*  If `T_l` and `T_k` are both dirty through the same copy `C_{m'}`, then the bridge
  case and the no-bridge case of Lemma 5 apply unchanged to the pair `{m, m'}`.
- *Mixed flanks.*  If `T_l` is dirty only through `C_{m'}` and `T_k` only through `C_{m''}`, with
  `m' != m''`, no pairwise statement applies.  The copies `C_{m'}` and `C_{m''}` need not meet at all, and
  Lemma 1 gives nothing about them.  This is the one gap.
- *Reduction for `N = 3`.*  Suppose mixed flanks are excluded.  Then there is at most one clean active coset per
  copy, and at most 3 dirty cosets per pair (Corollaries 2 and 3), so at most `3 + 3·3 = 12` active cosets.  The
  port cycle of §4 has length `L <= 12`, so `|W|_* <= 24 < 5 gamma/8 - 1 = 24.625`, and Lemma 6 again gives a
  contradiction.  **So the three-copy theorem reduces to excluding mixed flanks.**
- *`N >= 4`.*  The same count gives `N + 3 N(N-1)/2 > 12` active cosets.  So the short-relation ending fails
  whatever happens to the flanks, and a different ending is needed.  The natural candidate treats the port
  cycle as the boundary of a van Kampen diagram and the copies it crosses as faces, with a Greendlinger-type
  bound on how many copies a short cycle can cross.
- *Why the `N`-copy theorem suffices.*  The supports of `alpha u` and `alpha w` are finite and the translates
  `h g(V)` cover `K` (every `h` lies in `h g(V)`, as `g(v_{1,0}) = 1`).  So every two-layer relation
  `alpha(u + w b) = 0` lies in finitely many copies, and the `N`-copy theorem for all `N` is exactly the
  two-layer (`b`-degree one) case of the zero-divisor conjecture for `k[G(Gamma)]`.
