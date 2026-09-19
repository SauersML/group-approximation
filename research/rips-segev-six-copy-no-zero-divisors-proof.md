---
rg: 2
id: rips-segev-six-copy-no-zero-divisors-proof
kind: route
title: Count every coset on a shell arc, not only the arrival-departure ones; a copy other than the shell copy meets at most two of them unless it shares a whole b^2-syllable with the shell, so N copies cover at most 2N + (number of b^2-syllables) arc cosets, while the arc has 13 + (number of b^2-syllables); this closes every covering by at most six copies
target: rips-segev-six-copy-configurations-carry-no-zero-divisors
requires: [rips-segev-three-copy-configurations-carry-no-zero-divisors, rips-segev-two-copy-configurations-carry-no-zero-divisors]
---

**Conventions.**
- [3C] is `rips-segev-three-copy-no-zero-divisors-proof`, [TC] is
  `rips-segev-two-copy-configurations-carry-no-zero-divisors-proof`, [OC] is
  `rips-segev-one-copy-configurations-carry-no-zero-divisors-proof`, [EE] is
  `rips-segev-witness-supports-carry-no-zero-divisors-proof`, and [FL] is
  `rips-segev-steenbock-few-line-a-supports-are-regular-proof`.
- Notation is that of [3C]: `K`, `Gamma`, `Phi` (8-regular, girth `>= 42`), `gamma >= 42`, copies
  `C = h g(Gamma)` with vertex sets `V_C`, lines, distinguished positions `D_i`, `In_i`, `Out_i`, port pairs
  `P_T = f_T u`, `Q_T = f_T w`, port supports `S_T`, active, clean and dirty cosets, bridges.
- For distinct copies `C, C'` let `S(C, C')` be the set of left `<a>`-cosets meeting both `V_C` and `V_C'`.
  [TC] Corollary 3: any two members of `S(C, C')` are joined by a `b`-run with at most 2 edges whose vertices and
  edges lie in both copies, and `|S(C, C')| <= 3`.  [TC] Corollary 2: if the pair has a bridge, `S(C, C') = ∅` and
  the bridge is its only one.
- Standing hypothesis (H_N): `alpha in k[K]`, `alpha != 0`, `u, w in k[<a>]`, `w != 0`, `alpha (u + w b) = 0`,
  and `supp X ∪ supp Y ⊆ V_1 ∪ ... ∪ V_N` for copies `C_1, ..., C_N` (the *covering*), where `X = alpha u`,
  `Y = alpha w`.

What is new here, against [3C] §5: [3C] Lemma 9 charged only the 11 *arrival-departure* cosets `U_t` of a shell
arc, at 3 per covering copy.  Here every coset touched by the arc is charged, including the source coset of the
first `b`-syllable and the middle cosets of `b^2`-syllables, and a copy is charged 3 only when it shares a whole
`b^2`-syllable with the shell.  The two changes together move the threshold from `N <= 3` to `N <= 6`.

## 1. The walk of a shell arc

Fix a directed cycle of the port digraph ([3C] Lemma 6), its closed path `pi`, the cyclically reduced label `W'`,
a minimal van Kampen diagram `D` and a shell face `M` with copy `C_M = h_M g(Gamma)`, all exactly as in [3C]
Lemma 8.  By the proof of [3C] Lemma 8 the exterior arc `s` of `M` contains 12 consecutive full `b`-syllables
`beta_1, ..., beta_12` of `W'`, with nonzero `a`-syllables between consecutive ones, and the part of `pi` read along
`s` is `h_M g(c_s)` for a backtrack-free path `c_s` of `Gamma`.

Let `sigma` be the subpath of `pi` from the start of `beta_1` to the end of `beta_12`.  Let `E` be its number of
`b`-edges and `e_2` the number of the `beta_t` equal to `b^2`.  Since `b`-runs of `Gamma` have at most 2 edges,
`E = 12 + e_2` and `12 <= E <= 24`.  Write `v_0, v_1, ..., v_E` for the `<a>`-cosets that `sigma` visits between its
`b`-edges, in order: `v_0` contains the start of `sigma`, `v_E` its end, and the `r`-th `b`-edge of `sigma` runs from
`v_{r-1}` to `v_r`.

**Lemma 1 (arc cosets).**
- (a) The cosets `v_0, ..., v_E` are pairwise distinct.  Each meets `V_M` in one line `l_r` of `C_M`, and the
  lines `l_r` are pairwise distinct.
- (b) Each `v_r` contains a point of `supp X ∪ supp Y`.  So each `v_r` is active, and each meets `V_m` for some
  covering copy `C_m`.
- (c) If `0 < r < E` and `sigma` enters and leaves `v_r` at the same vertex (the `a`-syllable at `v_r` is `a^0`),
  then the `b`-edges `r` and `r + 1` of `sigma` form one of the syllables `beta_t = b^2`.  There are exactly
  `e_2` such `r`, and for no two of them are the indices `r` adjacent.

*Proof.*
- (a) `sigma` lies in the image of `c_s`, whose `b`-edges project to a non-backtracking walk in `Phi` ([FL]
  Lemma B).  The projection of `sigma` has length `E <= 24 < 42 <= girth(Phi)`, so by [FL] Lemma C its vertices
  `l_0, ..., l_E` are pairwise distinct.  Distinct lines of one copy lie in distinct cosets ([OC] §1).
- (b) The `b`-edges of `pi` are port edges `z_j -> z_j b` with `Y(z_j) != 0` and `X(z_j b) = - Y(z_j) != 0`.
  So both endpoints of every `b`-edge of `sigma` lie in `supp X ∪ supp Y`, and every `v_r` contains such an
  endpoint.  A coset containing a point of `supp X ∪ supp Y` has `alpha_T != 0`.  That point lies in some `V_m`
  by (H_N).
- (c) The `a`-syllables of `W'` between the `beta_t` are nonzero, and inside a syllable `b^2` the `a`-exponent is
  `0` (this is how `W'` merges `b`'s, [3C] §5).  Two adjacent such `r` would give a `b`-run of 3 edges in `c_s`,
  hence in `Gamma`, which does not exist. ∎

## 2. What one other copy can see of the arc

**Lemma 2 (at most two, or a whole `b^2`).**  Let `C_m` be a copy with `C_m != C_M`, and let `A_m` be the set of
`r` with `v_r in S(C_M, C_m)`.  Then `|A_m| <= 3`, and if `|A_m| = 3` then `A_m = {r - 1, r, r + 1}` for an `r`
as in Lemma 1(c): the three cosets are those of one syllable `beta_t = b^2`.

*Proof.*
- `|A_m| <= |S(C_M, C_m)| <= 3` by [TC] Corollary 3.
- Let `|A_m| = 3` and `r_1 < r_2 < r_3` be its elements.  By [TC] Corollary 3, `v_{r_1}` and `v_{r_3}` are joined by
  a `b`-run `rho` with at most 2 edges lying in `C_M` (and in `C_m`).  Its edges are edges of `C_M`, so `rho`
  projects to a path `rho'` of length `d' <= 2` in `Phi` from `l_{r_1}` to `l_{r_3}`.
- The projection of `sigma` between these vertices is a path of length `d = r_3 - r_1 >= 2` with distinct
  vertices.  If it differed from `rho'` as a path, their union would contain a cycle of length
  `<= d + d' <= 26 < 42`.  So the two paths coincide, `d = d' = 2`, and `r_2 = r_1 + 1`, `r_3 = r_1 + 2`.
- `b`-edges of `Gamma` correspond bijectively to edges of `Phi` ([TC] Conventions), and so do the `b`-edges of the
  copy `C_M`.  So the two `b`-edges of `sigma` between `v_{r_1}` and `v_{r_3}` are the two edges of `rho`.  Since
  `rho` is a `b`-run, the second begins where the first ends: the `a`-syllable of `sigma` at `v_{r_2}` is `a^0`.
  Lemma 1(c) finishes. ∎

**Corollary 3 (union bound).**  For any family of `n` copies, all different from `C_M`, the number of `r` with
`v_r in S(C_M, C)` for some member `C` of the family is at most `2 n + e_2`.

*Proof.*  Let `x` members have `|A_m| = 3`.  By Lemma 2 their sets `A_m` are among the `e_2` triples of Lemma 1(c);
say they use `y <= min(x, e_2)` distinct triples.  The union has at most `2 (n - x) + 3 y <= 2 n + y <= 2 n + e_2`
elements, since `3 y - 2 x <= y`. ∎

## 3. The two positions of the shell copy

**Lemma 4 (shell outside the covering).**  Under (H_N), if `C_M` is none of `C_1, ..., C_N`, then `2 N >= 13`.

*Proof.*  By Lemma 1(b) each of the `E + 1 = 13 + e_2` cosets `v_r` meets some `V_m`, and it meets `V_M` by
Lemma 1(a).  So `v_r in S(C_M, C_m)` with `C_m != C_M`.  Corollary 3 for the whole covering gives
`13 + e_2 <= 2 N + e_2`. ∎

**Lemma 5 (shell inside the covering).**  Under (H_N), if `C_M = C_{m_0}` is a covering copy, then
`2 (N - 1) >= 12`.

*Proof.*
- *Purity.*  Call `v_r` *pure* if `S_{v_r} ⊆ D_{l_r}` for the base point `h_M g(v_{l_r, 0})`.  Two pure `v_r`,
  `v_r'` are active (Lemma 1(b)) with port supports in `D_{l_r}` and `D_{l_r'}`, `l_r != l_r'` (Lemma 1(a)).
  [3C] Corollary 2 then gives `alpha = 0`.  So at most one `v_r` is pure.
- *Impure cosets are linked.*  This is the argument of [3C] Lemma 9, applied to any `v_r`.  Take
  `z in v_r ∩ (supp X ∪ supp Y)` outside the distinguished positions of `l_r`, say `Y(z) != 0` (for `X(z) != 0`
  use `z b^{-1}`).
  - If `z notin V_M`, then `z in V_m` for a covering copy `C_m != C_M`, and `v_r in S(C_M, C_m)`.
  - If `z in V_M`, then `z` is a non-distinguished point of line `l_r`.  No `b`-edge of `C_M` leaves `z`, so
    `z b notin V_M` ([EE] 1(a)-(b)).  By [3C] Lemma 3(a), `z b in V_m` for a covering copy `C_m != C_M`.  Either
    `z in V_m` and `v_r in S(C_M, C_m)`, or `z -> z b` is a bridge of the pair `{C_M, C_m}`.
- *Count.*  For a covering copy `C_m != C_M` let `B_m` be the set of `r` for which `v_r` is linked to `C_m` in one
  of these two ways.  If `{C_M, C_m}` has a bridge, then `S(C_M, C_m) = ∅` and the bridge is unique ([TC]
  Corollary 2), so `|B_m| <= 1`.  Otherwise `B_m = A_m`.  In both cases Lemma 2 and the proof of Corollary 3 apply,
  so the union of the `B_m` over the `N - 1` copies has at most `2 (N - 1) + e_2` elements.
- It contains every impure `r`, and there are at least `E = 12 + e_2` of them.  So
  `12 + e_2 <= 2 (N - 1) + e_2`. ∎

## 4. The six-copy theorem

**Theorem.**  Let `k` be a field and `u, w in k[<a>]`, `alpha in k[K]` with `alpha != 0`, `w != 0` and
`alpha (u + w b) = 0`.  Then `supp(alpha u) ∪ supp(alpha w)` lies in no union of six copies `h_m g(V(Gamma))`,
`h_m in K`.  The same holds in `k[G]` with `h_m in G`.

*Proof.*  Suppose (H_N) with `N = 6`; smaller `N` reduce to it by repeating a copy.
- A port cycle exists by [3C] Lemma 6, and it is a nontrivial relation of `K`, so the diagram `D` has faces and
  the shell `M` of [3C] Lemma 8 exists.
- If `C_M` is not a covering copy, Lemma 4 needs `12 >= 13`.  If it is one, Lemma 5 needs `10 >= 12`.  Both fail. ∎

*In `k[G]`.*  As in [3C] §4: split `alpha` over the left `K`-cosets, and translate each piece into `K`.  Each
piece is supported in the copies that lie in its coset, at most six of them.

**Large girth.**  For graphs of the same shape over `Phi` of girth `g`, with `gamma >= g`, put
`m_0 = floor(5 gamma/8) + 1` and `B = min(floor((m_0 - 2)/2), floor((g - 3)/2))` (as in [3C] §5, with `g - 3`
in place of `g - 1`).  The shell arc then contains `B` consecutive full `b`-syllables with walk length
`<= 2B <= g - 3`.  Lemmas 1-5 hold with 12 replaced by `B` (and 26 by `2B + 2 <= g - 1`, as needed in Lemma 2).  So the `N`-copy theorem holds whenever `2N <= B`.
Since `B` is about `5 g/16`, this reaches `N` of about `5 g/32`.  The bound of [3C] §5 was about `5 g/48`.
- For `g = 42`: `m_0 = 27`, `B = 12`, `N <= 6`.

## 5. The coefficient input, and a three-port lemma for the next step

The only coefficient facts used are [3C] Lemma 1 (through its Corollary 2) and `X(z b) = - Y(z)`.  One more
consequence of the port equations constrains any extremal-copy argument.

**Lemma 6 (three ports).**  Under (H_N), every clean active coset `T` has at least three port edges.  They are
edges of its copy `C_m` ending (or starting) on pairwise distinct lines, all adjacent to the line of `T` in `Phi`,
and all of their cosets are dirty.

*Proof.*
- Suppose `|supp P_T| = |supp Q_T| = 1`.  Then `f_T u` and `f_T w` are monomials of `k[t^{±1}]`, so `f_T`, `u`
  and `w` are monomials (`u != 0` by the proof of [3C] Lemma 1).  Hence `u + w b = c a^p (1 + e g)` with
  `g = a^{q - p} b`, `c, e != 0`.
- `g != 1` (no relator of `K` has length 2) and `K` is torsion-free, so `g` has infinite order.  Write
  `k[K] = ⊕_h h k[<g>]` over left coset representatives.  Right multiplication by `1 + e g` preserves each summand,
  and `k[<g>] ≅ k[t^{±1}]` is a domain, so `alpha (1 + e g) = 0` forces `alpha = 0`.  Contradiction.
- So `T` has at least three ports: points of `supp P_T` (targets of `b`-edges, [OC] Lemma 2) and of `supp Q_T`
  (sources).  By [3C] Lemma 3(c) the port edges are edges of `C_m`.  Two of them ending on one line `k` would be a
  double edge or a 2-cycle of `Phi`, which girth excludes.  [3C] Proposition 4(ii) makes their cosets dirty. ∎

So in a counterexample, a copy with at most two dirty cosets has no clean active coset at all, and all of its
active cosets are dirty.

## 6. What is left

- *Exact residue at `N = 7`.*  Lemma 5 becomes an equality case.  The shell copy is a covering copy, exactly one
  arc coset is pure, and the other six covering copies see pairwise disjoint sets of arc cosets of total size
  `12 + e_2`.  So `e_2` of them share a whole `b^2`-syllable with `C_M`, the remaining `6 - e_2` share exactly two
  arc cosets each, and no pair `{C_M, C_m}` has a bridge.  Lemma 4 allows one spare coset.
- *Why this still counts.*  The bound is `2N` against a shell arc of fixed length, so it cannot reach every `N`
  for a fixed graph.  The extremal-copy lemma proposed in [3C] §6 would supply the induction, but its
  coefficient-free form is false: `rips-segev-coefficient-free-extremal-copy-lemma-fails` gives minimal coverings,
  with port-closed supports, in which every copy meets the others in at least 9 cosets.  An induction on `N` must
  therefore feed in [3C] Proposition 4 and Lemma 6 above before it looks for an extremal copy.
- *The coefficient-aware form that remains open.*  In a counterexample every copy has at most one clean active
  coset (on one common line index), with at least three dirty port neighbours.  The next statement to prove is that
  some copy of a minimal covering has at most two dirty cosets.  By Lemma 6 all of its active cosets are then
  dirty, and the rank-one lemma is to be applied to those two cosets and their outside port edges.

## 7. Checks

- *Calibration against [3C].*  With the old charging (only the 11 cosets `U_t`, 3 per copy), the inside case
  needs `3 (N - 1) >= 10`, which is [3C] Lemma 9 and Corollary 10(a).  [3C] had no count for the outside case.
  The two new inputs are the extra arc cosets (`v_0`, the `b^2` middles) and the factor 2 of Lemma 2.
- *Where the girth is used.*  Lemma 1(a) needs `E < girth(Phi)`, and Lemma 2 needs the walk-plus-run cycle bound
  `d + d' <= E + 2 < girth(Phi)`.  For `g = 42` these are `24 < 42` and `26 < 42`.  Rigidity is not used in
  §§1-4.
- *No hidden use of rigidity or of the flank analysis.*  §§1-4 use only [TC] Corollaries 2-3, [3C] Lemmas 3, 6, 8,
  Corollary 2, [FL] Lemmas B-C and [OC] §1.
