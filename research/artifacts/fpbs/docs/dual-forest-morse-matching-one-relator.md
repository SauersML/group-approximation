# Dual-forest Morse matchings: fixed price for one-relator groups with a letter occurring twice

Worker `swarm-0917-w5-pull-fp-1`, 2026-09-17. This artifact proves (Q1), fixed-list attainment, of
`research/artifacts/fpbs/docs/bernoulli-morse-collapse-criterion.md` for a class of one-relator groups. It then
derives Bernoulli cost `|S| - 1/m` and fixed price for that class. The notation and conventions (cells, boundary
paths, (M1)-(M3), Theorem A) are those of Sections 1 and 2 of that artifact.

## 0. Statement

**Theorem.** Let `S` be finite, `m >= 1`, and let `w` be a cyclically reduced word in `S^{+-1}` that is not a proper
power. Suppose some `s in S` occurs exactly twice in `w`, counting occurrences of both `s` and `s^{-1}`. Put
`Gamma = <S | w^m>` and `R = {w^m}`. Then:

1. `Gamma` is infinite.
2. For every `eps > 0` the Bernoulli action `b` of `Gamma` has a Morse matching for `R` with mass at least
   `(1 - eps)/m`.
3. The Morse deficit is `m(R) = 0`, so (Q1) holds, and `C(b) = |S| - 1/m = 1 + beta_1^(2)(Gamma)`.
4. `Gamma` has fixed price `|S| - 1/m`: every essentially free p.m.p. action of `Gamma` has cost `|S| - 1/m`.

Examples in the class:

- orientable surface groups, with `w = [a_1,b_1]...[a_g,b_g]` and `m = 1` (fixed price already known);
- `Z^2` and the Baumslag-Solitar groups `<a,t | t a^p t^{-1} a^{-q}>`, where `t` occurs twice (already known);
- the Fuchsian groups `<a,b | [a,b]^m>` (already known);
- `<a,b,c | (a b a^{-1} c^2 b c^{-1})^m>` or `<a,b,c | (a b a c b^{-1} c^2)^m>` for any `m >= 1`, and in general any
  relator in which one letter is used exactly twice. We know of no fixed price reference for these (Section 6).

Nothing in the argument uses the other letters of `w`. They may occur any number of times.

## 1. Imported facts

- **(W) Weinbaum** (node `weinbaum-proper-subwords-of-relator-nontrivial`). Read on 2026-09-17 from Linton, *Residually rationally solvable one-relator groups*,
  arXiv:2407.09272v2, HTML rendering, Theorem 3.1, attributed there to [Wei72] C. M. Weinbaum, *On relators and
  diagrams for groups with one defining relation*, Illinois J. Math. 16 (1972), 308-322:
  "If F is a free group, w∈F is a word and G=F/⟨⟨w⟩⟩ is a one-relator group, then every proper non-empty subword of
  w is non-trivial in G."
  The fetched rendering may have dropped a standing hypothesis that the word is cyclically reduced. We apply (W)
  only to cyclically reduced words, so either reading suffices.
- **(F) Freiheitssatz.** From the ESTABLISHED `magnus-moldavanskii-hierarchy-with-decidable-edges`, item 1: for
  `G = <A | r>` with `r` cyclically reduced, if `A_0` omits some letter occurring in `r`, then `<A_0>` is free with
  basis `A_0`.
- **(PW) Poulin-Wróbel.** From the ESTABLISHED `one-relator-group-cost-equals-first-l2-betti-plus-one`
  (arXiv:2606.23506v1, Theorem 1.2, an unrefereed preprint): for infinite `Gamma = <S | w^m>` with `w` not a proper
  power, `cost(Gamma) - 1 = beta_1^(2)(Gamma) = |S| - 1 - 1/m`.
- **(A) Theorem A.** From the ESTABLISHED `fpbs-bernoulli-morse-collapse-criterion`: for a Morse matching `M` for a
  presentation on `S`, `C(b) <= |S| - mu(M)` and `mu(M) <= z(Phi_S)`.
- **(MAX) Bernoulli maximality.** From the ESTABLISHED `fpbs-bernoulli-maximal-cost` (Abért-Weiss, Corollary 2):
  the supremum of the costs of free p.m.p. actions is attained by the Bernoulli action.
- **(MTP) Mass transport for a free p.m.p. action.** If `Gamma` acts freely and preserves `mu`, and
  `f : X x X -> [0, infinity]` is Borel, then
  `int sum_{gamma} f(x, gamma.x) dmu(x) = int sum_{gamma} f(gamma^{-1}.y, y) dmu(y)`.
  Proof: exchange the sum and the integral (Tonelli), then substitute `y = gamma.x` in each term, using invariance
  of `mu`.

## 2. Combinatorics of the Cayley 2-complex

**Normal form.** We may replace `w` by a cyclic permutation. This conjugates `w^m` and leaves the group, cyclic
reducedness and the non-power property unchanged. We may also rename `s` to `s^{-1}`, which gives an isomorphic
presentation on a generating set of the same size, whose Cayley graphing has the same edge sets. So assume

```text
w = s v_1 s^eps v_2,     eps in {+1, -1},
```

with `v_1, v_2` words in `(S \ {s})^{+-1}`. They are freely reduced, being subwords of `w`. Put `W = w^m`,
`n = |W| = m|w|`, `u_1 = empty` and `u_2 = s v_1`. The two occurrences of `s^{+-1}` in `w` sit at positions `0` and
`o_2 = |u_2|`.

- If `eps = +1`, then `v_1 != v_2` as words, since otherwise `w = (s v_1)^2` is a proper power.
- If `eps = -1`, then `v_1` and `v_2` are nonempty, since `w` is cyclically reduced.
- In both cases `w` involves a letter other than `s`. Otherwise `w` would be `s^2`, a proper power, or `s s^{-1}`,
  which is not reduced. So `|S| >= 2` and `n >= |w| >= 3`.

**Lemma 1 (Gamma is infinite and s has infinite order).**

*Proof.* `W` is cyclically reduced, because `w` is. By (F) applied with `A_0 = {s}`, which omits a letter of `W`,
`<s>` is free on `{s}`, hence infinite cyclic. QED.

Fix a point `x` with trivial stabilizer. Via `gamma -> gamma^{-1}.x`, the orbit graph of `Phi_S` is the Cayley graph
with an edge `{gamma, gamma t}` for each `gamma` and `t in S` (Section 1 of the criterion artifact). Since `s` has
infinite order, each unordered pair `{g, g s}` is exactly one `s`-edge `(y, s)` of `Phi_S`, and it determines its
lower endpoint `g`.

**Lemma 2 (embedded boundary cycles).** For every `gamma`, the closed path that starts at `gamma` and reads `W` visits
`n` distinct vertices. Hence it traverses each edge at most once, and the first clause of (M1) holds for every edge of
every cell.

*Proof.* The path visits `gamma p_k`, `0 <= k < n`, where `p_k` is the prefix of `W` of length `k`. Suppose
`gamma p_k = gamma p_l` with `k < l < n`. Then the subword `W[k..l)` is trivial in `Gamma`. It is a proper nonempty
subword of the cyclically reduced relator `W`, contradicting (W).

Suppose an edge were traversed at two steps `k != l`. Its endpoints would give `{p_k, p_{k+1}} = {p_l, p_{l+1}}`,
with indices mod `n`. Distinctness of vertices forces either `k = l`, or `k = l+1` and `l = k+1` mod `n`, which means
`n = 2`. Both are excluded. QED.

**Cells as cosets.** The paths reading `W` from `gamma` and from `gamma w^j` have the same vertex and edge sets. Call
the left coset `gamma<w>` a *cycle*. By Lemma 2 the elements `p_{j|w|} = w^j`, `0 <= j < m`, are distinct, so `w` has
order exactly `m` and each cycle has exactly `m` base points.

**Incidences.** An *incidence* of the `s`-edge `e` is a pair `(C, i)`, with `C` a cycle and `i in {1, 2}`, such that
the loop of `C` crosses `e` at a step whose position is congruent to `o_i` mod `|w|` (`o_1 = 0`). The step at
position `j|w| + o_i` of the loop from `gamma` crosses the edge

```text
e_{gamma,i,j} = {gamma w^j u_i, gamma w^j u_i s}         for i = 1, and for i = 2 when eps = +1,
e_{gamma,2,j} = {gamma w^j u_2 s^{-1}, gamma w^j u_2}    for i = 2 when eps = -1.
```

**Lemma 3 (exactly two incidences, in distinct cycles).** Every `s`-edge `e = {g, g s}` has exactly one incidence with
`i = 1` and exactly one with `i = 2`, and the two cycles are distinct.

*Proof.* Lower endpoints are determined, so `e = e_{gamma,1,j}` iff `gamma w^j = g`. Hence the `i = 1` cycle exists
and is unique, namely `g<w>`. For `i = 2` the same computation gives the unique cycle `g u_2^{-1}<w>` when `eps = +1`,
and `g s u_2^{-1}<w>` when `eps = -1`.

Suppose both incidences had the same cycle `C`. Then the loop of `C` would cross `e` at two positions in different
classes mod `|w|`, hence at two different steps. This contradicts Lemma 2. QED.

Put

```text
t = u_2^{-1} = (s v_1)^{-1}          if eps = +1,
t = s u_2^{-1} = s v_1^{-1} s^{-1}   if eps = -1.
```

By Lemma 3, the cycles sharing an `s`-edge with `gamma<w>` are `gamma w^j t<w>` (through its `i = 1` edges) and
`gamma w^j t^{-1}<w>` (through its `i = 2` edges), for `j = 0, ..., m-1`.

**The dual graph.** `D` is the multigraph on cycles with one edge for each `s`-edge of the Cayley graph, joining its
two incidence cycles. By Lemma 3, `D` has no loops, and every cycle has degree `2m`.

**Lemma 4 (infinite dual components).** Let `H = <w, t>`. The `D`-component of `<w>` is `{h<w> : h in H}`, and it is
infinite. Left translation by `Gamma` preserves `D`, so every `D`-component is infinite.

*Proof.* The neighbours of `h<w>`, for `h in H`, are `h w^j t^{+-1}<w>`, which again have representatives in `H`.
Conversely, if `h<w>` is reachable then so are `h t^{+-1}<w>` (take `j = 0`), and `h w<w> = h<w>`. Induction on the
length of `h` as a word in `w^{+-1}, t^{+-1}` shows that every `h<w>` with `h in H` is reachable.

As `<w>` is finite, the component is infinite iff `H` is infinite. It suffices to find an element of infinite order
in `H`.

- `eps = -1`: `t = s v_1^{-1} s^{-1}` is conjugate to `v_1^{-1}`. By (F) with `A_0 = S \ {s}`, the subgroup
  `<S \ {s}>` is free on `S \ {s}`. `v_1` is a nonempty freely reduced word in this basis, hence a nontrivial
  element of a free group, hence of infinite order.
- `eps = +1`: `H` contains `t w = (s v_1)^{-1} s v_1 s v_2 = s v_2`, hence also `(s v_1)^{-1}(s v_2) = v_1^{-1} v_2`.
  This lies in the free subgroup `<S \ {s}>` and is nontrivial there, because `v_1 != v_2` are distinct reduced
  words. So it has infinite order. QED.

## 3. The dual-forest matching on the Bernoulli space

**Labels.** `X = [0,1]^Gamma` with the shift `(gamma.x)(delta) = x(gamma^{-1} delta)` and product Lebesgue measure.
Fix a Borel map `phi = (phi_1, phi_2) : [0,1] -> [0,1]^2`, defined off a null set, carrying Lebesgue measure to
Lebesgue measure on the square (interleave binary digits). Put `lambda_k(y) = phi_k(y(e))`. Under the orbit
identification `gamma -> gamma^{-1}.x`, the vertex `gamma` carries the labels `phi_k(x(gamma))`. These pairs are
independent over `gamma`, with independent uniform coordinates.

**Representatives.** The `m` base points of the cycle of the cell `(y, W)` are `w^{-j}.y`, `0 <= j < m` (in the
group picture, `gamma w^j`). Let

```text
Rep = { y : lambda_1(y) < lambda_1(w^{-j}.y) for 1 <= j < m }.
```

Almost surely the labels are distinct, so `Rep` contains exactly one base point of every cycle. The translates
`w^{-j}.Rep`, `0 <= j < m`, partition `X` modulo a null set, so `mu(Rep) = 1/m`.

**Markers.** For `eps > 0` let `A = { y in Rep : lambda_2(y) < eps }`. The event `y in Rep` depends only on
`lambda_1`, so `mu(A) = eps/m`.

**Dual distance.** For `y in Rep` and `(i, j)`, the cycle across the `s`-edge `e_{y,i,j}` has base point `g_{i,j}.y`
for a fixed `g_{i,j} in Gamma` (Section 2). Its representative is the unique `w^{-k} g_{i,j}.y` lying in `Rep`. So the
`D`-neighbours are given by `2m` Borel maps `Rep -> Rep`, and the `D`-distance `d(y)` from the cycle of `y` to the set
`A` is a Borel function `Rep -> {0, 1, ..., infinity}`.

**Lemma 5 (markers everywhere).** For almost every `y in Rep`, `d(y) < infinity`.

*Proof.* Work in the orbit of `x`, identified with `Gamma`. The partition of the cycles `Gamma/<w>` into
`D`-components does not depend on `x`. There are countably many components, each infinite by Lemma 4. Condition on
all `lambda_1`-labels. The representatives of the cycles in a fixed component `K` are then distinct fixed group
elements. Their `lambda_2`-labels are independent uniforms, independent of the conditioning, so the probability that
none is below `eps` is `prod (1 - eps) = 0`. A countable union of null events is null. QED.

**The matching.** For `y in Rep` with `0 < d(y) < infinity`, let `M(y, W)` be the first `s`-edge `e_{y,i,j}`, in
lexicographic order of `(i, j)`, whose other incidence cycle has distance `d(y) - 1`. Such an edge exists, because a
shortest `D`-path to `A` begins with one. `M` is Borel, and its domain is `D_W = { y in Rep : 0 < d(y) < infinity }`.
Write `P(y)` for the representative of the other incidence cycle of `M(y, W)`, so `d(P(y)) = d(y) - 1`, and let
`rho(y) = P^{d(y)}(y) in A` be the *root* of `y`. For `a in A` put `T(a) = { y : rho(y) = a }`, with `rho(a) = a`.

**Lemma 6 ((M1) and (M2)).**

*Proof.* (M1): `M(y, W)` lies on `bd(y, W)` and, by Lemma 2, is traversed once. (M2): distinct points of `Rep` are
distinct cycles. Suppose `M(y, W) = M(y', W) = e` with `y != y'`. By Lemma 3 these are the two incidences of `e`.
Then `d(y') = d(y) - 1` and `d(y) = d(y') - 1`, which is impossible. QED.

**Lemma 7 (children are tree children).** Let `e = M(c)` and let `e'` be a child of `e`, with `c' = M^{-1}(e')`. Then
`P(c') = c`.

*Proof.* `e' in bd(c)`, `e' != e`, and `e' = M(c') in bd(c')`. If `c = c'` then `e' = M(c) = e`, which is false. So
`c != c'` are incidence cycles of the `s`-edge `e'`. By Lemma 3 an `s`-edge has exactly two, so `c` is the other
incidence of `M(c')`, i.e. `P(c') = c`. QED.

So a chain `e_0, e_1, ...` of successive children gives cells `c_0, c_1, ...` with `P(c_{k+1}) = c_k`. They all lie in
`T(rho(c_0))`, and they are pairwise distinct, because `d(c_k) = d(c_0) + k`. An infinite chain therefore needs an
infinite tree.

**Lemma 8 ((M3): trees are finite).** Almost surely every tree `T(a)` is finite.

*Proof.* Let `E = { a in A : |T(a)| = infinity }` and `Z = { y in Rep : d(y) < infinity, rho(y) in E }`. Both are
Borel, since `|T(a)| = sum_gamma 1[rho(gamma^{-1}.a) = a]`. Apply (MTP) to `f(y, z) = 1[y in Z, z = rho(y)]`.

- The left side is `mu(Z) <= 1`.
- The right side is `int_E |T(z)| dmu(z)`, which is infinite unless `mu(E) = 0`. So `mu(E) = 0`, the right side is
  `0`, and hence `mu(Z) = 0`.

The orbits meeting `Z` form the null set `union_gamma gamma.Z`. Discard it together with the null sets of Lemma 5 and
of repeated labels. On the rest every tree is finite, so by Lemma 7 there is no infinite chain of children. QED.

## 4. Conclusion of the proof

- By Lemmas 6 and 8, `M` is a Morse matching for `R = {W}` on the Bernoulli action. By Lemma 5, its mass is
  `mu(D_W) = mu(Rep) - mu(A) = (1 - eps)/m`. This is item 2.
- (A) gives `C(b) <= |S| - (1 - eps)/m` for every `eps > 0`, so `C(b) <= |S| - 1/m`.
- By (PW) and identity (I), `z(Phi_S) = |S| - 1 - beta_1^(2)(Gamma) = 1/m`. Since `sup_M mu(M) >= 1/m` and, by (A),
  `mu(M) <= z(Phi_S)`, we get `m(R) = 0`. This is item 3, together with `C(b) >= 1 + beta_1^(2)`, from (I) or (PW).
- For a free p.m.p. action `a`, `|S| - 1/m = cost(Gamma) <= C(a) <= C(b) <= |S| - 1/m`. The first equality is (PW),
  the middle inequality is (MAX), and the last is the bound above. This is item 4. QED.

**Remark (no Bernoulli needed).** The construction uses the labels only to pick `Rep` and a small complete section
`A` of the aperiodic bounded-degree Borel graph `D`. For any free p.m.p. action, a Borel transversal of the finite
relation `<w>` and a Borel complete section of measure `< eps` meeting every infinite class (a standard marker
lemma) play the same role, and Lemmas 6-8 go through verbatim. That route bypasses (MAX), but the marker lemma was
recalled, not re-read, so the proof above uses the Bernoulli labels instead.

**Remark (the matching is well-founded but not local).** `d(y)` is almost surely finite but unbounded. So `M` is a
factor of iid with unbounded coding radius, which is permitted by (M3).

## 5. Scope, novelty and what does not transfer

**Calibration.** For `Z^2 = <a,b | [a,b]>` with `s = a`, the cycles are the unit squares and `D` joins vertically
adjacent squares, so every component is a column. The forest cuts each column into finite intervals, one per marker,
and deletes one `a`-rung for each non-root square, the rung toward its root. The surviving `a`-rungs have density
`eps`, so the remaining graphing has cost `1 + eps`, matching `C = 1`. For a genus-`g` surface the theorem returns `2g - 1`.

**Novelty (checked only against the repository).**

- Poulin-Wróbel compute `cost(Gamma)` for every infinite one-relator group. Their Remark 3.6, quoted in
  `research/artifacts/fpbs/poulin-wrobel-one-relator-cost-source-2026-09-11.md`, says their cutting method does not
  bound the Bernoulli cost.
- The criterion artifact (Section 4.3) records fixed price for one-relator groups as open.
- `bin/cairn search "one-relator fixed price"` returns no node on this class.
- The fixed-price table of Gaboriau's lecture notes, as recorded in `fpbs-bernoulli-cycle-tail-compactness`, covers
  surface groups, lattices in `SO(2,1)`, Artin groups and several other classes, but not general one-relator groups.
- Groups with an exponent-sum-zero letter are HNN extensions over free Magnus subgroups. These edge groups are
  non-amenable, so the amalgam and HNN fixed-price theorems over amenable subgroups do not apply.

We did not search the wider literature beyond these sources. The fixed price conclusion for the new members of the
class should be treated as new relative to this graph, not as a certified priority claim.

**What does not transfer.**

- *A letter occurring `k >= 3` times.* An `s`-edge then has `k` incidence cycles, and `D` becomes a `k`-uniform
  hypergraph. Lemma 7 fails: if `M(c') = e'` and `c` is any of the other `k - 1` incidences of `e'`, then `e'` is a
  child of `M(c)`. Well-foundedness therefore requires every matched hyperedge's other `k - 1` cells to be ancestors
  of its matched cell. That is a Borel peeling (Berge-acyclic orientation) condition on the incidence hypergraph,
  with mass `(1/m)(1 - density of roots)` only if almost every cell can be peeled. It is open here.
- *No letter used exactly twice.* This includes, for example, `<a,b | (a^2 b^3)^m>`-type relators where every letter
  repeats. There no edge class has exactly two incidences, and Kazhdan groups are untouched. The theorem gives nothing, and the target
  claim stays open in general.
- *Multi-relator presentations.* Lemmas 5-8 hold for any presentation whose cells are embedded and for which some
  Borel edge class has exactly two incidences in distinct cells, with infinite dual components. The mass is then the
  density of the cells in the dual graph. It equals `z(Phi_S)` only if that density is the full cycle dimension,
  which needs a separate `l^2` computation.


