# Sprinkle-then-absorb is inert at a malnormal free stage

Author: swarm-0917-w7-w7-fp-last1 (lane: paradigm/decomposition, last mile to
`fpbs-fixed-price-universal`).

Status: the route `fpbs-mal-sprinkle-then-absorb-inert-proof` is complete.
- Its prerequisites are both ESTABLISHED:
  [[fpbs-malnormal-coset-cycles-linear-perimeter]] and
  [[fpbs-malnormal-measured-absorption-cap]].
- Freeness is proved inline.
- It has been verified by the author only. No referee has checked it yet.

This artifact closes the gap that the ESTABLISHED cap
[[fpbs-malnormal-measured-absorption-cap]] explicitly leaves open under
"Not excluded": *chains that first pay a finite-contact step and only then
absorb*. The paid step is a sparse bounded-range sprinkle of the new
generator. The absorption steps are arbitrary infinite-contact steps whose
paths cross boundedly many unsprinkled edges. The result is that the whole
chain is inert: after the payment, no absorption step adds anything.

## 0. Setting and notation

- `F` is free with basis `S`, `r = |S|`. `H <= F` is finitely generated and
  malnormal, `t in F \ H`, and `F = <H, t>`. For `Gamma_mal` stages,
  `F = F(a, s) = H_{n+1}`, `H = <a, s a s^{-2}> = H_n`, `s = b_{n+1}` and
  `t = s^{-1}` (Stallings size 3, `D = 9`, `tau = 1`).
- `A = A(F, H, t)` is the constant of
  [[fpbs-malnormal-coset-cycles-linear-perimeter]] item 2. **Import (I):** the
  number `M(k)` of simple cycles (distinct vertex cosets) through a fixed edge
  `e(g)` of the coset graph, with `k` `t`-edges, is at most `A^k`.
- `Gamma ⊇ F` is countable, and `a` is the Bernoulli shift
  `(gamma x)(delta) = x(gamma^{-1} delta)` on `(X, mu) = (Z^Gamma, nu^Gamma)`,
  where `nu` is not a point mass.
- `W ⊆ Gamma` is finite and nonempty. `B ⊆ X` is measurable with respect to
  `x|_W`, and `epsilon = mu(B)`. Put `q = epsilon^{1/|W|^2}`.
- `Theta_B = {(y, t^{-1} y) : y in B}`, and `S_1 = E_H v Theta_B`, where `E_H`
  is the orbit relation of `a|H`.

For `Gamma_mal` with `t = s^{-1}`, `Theta_B` is the set of `s`-edges
`(y, s y)`, `y in B`. That is the same `S_1` as in
[[fpbs-mal-stage-block-sprinkling-threshold]].

## 1. Freeness of the Bernoulli shift (self-contained)

**Lemma 1.** `a` is essentially free.

*Proof.* `Gamma` is infinite because it contains `F`. Fix `gamma ≠ 1`. Choose
`delta_1, delta_2, ...` inductively. Given the finite set `U_n` of elements
already used (the `delta_i` and `gamma^{-1} delta_i`, `i <= n`), pick
`delta_{n+1} ∉ U_n ∪ gamma U_n`. Then `delta_{n+1}` and
`gamma^{-1} delta_{n+1}` both lie outside `U_n`, and they differ since
`gamma ≠ 1`. So the pairs `{delta_i, gamma^{-1} delta_i}` are pairwise
disjoint.

The events `E_i = {x(delta_i) = x(gamma^{-1} delta_i)}` are independent. Each
has probability `p = sum_z nu({z})^2`, and `p < 1` because `nu` is not a point
mass. If `gamma x = x`, then every `E_i` occurs, so
`mu(Fix(gamma)) <= p^n` for all `n`, which is `0`. Take the union over the
countably many `gamma`. ∎

## 2. The class graph is the coset graph with random open edges

Fix `x` with trivial stabilizer. The map `g ↦ g^{-1} x` is a bijection
`F -> F x`.
- **Vertices.** The `H`-orbits `H y` in `F x`. We have
  `H g^{-1} x = H g'^{-1} x` iff `g' in g H`, so vertices correspond to cosets
  `g H`.
- **Potential edges.** One for each `y in F x`, written `<y>`, joining `H y`
  and `H t^{-1} y`. For `y = g^{-1} x`, `t^{-1} y = (g t)^{-1} x`, so `<y>` is
  the coset-graph edge `e(g)` from `g H` to `g t H`.
- **Open edges.** `<y>` is *open* iff `y in B`, and *closed* otherwise.
  `S_1`-classes in `F x` are exactly the unions of vertices in one component
  of the open subgraph. These are the *clusters*.

This identification is a deterministic graph (the coset graph) with a random
set of open edges, because `x` has law `mu`.

**Lemma 2 (block independence).** Any `m` distinct potential edges are all
open with probability at most `q^m`.

*Proof.* `e(g)` is open iff `g^{-1} x in B`. Since
`(g^{-1} x)(delta) = x(g delta)`, this event is measurable with respect to
`x|_{gW}`. Edges `e(g)` and `e(g')` have disjoint windows unless
`g^{-1} g' in W W^{-1}`, so each edge shares a window coordinate with at most
`|W|^2` edges, itself included. Greedy selection from the `m` edges gives
`>= m / |W|^2` edges with pairwise disjoint windows. Their events are
independent, each of probability `epsilon`. So the probability is at most
`epsilon^{m/|W|^2} = q^m`. ∎

## 3. Few-closed-edge cycles are locally finite

For a potential edge `f` and `j >= 0`, let `N_j(f)` be the number of simple
cycles of the class graph through `f` with at most `j` closed edges other than
`f`.

**Lemma 3 (property P).** If `A q < 1`, then for a.e. `x`, every potential edge
`f` of the class graph of `F x` has `N_j(f) < infinity` for every `j`.

*Proof.* Under the identification of §2, fix `g` and `j`. A simple cycle
through `e(g)` of length `k` has `k - 1` other edges. At most `j` of them are
closed in at most `sum_{i <= j} C(k-1, i) <= k^j` ways, and then the remaining
`>= k - 1 - j` edges are open. By Import (I) and Lemma 2,

```text
E N_j(e(g))  <=  sum_{k <= j+1} A^k k^j  +  sum_{k > j+1} A^k k^j q^{k-1-j}.
```

The second sum is `A^{j+1} sum_{k > j+1} k^j (A q)^{k-1-j}`, which is finite
because `A q < 1`. So `N_j(e(g)) < infinity` almost surely. Take the union over
the countably many pairs `(g, j)`. Every edge of `F x` is some `e(g)`. ∎

**The cluster graph `G`.** Its vertices are the clusters (`S_1`-classes) in
`F x`, and its edges are the closed potential edges, each joining the clusters
of its two end vertices. A closed edge inside one cluster is a *loop* of `G`.
`G` may have parallel edges. A *simple `G`-cycle of length `L >= 2`* is a
cyclic sequence of `L` distinct non-loop edges through `L` distinct clusters.

**Lemma 4 (fineness).** On the event of Lemma 3, every non-loop edge `f` of
`G` lies on only finitely many simple `G`-cycles of length at most `L`, for
every `L`.

*Proof.* Let `Z` be a simple `G`-cycle `C_0, f_1, C_1, ..., f_L, C_L = C_0`
with `f_1 = f`. In `C_i`, the edge `f_i` ends at a class `u_i` and `f_{i+1}`
starts at a class `w_i`. Join `u_i` to `w_i` by a vertex-simple path of open
edges inside `C_i` (the empty path if `u_i = w_i`), which exists because `C_i`
is an open component.
- The concatenation is a closed path of the class graph.
- Its vertices in different clusters are distinct, since the `C_i` are
  distinct, and within each cluster the path is vertex-simple. So it is a
  simple cycle through `f`.
- Its closed edges are exactly `f_1, ..., f_L`.

So `Z` lifts to a cycle counted by `N_{L-1}(f)`, and the lift recovers `Z` as
its set of closed edges. Distinct `Z` therefore have distinct lifts. Hence the
number of simple `G`-cycles through `f` of length at most `L` is at most
`sum_{L' <= L} N_{L'-1}(f) < infinity`. ∎

This is Bowditch fineness of `G` at every non-loop edge. It is the invariant
of this artifact.

## 4. Crossing number of a label

Let `phi in [[E_F]]`, with `phi y = gamma(y) y` and `gamma(y) in F`, unique by
Lemma 1. A *syllable word* for `gamma in F` is an expression
`gamma = h_0 t^{e_1} h_1 ... t^{e_j} h_j` with `h_i in H` and `e_i = ±1`. It
exists because `F = <H, t>`.

Read right to left from `y`, the word is a walk in the class graph from `H y`
to `H gamma y`:
- an `H`-letter stays at a vertex;
- a letter `t^{-1}` applied at a point `z` crosses `<z>`;
- a letter `t` applied at `z` crosses `<t z>`.

Put `kappa(y)` = the minimum, over syllable words for `gamma(y)`, of the
number of crossings of **closed** edges by the walk, counted with
multiplicity. Fix a Borel choice `P(y)` of a
minimizing word, the first in a fixed enumeration of the countable set of
words. Then `kappa(y) <= ell_H(gamma(y))`, the least number of `t`-letters in a
syllable word.

## 5. Main theorem

Recall from [[fpbs-malnormal-measured-absorption-cap]] that `S_phi` consists of
the pairs `(y, z) in S_1` with `y, z in dom phi` and `(phi y, phi z) in S_1`,
and `D_phi(S_1)` is the union of the infinite `S_phi`-classes.

**Theorem 5.** Assume `A q < 1`. Let `phi in [[E_F]]`, and suppose:

> (★) For a.e. `x in D_phi(S_1)`, the `S_phi`-class of `x` contains
> infinitely many `y` with `kappa(y) <= K`, for some finite `K = K(x)`.

Then `(x, phi x) in S_1` for a.e. `x in D_phi(S_1)`. So
`S_1 v graph(phi|D_phi(S_1)) = S_1`.

(★) holds in particular whenever `ell_H(gamma) <= k` a.e. on `dom phi`, and
more generally whenever `kappa <= k` a.e. on `dom phi`.

*Proof.* **Step 1 (mass transport).** For each `K`, let `M_K ⊆ E_F` be the
set of pairs `(y, z)` with:
- `y in dom phi` and `kappa(y) <= K`;
- `<z>` closed and crossed by `P(y)`.

This set is Borel, and `|(M_K)_y| <= K`. By the mass transport principle for
the p.m.p. relation `E_F`,

```text
∫ |M_K^z| dmu(z)  =  ∫ |(M_K)_y| dmu(y)  <=  K,
```

so `|M_K^z| < infinity` for a.e. `z`. The saturation of a null set is null,
since `F` is countable. So for a.e. `x`, simultaneously for all `K`: every
closed edge of `F x` is crossed by `P(y)` for only finitely many
`y in F x` with `kappa(y) <= K`. Intersect this with the event of Lemmas 3–4.

**Step 2 (edge-disjoint arcs).** Take such an `x` in an infinite
`S_phi`-class `Q`, with `K` as in (★). Every `y in Q` has
`[y]_{S_1} = C_1 := [x]_{S_1}` and `[phi y]_{S_1} = C_2 := [phi x]_{S_1}`.
Suppose `C_1 ≠ C_2`.

For `y in Q`, project the walk `P(y)` to `G`. Open edges stay inside a cluster,
and closed edges are `G`-edges. The projection is a `G`-walk from `C_1` to
`C_2` with at most `kappa(y)` edges. Loop-erase it to a `G`-arc `alpha(y)`: a
path through distinct clusters from `C_1` to `C_2`, with no loops, of length
between 1 and `kappa(y)`, using only closed edges crossed by `P(y)`.

Let `Q_K = {y in Q : kappa(y) <= K}`, which is infinite. Say that `y` and
`y'` in `Q_K` *conflict* if `P(y)` and `P(y')` cross a common closed edge. By
Step 1, each `y` conflicts with only finitely many `y'`, because it crosses at
most `K` closed edges, and each lies on finitely many such walks. Greedy
selection in this locally finite conflict graph gives infinitely many `y_j`
whose arcs `alpha_j = alpha(y_j)` are pairwise edge-disjoint. Each arc has
length at most `K`.

**Step 3 (arc lemma).** Let `f` be the first edge of `alpha_1`. It is not a
loop. For `j >= 2`, the edge set `alpha_1 ∪ alpha_j` has even degree at every
cluster:
- each arc has degree 1 at `C_1` and at `C_2`, which are distinct;
- each arc has degree 2 at its interior clusters and 0 elsewhere;
- the arcs are edge-disjoint and loop-free.

By Veblen's theorem it is an edge-disjoint union of simple `G`-cycles. Let
`Z_j` be the one containing `f`, so `|Z_j| <= 2K`. `Z_j` is not contained in
`alpha_1`, because a path contains no cycle. So `Z_j` contains an edge of
`alpha_j`.

The `alpha_j` are pairwise disjoint, so a fixed finite cycle `Z` equals `Z_j`
for at most `|Z| <= 2K` indices `j`. Hence the `Z_j` include infinitely many
distinct simple `G`-cycles through the non-loop edge `f`, each of length at
most `2K`. This contradicts Lemma 4. So `C_1 = C_2`, that is,
`(x, phi x) in S_1`. ∎

## 6. Chains, labels outside the stage, and properness

**Corollary 6 (chains are stationary).** Assume `A q < 1`. Let
`(S_alpha)_{alpha <= lambda}`, with `lambda` a countable ordinal, be a
transfinite chain of infinite-contact steps starting at `S_1`:
- `S_{alpha+1} = S_alpha v graph(phi_alpha|D_{phi_alpha}(S_alpha))`;
- unions are taken at limit ordinals.

Suppose each `phi_alpha in [[E_a]]`, where `a` is the Bernoulli action of
`Gamma`, and suppose each `phi_alpha` satisfies (★) relative to `S_1` on the
part of its domain where its label lies in `F`. If moreover `F` is malnormal in
`Gamma`, then `S_alpha = S_1` (mod null) for every `alpha`.

*Proof.* By transfinite induction it suffices to treat one step with
`S_alpha = S_1`. Since `S_1 ⊆ E_{a|F}`, Theorem A of
[[fpbs-malnormal-measured-absorption-cap]] (ESTABLISHED; it holds for every
free action and every Borel label) gives `gamma(x) in Q(F)` for a.e.
`x in D_phi(S_1)`. For infinite malnormal `F`, `Q(F) = F`: if
`F ∩ g^{-1} F g` is infinite, it is nontrivial, so `g in F`.

So `phi|D_phi(S_1)` has labels in `F`, and it agrees a.e. with
`phi' = phi|{gamma in F}`. Moreover `D_{phi'}(S_1) = D_phi(S_1)` up to a null
set: the `S_phi`-classes inside `D_phi` lie a.e. in `dom phi'`, and
`S_{phi'}` is the restriction of `S_phi`. Theorem 5, applied to `phi'` as an
element of `[[E_F]]`, gives that the step adds nothing. ∎

For `Gamma = Gamma_mal` every stage `H_{n+1}` is malnormal in `Gamma_mal`:
- `H_{n+1}` is malnormal in every `H_m`, by
  [[fpbs-malnormal-coset-cycles-bounded-syllables]] (last paragraph: a
  composite of malnormal inclusions is malnormal);
- every `g in Gamma_mal` lies in some `H_m`.

So Corollary 6 applies with `F = H_{n+1}` and `H = H_n`.

**Proposition 7 (the paid step is sparse and proper).** If
`q <= 1/(4 A^2)`, then

```text
mu{ x : (x, t^{-1} x) in S_1 }  <=  epsilon + 1/3  <  1/2,
```

so `S_1 ≠ E_F`. Since the closure of Corollary 6 equals `S_1`, it is
`≠ E_F` too.

*Proof.* `(x, t^{-1} x) in S_1` iff either `<x> = e(1)` is open, which has
probability `epsilon`, or there is an open path from `H x` to `H t^{-1} x`
avoiding `e(1)`. In the second case there is a vertex-simple such path, so a
simple cycle through `e(1)` all of whose other edges are open. By Import (I)
and Lemma 2 this has probability at most

```text
sum_{k >= 2} A^k q^{k-1}  =  A (A q) / (1 - A q)  <=  (1/4) / (3/4)  =  1/3,
```

using `A q <= 1/(4A) <= 1/4`. Finally `epsilon = q^{|W|^2} <= q <= 1/4`. ∎

**Combined statement.** Suppose `epsilon^{1/|W|^2} <= 1/(4 A^2)`. Pay the
finite-contact step `Theta_B`, at cost `epsilon`. Then no transfinite chain of
zero-cost infinite-contact steps in `[[E_a]]` whose `F`-labelled parts satisfy
(★) ever leaves `S_1`, and `S_1` misses the pair `(x, t^{-1} x)` on a set of
measure `> 1/2`. This holds for every `Gamma ⊇ F` in which `F` is malnormal,
including every stage of `Gamma_mal`.

## 7. Reductions covered by the same proof

1. **Multi-label sprinkles.** Consider finitely many labels
   `h_i t^{e_i} h'_i` (`h_i, h'_i in H`, `e_i = ±1`) on block sets `B_i` with
   windows `W_i`. Modulo `E_H`, the pair `(y, h_i t^{e_i} h'_i y)` equals
   `(z, t^{e_i} z)` with `z = h'_i y`:
   - for `e_i = -1` it is the potential edge `<z>`, with `z in h'_i B_i`;
   - for `e_i = +1` it is `<t z>`, with `t z in t h'_i B_i`.

   So `E_H v (all of them) = E_H v Theta_{B'}`, where `B'` is the union of the
   sets `h'_i B_i` (for `e_i = -1`) and `t h'_i B_i` (for `e_i = +1`). Since
   `g B` is measurable with respect to `x|_{gW}`, `B'` is a block factor with
   the finite window `W'` made of the corresponding translates `h'_i W_i` or
   `t h'_i W_i`. Also `mu(B') <= sum_i mu(B_i)`. The theorem applies with
   `q' = mu(B')^{1/|W'|^2}`.
2. **Interleaving.** Finitely many sprinkles interleaved with absorption
   steps reduce to one sprinkle `Theta_{∪ B_i}`. By Corollary 6 applied at each
   intermediate relation `E_H v Theta_{B_1 ∪ ... ∪ B_i}`, each absorption step
   adds nothing, provided the threshold holds for the union. The window is the
   union of the windows, and the measure is at most the sum.
3. **General stage pairs.** Nothing used `r = 2` or the specific `H`. The
   proof runs for every finitely generated malnormal `H` in a free `F` with
   `F = <H, t>`, using that pair's own constant `A(F, H, t)`. For
   `Gamma_mal` this covers every composite pair `(H_m, H_n)` with
   `t = b_m^{-1}`. The constant, however, depends on the Stallings size of
   `H_n` in the basis `(a, b_m)`, which grows with `m - n`.
4. **Sharper constant (conditional).** If the circuit lemma
   `c_m <= 2^{25 m}` of `research/artifacts/fpbs-mal-stage-coset-nerve-2026-09-17.md`
   is accepted. All three referee lenses checked it, but its node is OPEN. It
   counts vertex-simple nerve paths joining the ends of an edge and avoiding
   it. Converting them to simple cycles through a fixed edge is immediate if
   the nerve has no parallel edges, which is not checked here. That would give
   Import (I) with `A = 2^{25}`. The thresholds would then become
   `q < 2^{-25}` for Theorem 5 and `q <= 2^{-52}` for Proposition 7. The
   numerics there suggest a growth rate near 7, so the true threshold may be of
   order `1/7`. None of this is used above.

## 8. Not excluded (honest boundary)

- **kappa-escaping contact classes.** These are infinite `S_phi`-classes along
  which `kappa -> infinity` with every level set finite. The arcs are then
  unboundedly long, and Lemma 4 only controls cycles of bounded length. This is
  the one surviving form of "pay then absorb" at a single stage with a sparse
  block payment.
- **Correlated payments with growing windows.** `|W| -> infinity` sends
  `q -> 1` at fixed `epsilon`.
- **Non-Bernoulli actions.**
- **Countably many payments.** Countably many payments with total mass
  `< infinity` but unbounded windows.
- **Payments by long generators.** Payments with labels outside
  `H t^{±1} H`, for example `t'` of unbounded length, where `A(F, H, t')` is
  unbounded (compare [[fpbs-mal-long-generator-packing-growth]]).
- **Methods not presented as chains**, such as general graphings of small
  cost with no absorption structure.

## 9. Invariant, step, and what it means for the target

- **Invariant.** Almost-sure Bowditch fineness of the cluster graph `G`
  (Lemma 4). It comes from exponential circuit growth `M(k) <= A^k` (Import I)
  plus a first-moment bound under block independence.
- **Step where the class dies.** The first infinite-contact step after the
  payment. By Theorem 5, `D_phi(S_1)` already lies inside the `S_1`-classes,
  since infinitely many edge-disjoint short cluster-arcs would put one closed
  edge on infinitely many short `G`-cycles.
- **For `fpbs-mal-bernoulli-single-stage-floor`.** Its negation is
  `relC = 0`, equivalently `C(beta) = 2`. A proof of the negation of the
  "pay `epsilon`, absorb for free" shape must avoid everything in §§5–7:
  - labels outside the stage are killed by the cap's Theorem A;
  - bounded-crossing labels are killed by Theorem 5;
  - multi-label and interleaved payments are killed by §7.

  What remains is exactly §8. The next falsifiable decomposition of the floor
  claim is therefore a statement about **kappa-escaping contact**: show that a
  sparse block payment admits no `phi` with a non-null set of kappa-escaping
  infinite contact classes crossing between distinct clusters. Together with
  §8's other items, that would upgrade this inertness from a route obstruction
  to a genuine floor for chain-shaped certificates. It still would not give a
  floor for arbitrary graphings.
