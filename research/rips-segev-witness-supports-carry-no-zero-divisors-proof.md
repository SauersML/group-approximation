---
rg: 2
id: rips-segev-witness-supports-carry-no-zero-divisors-proof
kind: route
title: Hanging b-letters stay off the graph, so free a-line indices force alpha onto adjacent distinguished positions and rank-one beta factors
target: rips-segev-witness-supports-carry-no-zero-divisors
requires: []
---

**Conventions.**  Everything follows Steenbock, arXiv:1307.0981.  The citations are:
- Theorem "gi": graphs with the `Gr'_*(1/6)` condition inject into the Cayley graph.
- Theorem "tf": `Gr'_*(1/8)` gives a torsion-free group.
- The graphical small cancellation lemma.
- The proposition that `A` and `B` embed.

Further conventions:
- `F = G_1 * G_2`, `1 != a in G_1`, `1 != b in G_2`, both factors torsion-free.
- `Gamma = Theta'` is a generalized Rips--Segev graph with coefficients `(I,O,C)`, with its labeling satisfying
  `Gr'_*(lambda)` for `lambda = 1/8`.  The `c_i` are labels of shortest paths from `v_10` to `v_i0`, so
  `Gamma` is exactly the graph of Steps 1--3.  It is connected, and its labeling by `{a^{±1}, b^{±1}}` is reduced
  (consecutive edges never cancel).
- `G = G(Gamma)`.  For a vertex `v`, `g(v) in G` is the image of the label of any path from `v_10` to `v`.  This
  is well defined because cycle labels are relators, and `g(v_il) = c_i a^l`.
- `|.|_*` is free product length, `Lambda` the maximal piece length, `gamma` the minimal cycle length, so
  `Lambda < lambda gamma`.

**Vertices of `Gamma`.**  The vertices are the a-line vertices `v_il`, `0 <= l <= C_i`; no two of them are
identified.
- Step 1 identifies each `w_{i0}`, `w_{iC_i}` with a vertex `v_{jI}`, with distinct pairs `(j,I)`.
- Step 2 identifies each remaining `v_{j0}`, `v_{jC_j}` with a vertex `w_{lO}`, `0 < O < C_l`.
- Step 3 deletes every other `w`.

So a vertex `v_il` carries a `b`-edge only if `l` is *distinguished*, meaning `l in D_i := {0, C_i} ∪ I_i ∪ O_i`.
- The source of every `b`-edge is some `v_jn` with `n in {0, C_j} ∪ O_j`.
- Its target is the vertex it was glued to: some `v_{kI}` with `I in I_k`, or some `v_{k0}`, `v_{kC_k}`.  In
  every case the target position is distinguished.

Call `v_jn` *hanging* if `n notin {0, C_j} ∪ O_j`.  Equivalently, `v_jn` has no outgoing `b`-edge.

---

## Lemma 1 (exact encoding)

(a) `g` is injective on vertices of `Gamma`.

(b) If `v` is hanging and `u` is any vertex of `Gamma`, then `g(v) b != g(u)`.

(c) If `v, v'` are vertices and `g(v) b = g(v') b`, then `v = v'`.

*Proof.*
- (a) is Theorem "gi" for the one-graph family `Gamma`.
- (c) follows from (a) by cancelling `b`.

*(b).*  Suppose `g(v) b = g(u)`.  For every path `q` in `Gamma` from `v` to `u`, `omega(q) = g(v)^{-1} g(u) = b`
in `G`, so the word `omega(q) b^{-1}` is trivial in `G`.
- Among all such `q`, choose `q` and a minimal van Kampen diagram `D` for `omega(q) b^{-1}` over the relators of
  `Gamma` so that the number of faces `|D|` is as small as possible.
- The minimal number of faces depends only on the element `omega(q) in F`, and deleting backtracks from `q` does
  not change that element.  So we may assume `q` has no backtracking.
- Write the boundary cycle of `D` as `q̄ e`, where `q̄` is a copy of `q` and `e` is one edge labelled `b^{-1}`.

*No face originates with `q`.*  Call a face `M` of `D̃` *originating with `q`* if its exterior boundary contains
a subpath `s` of `q̄` whose lift to `Gamma` with `M` coincides with the lift of `s` to the subpath of `q`.
- Suppose such an `M` exists.  Remove its interior together with `s`, as in the proof of Theorem "gi".  If this
  disconnects the diagram, discard every component that does not contain `e`.
- The complementary arc of the boundary cycle of `M` lifts to a path in `Gamma` between the endpoints of `s`.
  Replacing `s` by that arc turns `q` into a path `q'` in `Gamma` from `v` to `u`.
- The new diagram is a van Kampen diagram for `omega(q') b^{-1}` with fewer faces.  This contradicts the choice
  of `q`.

*Exterior arcs inside `q̄` are short.*  Let `M` be a face of `D̃` whose exterior boundary contains a connected
arc `s` inside `q̄` (so `e notin s`).
- Since `M` does not originate with `q`, the arc `s` has two distinct immersions into `Gamma` with the same
  label: one through the boundary cycle of `M`, one as a subpath of `q`.
- In a reduced labeling by `{a^{±1}, b^{±1}}`, two immersions with the same label that agree at one vertex agree
  everywhere, because a vertex carries at most one edge with a given label.  So these immersions are distinct
  and `s` is a piece.
- Hence `|omega(s)|_* <= Lambda < lambda gamma <= lambda |omega(∂M)|_*`.

*Case `|D| = 0`.*
- `omega(q) = b` in `F`.  A backtrack-free path in a reduced graph has a freely reduced label in `a^{±1}`,
  `b^{±1}`.  Since `a` and `b` have infinite order, such a word represents `b` in `F` only if it is the
  one-letter word `b`.
- So `q` is a single `b`-edge leaving `v`.  But `v` is hanging, a contradiction.

*Case: `D̃` has more than two faces.*
- By the graphical small cancellation lemma, at least two exterior faces `M_1`, `M_2` have a connected exterior
  boundary with `|omega(∂_ext M_j)|_* > (1 - 3 lambda) |omega(∂M_j)|_*`.
- Distinct faces have edge-disjoint exterior boundaries, so one of them, say `M`, does not contain `e`.  Then
  `s = ∂_ext M` lies inside `q̄`.
- The previous paragraph gives `|omega(s)|_* < lambda |omega(∂M)|_*`.  This contradicts
  `|omega(s)|_* > (1 - 3 lambda) |omega(∂M)|_*`, because `lambda = 1/8 < 1 - 3 lambda`.

*Case: `D̃` has one face `M`.*
- Every edge of `∂M` is exterior.
- If `e notin ∂M`, then `s = ∂M` lies inside `q̄` and is a piece.  So `gamma <= |omega(∂M)|_* < lambda gamma`,
  which is absurd.
- If `e in ∂M`, then `s = ∂M` minus `e` is a connected arc in `q̄` and a piece.  So
  `|omega(∂M)|_* <= |omega(s)|_* + 1 < lambda |omega(∂M)|_* + 1`.  This gives
  `gamma <= |omega(∂M)|_* < 1/(1 - lambda) < 2`.  But a single `a`-edge occurs on many a-lines and is a piece,
  so `Lambda >= 1` and `gamma > Lambda / lambda >= 8`.  This is a contradiction.

*Case: `D̃` has two faces `M_1`, `M_2`.*
- Each face is simply connected.  Two faces of a simply connected planar diagram share at most one maximal arc
  `t`: two disjoint common arcs would enclose a disc that must contain a third face.
- `t` is an inner arc of `D̃`, so it does not originate and is a piece: `|omega(t)|_* < lambda |omega(∂M_j)|_*`.
- At least one face, say `M`, does not contain `e`.  Its exterior boundary `s = ∂M` minus `t` is connected, lies
  inside `q̄`, and satisfies `|omega(s)|_* >= |omega(∂M)|_* - |omega(t)|_* > (1 - lambda) |omega(∂M)|_*`.
- It is also a piece, so `|omega(s)|_* < lambda |omega(∂M)|_*`.  This is a contradiction.

All cases are contradictory, so `g(v) b != g(u)`. ∎

*Remark.*  Theorem "gi" cannot simply be applied to `Gamma` with the deleted edge `v -> v b` put back.  Its proof
closes the path `p` into a cycle, which fails at a degree-one vertex.  And the conclusion itself can fail for a
long pendant path whose label is the long arc of a relator.  Lemma 1(b) uses that the pendant is a single letter.

---

## Lemma 2 (coefficients at free indices)

Let `beta = p + x a + y b + z ab` and `alpha = sum_{i,l} alpha_i(l) c_i a^l`, with `0 <= l <= C_i - 1`.  Let
`1 <= l <= C_i - 1` with `l notin D_i`.  Then

    (alpha beta)(g(v_il))   = p alpha_i(l) + x alpha_i(l-1),
    (alpha beta)(g(v_il) b) = y alpha_i(l) + z alpha_i(l-1).

*Proof.*  `A` embeds in `G` (the embedding proposition), so a pair `(h, k)` with `h in A`, `k in B` is determined
by `h` and the product.  Every such product is `g(v_jn)` or `g(v_jn) b` with `0 <= n <= C_j`.

*Products equal to `g(v_il)`.*
- `g(v_jn) = g(v_il)` forces `(j,n) = (i,l)` by Lemma 1(a).
- If `n in {0, C_j} ∪ O_j`, then `g(v_jn) b = g(target)`, whose position is distinguished.  Since `l` is not
  distinguished, Lemma 1(a) excludes `g(v_jn) b = g(v_il)`.
- If `v_jn` is hanging, Lemma 1(b) excludes it.
- The remaining pairs are `(v_il, 1)` and `(v_i(l-1), a)`, both present because `0 <= l-1 < l <= C_i - 1`.

*Products equal to `g(v_il) b`.*
- Since `l notin {0, C_i} ∪ O_i`, `v_il` is hanging.  So `g(v_jn) = g(v_il) b` is excluded by Lemma 1(b).
- `g(v_jn) b = g(v_il) b` forces `(j,n) = (i,l)` by Lemma 1(c).
- The remaining pairs are `(v_il, b)` and `(v_i(l-1), ab)`. ∎

---

## Proof of the theorem

Let `alpha != 0` with `supp alpha` inside `A`, let `beta != 0` with `supp beta` inside `B`, and suppose
`alpha beta = 0`.  Write `beta = p + x a + y b + z ab`.  By Theorem "tf", `G` is torsion-free.  Since `B` embeds,
`a != 1` and `b != 1` in `G`.

**Rank two: `pz != xy`.**
- By Lemma 2, at each `l in [1, C_i - 1]` with `l notin D_i`, the invertible matrix `[[p, x], [y, z]]` sends
  `(alpha_i(l), alpha_i(l-1))` to `0`.  So `alpha_i(l) = alpha_i(l-1) = 0`.
- List `D_i` as `0 = d_0 < d_1 < ... < d_r = C_i`.  Every index `m in [0, C_i - 1]` lies in exactly one block
  `[d_s, d_{s+1} - 1]`.
- If `d_{s+1} - d_s >= 2`, each `l` with `d_s < l < d_{s+1}` is non-distinguished and lies in `[1, C_i - 1]`.  The
  previous step kills `alpha_i(l)` and `alpha_i(l-1)`, and together these cover the whole block.
- So `alpha_i(m) != 0` only when `m = d_s` and `d_{s+1} = d_s + 1`, that is, when `m` and `m+1` are both
  distinguished.
- By hypothesis at most one such pair `(i,m)` exists over all lines.  So `alpha = mu h` for a scalar `mu != 0` and
  a group element `h`, and `alpha beta = mu h beta != 0`.  This is a contradiction.

**Rank one: `pz = xy`.**
- The rows `(p, x)` and `(y, z)` are proportional and not both zero.  So there are `(s,t) != 0` and `(u,v) != 0`
  with `p = us`, `x = vs`, `y = ut`, `z = vt`.
- Expanding, `(u + v a)(s + t b) = us + vs a + ut b + vt ab = beta`.
- Suppose `alpha beta = 0`.  By Lemma 0 of `rips-segev-witness-pairs-carry-no-zero-divisors-proof`, applied with
  `0 != s + tb in k[<b>]`, we get `alpha (u + v a) = 0`.  By Lemma 0 again with `0 != u + va in k[<a>]`, we get
  `alpha = 0`.  This is a contradiction.

Lemma 0 itself: `k[G]` is a free right `k[<a>]`-module on left coset representatives, and `k[<a>] ≅ k[t, t^{-1}]`
is a domain. ∎

---

## Coverage of the explicit families

For Steenbock's explicit families, `s_i = t_i = 2`, the Rips--Segev condition holds and `girth(Phi_Gamma) >= 41`.
- Steenbock's pieces lemma gives `Lambda <= 3`, and his cycle lemma gives `gamma >= 41`.
- His criterion `(Lambda + 2)/gamma <= 5/41 < 1/8` gives `Gr'_*(1/8)`.
- The Rips--Segev condition lists `I_{ij}`, `O_{ik}`, `C_i` and all pairwise differences of the distinguished
  positions of each line, over all lines, and requires them nonzero and pairwise distinct.  So at most one of these
  distances equals `1`.
- For the coefficient table `(10^{5i-4}, ..., 10^{5i})`, no distance is `1`, so rank two gives `alpha = 0`
  directly.

---

## Why the spacing hypothesis matters, and a sanity check

- *Where it is used.*  Without spacing, a run of consecutive distinguished positions leaves coefficients of `alpha`
  that the four equations of Lemma 2 do not see.  The calibration row of
  `experiments/rips-segev-coefficient-rigidity-2026-09-17/spaced_results.txt` shows this in the pattern model: 308
  rank-two rows have kernel vectors of support at least two when gluings are unrestricted.  With at most one
  adjacent pair, every rank-two kernel vector found is a monomial, as the theorem predicts.
- *What the pattern model covers.*  By Lemma 1 and the gluing description above, two products `hk` (`h in A`,
  `k in B`) coincide in `G` exactly when they are the same vertex of `Gamma` or the same hanging product.  That is
  the identification the pattern model uses.  So for small-cancellation gluings, the pattern kernel is exactly the
  kernel of `alpha -> alpha beta` on `k[A]`.
