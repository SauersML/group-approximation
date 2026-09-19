---
rg: 2
id: rips-segev-ab-layered-elements-have-no-left-annihilator
kind: claim
title: In Steenbock's Rips--Segev group no nonzero element supported in <a><b> has a left annihilator, for any number of b-layers and over every field, and every u + v b^{±1} w with u, v, w in k[a^{±1}], v w != 0, is a two-sided non-zero-divisor; a coset-wise gcd flip turns right annihilators of degree one into left ones, and b-line clusters give the port graph for every b-degree
distinct_from:
  rips-segev-two-layer-elements-have-no-left-annihilator: that treats only u + w b^{±1} (b-degree one, left annihilators).  This covers every b-degree, and by the flip also right annihilators and the elements u + v b w.
  rips-segev-sparse-a-support-elements-are-regular: that needs S - S to miss Dist(Gamma); this has no condition on the a-supports.
  rips-segev-steenbock-eleven-point-a-supports-are-regular: that needs at most q(gamma) distinct a-exponents; this has no bound on them.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question.  This settles the one-sided case "beta supported in <a><b>" and the two-sided case of b-degree one; right annihilators of b-degree >= 2 and general supports stay open.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-ab-layered-no-left-annihilator-proof`.

**Setting.**  As in `rips-segev-two-layer-elements-have-no-left-annihilator`.
- `G` is the Rips--Segev group built from Steenbock's graph `Gamma`, with core `K = F/<<R>>`, `F = <a> * <b>`,
  `Gr'_*(1/8)` and `girth(Phi) >= 42`.
- `k` is any field.  Elements of `k[t^{±1}]` are evaluated at `a`.

**Theorem A (no left annihilators on `<a><b>`).**  Let `d >= 0` and `u_0, ..., u_d in k[t^{±1}]`, not all zero,
and put `beta = sum_j u_j(a) b^j`.  If `alpha in k[G]` and `alpha beta = 0`, then `alpha = 0`.
- Equivalently: every nonzero `beta in k[G]` with `supp beta ⊆ <a><b>` has no left annihilator.  Right
  multiplication by `b^m` reduces any finite `b`-range to `0..d`.
- By the involution `g -> g^{-1}`: every nonzero element supported in `<b><a>` has no right annihilator.
- The case `d = 1` is Theorem 2 of `rips-segev-two-layer-elements-have-no-left-annihilator`.

**Theorem B (flip; any group).**  Let `H` be a group and `a, b in H` with `a` of infinite order.  Let
`u, v, w in k[<a>]` with `v != 0`, `w != 0`, and `eps = ±1`.
- Write `u = g u_0`, `w = g w_0` with `g = gcd(u, w)`.
- If `alpha (u + v b^eps w) = 0`, then `alpha = eta w_0` and `eta (u_0 + w_0 v b^eps) = 0` for some `eta`, with
  `eta != 0` when `alpha != 0`.
- So left annihilators of `u + v b^eps w` come from left annihilators of the two-layer element
  `u_0 + (w_0 v) b^eps`.

**Corollary C (two-sided, degree one).**  In `k[G]`, every `u + v b^{±1} w` with `u, v, w in k[a^{±1}]` and
`v w != 0` is a non-zero-divisor on both sides.
- In particular `u + w b` and `u + b w` are regular for all `u` and all `w != 0`.
- This settles the right-annihilator step `(u + w b) alpha = 0` left open by the two-layer node.

**Mechanism of Theorem A.**
- *Clusters.*  Put `X_j = alpha u_j`.  Along each `b`-line `y <b>` the equation reads
  `sum_j X_j(v b^{-j}) = 0`.  So the active points of a `b`-line fall into clusters with gaps `<= d`, and each
  cluster has at least two points.
- *Port graph.*  `S` has an edge for every `b`-edge inside the span of a cluster.  An active coset has an in-edge
  where `X_0 != 0` and a distinct out-edge where `X_d != 0`.  An inactive point inside a span carries two edges.
  So `S` has minimum degree 2, and the leaf-block flow cycle of the two-layer node applies unchanged.
- *Pure active lines.*  A good untouched active line has all its ports at distinguished positions of its row.  A
  multi-layer rank-one lemma, `P^i_T P^j_T' = P^i_T' P^j_T`, allows at most one such line per copy.
- *Isolated inactive lines.*  A good untouched line in an inactive coset carries only pass-through points.
  These sit at the middle positions `0, C` of its line.  In Steenbock's gluing the neighbours of a middle
  position along its `b`-run are never middles (`b`-runs have at most 2 edges).  So two such lines are never
  consecutive along a walk of cycle lines.
- *Hopping with windows of 6.*  Among 6 consecutive untouched cycle lines of one copy, at most 2 are not
  inactive (one pure line, one bridge end), and the inactive ones are pairwise non-consecutive.  That is
  impossible.  So visits have 3 to 8 edges.  A Greendlinger arc of 13 consecutive `b`-edges still contains
  3 consecutive edges of each of two consecutive visits, and two distinct copies share at most 3 cosets.

**Mechanism of Theorem B.**
- Right multiplication by `k[<a>]` preserves the decomposition of `k[H]` along left `<a>`-cosets.  So
  `alpha u_0 = -(alpha v b^eps) w_0` holds coset by coset in `k[t^{±1}]`.
- Since `gcd(u_0, w_0) = 1`, this gives `alpha = eta w_0` and `alpha v b^eps = -eta u_0` with one `eta`.
  Substituting, `eta (u_0 + w_0 v b^eps) = 0`.

**Calibration.**
- In `H_{m,n} = <a, b | (a^m b)^n>` (`n >= 3`), `alpha = sum_j (a^m b)^j` kills `1 - a^m b` on both sides.
  Theorem B is consistent with this: the flip sends the right annihilator to `eta = -alpha^* a^m`, and `eta`
  kills `1 - a^{-m} b^{-1}` on the left.
- Theorem A fails in `H_{m,n}` only at the rank-one step: all lines of its relator loop carry the port set
  `{0, m}`, and there are no distinct rows.

**Open.**
- Right annihilators of `b`-degree `>= 2`: `alpha (sum_j b^j v_j) = 0`.  The port graph (segments `y .. y b^d`
  for `y in supp alpha`), the flow cycle and the purity step all transfer.  What fails is the rank-one step:
  the port vector of a coset lies in the syzygy module of `(v_0, ..., v_d)`, which has rank `d >= 2`.
- General supports, beyond `<a><b>` and `<b><a>`.
