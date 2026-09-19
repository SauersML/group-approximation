---
rg: 2
id: fpbs-sparse-spines-iff-sparse-one-ended-forest-connectors
kind: claim
title: Invariant sparse spines exist exactly when the trees of one fixed one-ended invariant forest can be joined by sparse connectors, so spines are cost-one graphs with uniformly tight descendant tails
distinct_from:
  fpbs-soft-collapse-iff-invariant-sparse-spines: that proves soft collapse iff sparse spines; this replaces spines by sparse inter-tree connectors for any fixed one-ended forest, and isolates the tightness of descendant tails as the only thing cost one lacks
  fpbs-sparse-spine-cost-bound: that turns an FIID spine into a cost bound; this is an equivalence at the level of invariant (not FIID) objects on the fixed Cayley graph
  fpbs-wired-forest-degree-two: that controls degree and ends of the wired forest of one fixed invariant graph; this needs no uniform spanning forest and quantifies over connectors, not over forests
  fpbs-quantitative-routing-tail-bound: that says cheap spanning graphs have long routes; this says what a cheap spanning graph needs in addition to become a sparse spine, namely a forest whose descendant tails do not depend on the price
---

**ESTABLISHED.** Proof in
`fpbs-sparse-spines-iff-sparse-one-ended-forest-connectors-proof`.

Let `G = Cay(Gamma,S)` for a finitely generated group `Gamma`. A *one-ended
forest* is a random spanning forest `F` of `G` with `Gamma`-invariant law
whose components are a.s. infinite, one-ended trees. In such a tree every
vertex `x` has a unique ray `gamma_x` to the end, and its *descendant set*
`desc(x) = {y : x in gamma_y}` is finite (König). *Invariant sparse spines*
are as in `fpbs-soft-collapse-iff-invariant-sparse-spines`.

**Connectors.** For a one-ended forest `F` and `beta > 0`, a
`beta`-connector is a random edge set `E'` such that `(F,E')` has
`Gamma`-invariant joint law, every edge of `E'` joins two distinct trees of
`F`, the quotient graph (trees of `F` as vertices, `E'` as edges) is a.s.
connected, and `P(o is an endpoint of an E'-edge) <= beta`.

**Theorem.**

* **(i)** If `G` has invariant sparse spines, then *every* one-ended forest
  `F` has a `beta`-connector for every `beta > 0`.
* **(ii)** Suppose that there is `phi` with `phi(n) -> 0` and, for every
  `beta > 0`, a one-ended forest `F_beta` with a `beta`-connector, such that
  `P(|desc_(F_beta)(o)| > n) <= phi(n)` for all `n`. Then `G` has invariant
  sparse spines. This applies in particular when `F_beta = F` is one fixed
  forest.

So if `G` has one one-ended forest (hypothesis (H)), then the following are
equivalent:

* sparse spines;
* sparse connectors for every one-ended forest;
* sparse connectors for some one-ended forest.

By Theorem A of `fpbs-soft-collapse-iff-invariant-sparse-spines`, these are
also equivalent to the existence of a soft collapse family.

**Degree lemma.** Every one-ended forest has `E deg_F(o) = 2`. So
`F_beta ∪ E'_beta` is an invariant connected spanning subgraph of
expected degree `<= 2 + |S| beta`. Condition (ii) therefore implies invariant
Cayley cost one at `S`, and it is invariant Cayley cost one *plus uniform
tightness of the descendant tails*.

**Where the kernel question now sits.** On the fixed-price-one kernel the
open question is whether sparse spines exist. By the theorem it is the
question whether cheap connected spanning graphs `H_eps` (expected degree
`2+2 eps`) can be taken to contain one-ended forests whose law of
`|desc(o)|` is tight as `eps -> 0`.
- Without tightness, `c_inv(S) = 1` alone gives a forest together with an
  `O(eps)` inter-tree edge set for each `eps`. This takes a spanning forest of
  `H_eps` of expected degree 2 and is not load-bearing here.
- So any counterexample to spines on a group with `c_inv(S)=1` must have
  descendant tails that escape to infinity as the price goes to one.
- Any proof of spines must produce a tight family.

**Hypothesis (H).** (H) is not imported here. The expected source is the
wired uniform spanning forest: on transient unimodular transitive graphs its
components are a.s. one-ended (Benjamini–Lyons–Peres–Schramm, *Uniform
spanning forests*, Ann. Probab. 29 (2001), and Morris 2003). This remark is
not load-bearing. Part (i) and part (ii) are unconditional.
