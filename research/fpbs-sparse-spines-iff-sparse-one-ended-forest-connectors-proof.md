---
rg: 2
id: fpbs-sparse-spines-iff-sparse-one-ended-forest-connectors-proof
kind: route
title: Hang the ray to the end from every connector endpoint and pay with the mass-transport principle, and conversely join every tree to an independent spine by harmonic-rate geodesics from its nearest points
target: fpbs-sparse-spines-iff-sparse-one-ended-forest-connectors
requires: []
---

The notation is that of the target. `G` is a Cayley graph, so it is
unimodular, and the mass-transport principle (MTP) holds. For every
nonnegative `f(x,y;omega)` that is invariant under the diagonal
`Gamma`-action, with `omega` any invariant random structure,
`E sum_y f(o,y) = E sum_x f(x,o)`. `V(L)` is the vertex set of `L`, and
`ends(E')` is the set of endpoints of edges of `E'`. All auxiliary
randomness consists of iid uniform labels on `V ⊔ E`, independent of
everything else. So every construction below is a jointly invariant factor
of invariant inputs.

## Lemma 0 (no finite invariant subsets of infinite pieces)

Let `P` be an invariant random partition of `V` into infinite classes, and
let `M` be an invariant random vertex set. Then a.s. no class `C` of `P` has
`0 < |M ∩ C| < infinity`.

*Proof.* On `{0<|M∩C|<infinity}`, let each `x in C` send mass
`1/|M∩C|` to each point of `M∩C`. Each vertex sends total mass `<= 1`. A
vertex of `M∩C` in such a class receives `|C| · 1/|M∩C| = infinity`. By the
MTP this happens with probability `0` at `o`, and by invariance and
countability it happens at no vertex. ∎

## Lemma 1 (structure of one-ended trees)

Let `T` be a one-ended locally finite tree. For each vertex `x` let `gamma_x`
be the unique ray from `x` representing the end, and let `p(x)` be its
second vertex, the *parent*.

* (a) For all `x, y in T`, the rays `gamma_x` and `gamma_y` share a tail. So
  `⋃_(b in B) gamma_b` is connected for every nonempty `B ⊆ V(T)`.
* (b) `desc(x) = {y : x in gamma_y}` is finite, and `desc(x) ⊊ desc(p(x))`.
  So along `gamma_x` the sizes `|desc|` strictly increase, and at most `n`
  vertices of `gamma_x` have `|desc| <= n`.
* (c) For a one-ended forest, `E deg_F(o) = 2`.

*Proof.*
- (a) Two rays in a one-ended tree represent the same end, so they share a
  tail. Each `gamma_b` is connected and meets every other one.
- (b) `desc(x)` is the vertex set of the component of `x` in
  `T - {x p(x)}`. If it were infinite, König's lemma would give a ray from
  `x` inside it, which is disjoint from the tail of `gamma_x` beyond `x`,
  giving a second end. The strict inclusion holds because `p(x)` lies in
  `desc(p(x))` and not in `desc(x)`.
- (c) Every vertex sends mass `1` to its parent. By the MTP,
  `E #children(o) = 1`. Also `deg_F(o) = #children(o) + 1`. ∎

## Part (ii): tight forests and sparse connectors give spines

Fix `eps > 0`. Choose `n` with `phi(n) <= eps/2`, then
`beta = delta = eps/(4n)`. Let `F = F_beta`, let `E' = E'_beta`, and let
`A_delta` be an independent iid Bernoulli(`delta`) vertex set. Put
`B = ends(E') ∪ A_delta` and

```text
L = E' ∪ ⋃_(b in B) gamma_b.
```

*Infinite and connected.* Every tree `T` of `F` is infinite, so `A_delta`
meets it a.s. (conditionally on `F`, infinitely many independent trials of
probability `delta`). By Lemma 1(a), `L_T = ⋃_(b in B∩T) gamma_b` is a
connected infinite subtree of `T`. It contains every endpoint in `T` of an
`E'`-edge, because `b in gamma_b`. Let `T, T'` be two trees. The quotient
graph is connected, so there are trees `T = T_0, ..., T_k = T'` and edges
`e_i in E'` joining `T_(i-1)` to `T_i`. The union
`L_(T_0) ∪ e_1 ∪ L_(T_1) ∪ ... ∪ L_(T_k)` is connected. So `L` is connected,
and it is infinite.

*Density.* Every vertex of `L` lies on some `gamma_b`. Also
`o in gamma_b` iff `b in desc(o)`. So

```text
P(o in V(L)) = P(desc(o) ∩ B ≠ ∅)
  <= P(|desc(o)| > n) + E[ |desc(o) ∩ B| ; |desc(o)| <= n ].
```

Transport `f(x,y) = 1{x in B, y in gamma_x, |desc(y)| <= n}`. The mass
received at `o` is `|desc(o) ∩ B| · 1{|desc(o)| <= n}`. The mass sent from
`o` is at most `n · 1{o in B}`, by Lemma 1(b). Also
`P(o in B) <= beta + delta`. So

```text
P(o in V(L)) <= phi(n) + n(beta + delta) <= eps/2 + eps/2 = eps.
```

The law of `L` is invariant, because `L` is an equivariant function of
`(F, E', A_delta)`. So `L` is an invariant sparse spine of density `<= eps`.
∎

## Part (i): spines give connectors for every one-ended forest

Let `F` be a one-ended forest and `beta in (0,1]`. Take a spine `L` with
`P(o in V(L)) <= beta`, sampled independently of `F`. The pair `(F,L)` then
has invariant joint law. For a tree `T` of `F`, let
`r_T = min_(x in T) d(x, V(L))`, which is finite because `L` is nonempty, and
let `M_T = {x in T : d(x,V(L)) = r_T}`. This is nonempty. By Lemma 0, applied
to the partition into trees and to `M = ⋃_T M_T`, every `M_T` is infinite
a.s.

*Selection.* Independently for each `x in M`, select `x` with probability
`beta/(1 + d(x,V(L)))`. Let `A` be the selected set. For `x in A`, let `pi_x`
be the geodesic from `x` to `V(L)` that is lexicographically minimal for the
iid vertex labels. It has `d(x,V(L)) + 1` vertices.

*Every tree is reached.* Conditionally on `(F,L)`, the points of `M_T` are
selected independently, each with the same probability `beta/(1+r_T) > 0`,
and `M_T` is infinite. So `A ∩ T ≠ ∅` a.s. for every `T`.

*Cost of the paths.* Transport `f(x,y) = 1{x in A, y in pi_x}`. The mass
received at `o` bounds `1{o in ⋃_x pi_x}`. The expected mass sent from `o` is

```text
E[ 1{o in A} (d(o,V(L)) + 1) ] = E[ 1{o in M} beta ] <= beta.
```

So `P(o in ⋃_(x in A) pi_x) <= beta`.

*Connector.* Let `L' = L ∪ ⋃_(x in A) pi_x`. It is connected, because each
`pi_x` ends in the connected graph `L`, and it meets every tree of `F`. Let
`E'` be the set of edges of `L'` whose endpoints lie in distinct trees of
`F`. Given trees `T` and `T'`, pick `x in A∩T` and `x' in A∩T'`, and a path
from `x` to `x'` in `L'`. Consecutive vertices of the path lie in the same
tree or are joined by an edge of `E'`, so the path projects to a path from
`T` to `T'` in the quotient graph. So the quotient is connected. Finally
`ends(E') ⊆ V(L')`, so

```text
P(o in ends(E')) <= P(o in V(L)) + P(o in ⋃ pi_x) <= 2 beta.
```

`(F,E')` is an equivariant function of `(F, L, labels)`, so its joint law is
invariant. Replacing `beta` by `beta/2` gives a `beta`-connector. ∎

## The equivalence and the degree remark

Under (H), the implications are:
- spines ⇒ connectors for every `F`, by (i);
- connectors for every `F` ⇒ connectors for the forest given by (H);
- connectors for one fixed `F` ⇒ spines, by (ii), with
  `phi(n) = P(|desc_F(o)| > n)`, which tends to `0` because `desc_F(o)` is
  finite a.s.

For the degree remark, note that `E'` has at most `|S|` edges at each of its
endpoints. So `E deg_(F ∪ E')(o) <= 2 + |S| beta` by Lemma 1(c), and
`F ∪ E'` is connected and spanning. ∎
