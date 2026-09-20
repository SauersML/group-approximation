---
rg: 2
id: fpbs-invariant-spines-iff-tight-forest-repair-proof
kind: route
title: Send each connector endpoint up its forest ray, bound the density by mass transport through pasts of size at most M, and get one-ended repairs from the wired forest of a near-optimal connected graph or of the Cayley graph itself
target: fpbs-invariant-spines-iff-tight-forest-repair
requires:
  - fpbs-wired-forest-degree-two
---

Notation is as in the target. `G = Cay(Gamma,S)` is transitive and
unimodular, so the mass-transport principle (MTP) holds for every
diagonally invariant `f(u,v;omega) >= 0`:
`E sum_v f(o,v) = E sum_v f(v,o)`.

## Imports (literature, used as stated)

- **(AL6.1)** Aldous–Lyons, *Processes on unimodular random networks*
  (arXiv:math/0603062), Theorem 6.1: a unimodular measure on infinite graphs
  has `deg >= 2`.
- **(AL6.2)** Theorem 6.2: a unimodular measure on infinite graphs has
  `deg = 2` iff a.s. the graph is a tree with at most 2 ends.
- **(AL7.1)** Proposition 7.1: if `mu` is unimodular on infinite networks,
  then `deg(WUSF(mu)) = 2`.
- **(AL7.2)** Theorem 7.2: if `mu` is unimodular and concentrated on
  transient networks with bounded degree, then `WUSF(mu)`-a.s. each tree has
  exactly one end.
- **(AL8.9)** Theorem 8.9 (i)<=>(ii): `mu` is amenable iff some percolation on
  `mu` gives spanning trees with at most 2 ends a.s. For a fixed unimodular
  transitive graph this is the usual amenability (AL, remark before Theorem
  8.5, citing BLPS 1999 Theorems 5.1 and 5.3).
- **(W)** On a recurrent connected locally finite graph, Wilson's algorithm
  rooted at a vertex samples the uniform spanning tree, which equals the wired
  (and free) uniform spanning forest. In particular that forest is a single
  spanning tree (BLPS 2001, *Uniform spanning forests*, Section 5).
- **(HP)** Hutchcroft–Pete, arXiv:1810.11015, Remark after Proposition 2.1,
  verbatim: "some components of WUSF must intersect the infinite component of
  ω a.s., and it follows by indistinguishability of trees in WUSF [20] that
  every tree intersects the infinite component of ω a.s., so that the union of
  WUSF with ω is a.s. connected." Here `omega` is any invariant random
  subgraph with a unique infinite component, and WUSF is independent of it.
  [20] is Hutchcroft–Nachmias.

Rooted laws of `Gamma`-invariant random subgraphs of `G`, with any jointly
invariant decorations, are unimodular (MTP on the Cayley graph). The
fixed-graph facts `E deg_F(o) = 2` for one-ended spanning forests used below
are proved directly by MTP.

## Step 0. Facts about one-ended forests

Let `F` be a spanning forest of `G` whose trees are one-ended. For `v`, let
`ray(v) = (v = u_0, u_1, u_2, ...)` be the unique ray from `v` in the end
class of its tree, and let `parent(v) = u_1`.

- (0a) **`past(o)` is finite a.s.** `past(o)` is connected: if `v` is in it,
  the segment of `ray(v)` from `v` to `o` is in it. Also
  `parent(o) notin past(o)`, since otherwise `o in ray(parent(o))`, which is
  the tail of `ray(o)` after `o`, contradicting simplicity. If `past(o)` were
  infinite, König's lemma would give an infinite simple path from `o` inside
  `past(o)`. That path avoids `ray(o) \ {o}` and so defines a second end.
- (0b) **Monotone pasts along rays.** `{u_0, ..., u_i} ⊆ past(u_i)`, so
  `|past(u_i)| >= i + 1`. Hence at most `M` vertices of `ray(v)` have past of
  size `<= M`.
- (0c) **`E deg_F(o) = 2`.** Send mass 1 from each `v` to `parent(v)`. The
  outgoing mass is 1, so the expected number of children of `o` is 1, and
  `deg_F(o) = 1 + #children(o)`.
- (0d) **Rays in one tree merge.** Two rays toward the same end share a tail.

## Step 1. Item 1: `c_inv(S) = 1` iff `inf eta = 0`

**(<=)** Let `(F,C)` be a repair. Then `H = F ∪ C` is an invariant connected
spanning subgraph. By (0c),
`E deg_H(o) <= 2 + E deg_C(o) <= 2 + D P(o in V(C)) = 2 + D eta`, so
`c_inv(S) <= 1 + D eta / 2`. Also `c_inv(S) >= 1` by (AL6.1).

**(=>)** Fix `delta > 0` and an invariant connected spanning `H` with
`E deg_H(o) <= 2 + 2 delta`.

- **`H` is transient a.s.** The event `Rec = {H is recurrent}` is
  `Gamma`-invariant. Suppose `P(Rec) > 0`, and condition on it; the
  conditioned law is still invariant. Let `F = WUSF(H)`, sampled conditionally
  on `H`, which is an equivariant kernel, so `(H,F)` is jointly invariant.
  - By (W), `F` is a single spanning tree of `H`, hence of `G`.
  - By (AL7.1), `E deg_F(o) = 2`. By (AL6.2), applied to the unimodular rooted
    law of `(F,o)`, `F` has at most 2 ends.
  - So `F` is an invariant percolation on the fixed unimodular transitive graph
    `G` that gives spanning trees with at most 2 ends. By (AL8.9), `G` is
    amenable. That is a contradiction.
- **The repair.** Now let `F = WUSF(H)`, sampled as above.
  - By (AL7.2), since `H` has degree at most `D` and is transient, each tree of
    `F` has exactly one end.
  - By (AL7.1), `E deg_F(o) = 2`.
  - Put `C = H \ F`. Then `E deg_C(o) = E deg_H(o) - 2 <= 2 delta`, so
    `eta(F,C) <= P(deg_C(o) >= 1) <= 2 delta`.
  - `F ∪ C = H` is connected, so `(F,C)` is a repair.

## Step 2. Item 2, direction repair => spines

Let `(F,C)` be a repair, `M >= 1` and `a in (0,1]`.

- Let `A` be an iid Bernoulli(`a`) vertex set, independent of `(F,C)`, and
  put `B = V(C) ∪ A`. Then `(F,C,A)` is jointly invariant, `B` is nonempty
  a.s., and `P(o in B) <= eta + a`.
- Define `L` as the union of `C` and of `ray(v)` over all `v in B`, with
  vertex and edge sets. `L` is an equivariant measurable function of
  `(F,C,A)`, so its law is invariant. It is a subgraph of `G`, since
  `F, C ⊆ E(G)`, and it is infinite since the rays are infinite.

**Connected.** Every vertex of `L` lies on `ray(v)` for some `v in B`, and is
joined to `v` inside `L`. So it suffices to join `v, w in B`.

- Take a path from `v` to `w` in `F ∪ C`. Cut it at its `C`-edges. Each maximal
  `F`-segment lies in one tree, and its endpoints are `v`, `w`, or endpoints of
  `C`-edges, all of which are in `B`.
- Two points `p, q in B` of one tree are joined inside
  `ray(p) ∪ ray(q) ⊆ L`, by (0d).
- The `C`-edges are in `L`.

So `v` and `w` are joined in `L`.

**Density.** `o in V(L)` iff `o in ray(v)` for some `v in B`, that is, iff
`past(o) ∩ B` is nonempty. Endpoints of `C`-edges are in `B`, and
`v in ray(v)`. Let
`f(v,u) = 1{v in B, u in ray(v), |past(u)| <= M}`. This is diagonally
invariant.

- By (0b), `sum_u f(o,u) <= M 1{o in B}`.
- `sum_v f(v,o) = |past(o) ∩ B| 1{|past(o)| <= M}`.

By MTP,

```text
P(o in V(L)) <= P(|past(o)| > M) + E[ |past(o) ∩ B| ; |past(o)| <= M ]
             <= tau_F(M) + M (eta + a).
```

This is the quantitative statement in item 2. If the infimum in item 2 is 0,
then for every `eps` choose `(F,C,M)` with `tau_F(M) + M eta < eps/2` and
`a = eps/(2M)`. This gives spines with density `<= eps`.

## Step 3. Items 2 and 3, direction spines => fixed-forest repair

Let `W = WUSF(G)`. `G` is transient, since `Gamma` is nonamenable (Kesten), so
by (AL7.2), applied to the point mass at `(G,o)`, every tree of `W` has one
end, and `tau_W(M) -> 0` by (0a).

- Given a spine `L_eps` (invariant, connected, infinite, with
  `P(o in V(L_eps)) <= eps`), take `W` independent of `L_eps`. `L_eps` has a
  unique infinite component (itself), so (HP) gives that `W ∪ L_eps` is
  connected a.s.
- Put `C = E(L_eps)`. Every vertex of the connected infinite `L_eps` has an
  `L_eps`-edge, so `V(C) = V(L_eps)` and `eta(W,C) <= eps`.

This is item 3 (=>). Then `inf_M [tau_W(M) + M eps]` tends to 0 as
`eps -> 0`: choose `M` with `tau_W(M)` small, then `eps`. This gives item 2
(=>). Item 3 (<=) is Step 2 applied to `F = W`.

## Step 4. The Corollary

If `c_inv(S) = 1` and there are no spines, then item 2 fails. So every
sequence of repairs with `eta_n -> 0`, which exists by item 1, has
`liminf inf_M [tau_(F_n)(M) + M eta_n] > 0`. The repairs of Step 1 have
forest `WUSF(H_delta)`, whose law depends on `delta`. The passage in Step 2
needs one `M` that is good for all `delta`, and that is the missing input.

## What was not used

- No factor-of-iid structure. All couplings are merely invariant.
- Hutchcroft–Nachmias is used only through (HP), in Step 3.
- Steps 1 and 2 use only the imports AL6.1, 6.2, 7.1, 7.2, 8.9 and (W).
