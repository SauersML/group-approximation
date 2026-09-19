---
rg: 2
id: fpbs-profinite-relcost-equals-relative-rank-gradient-proof
kind: route
title: Fold chords into the coset graph of K over Q, lift paths for sufficiency, use freeness for necessity, approximate cheap graphings by clopen ones, and transfer along weak containment
target: fpbs-profinite-relcost-equals-relative-rank-gradient
requires:
  - abert-weiss-free-actions-weakly-contain-bernoulli
  - fpbs-mal-floor-iff-deep-promotion-floor
artifacts:
  - research/artifacts/fpbs-relative-rank-collapse-2026-09-18.md
---

Notation is as in the target. `L` acts on the right. `Q` is a finite
transitive `L`-set with `n = |Q|`. An action `X` *has factor* `Q` if there is
an equivariant `π : X → Q`. Then `π_*μ` is uniform, because `Q` is
transitive. A graphing *piece* `(g, A)` is the partial map `x ↦ x·g` on `A`,
and it costs `μ(A)`. Every graphing inside `E_L` splits into countably many
pieces with the same total cost. A chord `(p, w)` is the piece
`(w, π^{-1}(p))`, and it costs `1/n`.

## 1. Folding criterion (part (1))

Let `G` be the labelled graph over `Q` defined in the target. Each edge maps
to an `L`-step of `Q`, and `φ : V(G) → Q` is the vertex map. Let `F` be the
Stallings fold of `G`. Folding identifies two edges with the same label and
the same origin. Their endpoints have the same `φ`, so `φ` descends to `F`.
Two standard facts about folding:
- **(F1)** If `v, v'` are vertices of `G`, then every path in `F` from `[v]`
  to `[v']` lifts to a path in `G` from `v` to `v'` whose label is freely
  equal. To see this, induct on folds. When `e_1 : u → v_1` and `e_2 : u → v_2`
  are folded, insert `e_1^{-1} e_2` each time the path passes from `v_1` to
  `v_2`.
- **(F2)** In the folded graph `F`, every path is homotopic rel endpoints to
  the reduced path that carries the free reduction of its label.

**Real-to-real paths act on X.** Suppose `x ∈ π^{-1}(p)`, and let `γ` be a path
in `G` from the real vertex `p` to a real vertex with label `u`.
- Split `γ` at its visits to real vertices. Interior vertices of `c`-paths and
  chord paths have degree 2.
- So each segment is one of three kinds. It is an `a`-edge, a whole `c`-path,
  or a whole chord path, traversed in either direction. Otherwise it goes in
  and back out, and then its label is freely trivial.
- Apply the segments in turn. The current point `y` satisfies
  `π(y) = φ(current real vertex)`, so a chord step is applied inside its
  domain.
- Hence `x·u ∈ [x]_{E_K ∨ Φ}`, where `Φ` is the set of chords.

**Sufficiency.** Suppose `F` has `n` vertices.
- The real vertices have distinct `φ`, so they are all the vertices of `F`.
- The edge `p -b-> x_1` of the `c`-path at `p` gives an edge `p -b-> p·b` in
  `F`.
- By (F1), there is a path in `G` from `p` to `p·b` whose label is freely
  equal to `b`.
- Since `x·a` is in `E_K`, the chords and `E_K` generate `E_L` on every action
  with factor `Q`. Freeness is not used.

**Necessity.** Suppose the chords and `E_K` generate `E_L` on one essentially
free action `X` with factor `Q`.
- Every `p` has positive mass. So there is an `x` over `p` and a finite
  `E_K ∨ Φ` path from `x` to `x·b`.
- Each step is `a^{±1}`, `c^{±1}` or a chord step, applied at a point over its
  base. So the steps trace a path in `G` from `p` to a real vertex.
- Let `g` be the product of the step elements. Then `x·g = x·b`, so `g = b` by
  freeness.
- By (F2), `F` has an edge `p -b-> p·b`, and it has the `a`-edges as well. So
  every real vertex of `F` carries all four labels, pointing to real vertices.
- Suppose some non-real vertex exists. Every vertex of `G` lies on a path that
  starts at a real vertex, so some non-real vertex `v` is adjacent in `F` to a
  real vertex `p` by a label `l`. But `p` already has its `l`-edge to `p·l`,
  and `F` is folded, so `v = p·l` is real. This contradiction shows `F` has `n`
  vertices.

So one free action suffices, and `d(Q)` is well defined and finite. The
original `b` placed at every point is `n` chords, so `d(Q) ≤ n`.

## 2. Relative rank (part (2))

Assume `K` is transitive on `Q`, and fix a base point `q_0`.

**The graph without chords.** Let `G_K` be the part of `G` with no chords.
- `G_K` is connected, because `K` is transitive.
- The letters `a` and `c` act on `Q` as permutations. So each real vertex has
  exactly one outgoing `a`-edge and one outgoing `c`-path, and exactly one of
  each incoming.
- Hence real-to-real loops at `q_0` read exactly `Stab_K(q_0)`.

**Adding chords.** Adding the path of a chord `(p, w)` to a connected graph
adds one free generator to `π_1`. That generator is `t = k w k'`, where
`k, k' ∈ K` satisfy `q_0·k = p` and `p·w·k' = q_0`. So the image of `π_1` is

```text
H = < Stab_K(q_0), t_1, …, t_d > ≤ Stab_L(q_0).
```

Folding does not change this image.

**Criterion.**
- If `F` has `n` vertices, then `F` is the Schreier graph of `Q`, so
  `H = Stab_L(q_0)`.
- Conversely, suppose `H = Stab_L(q_0)`. The core of the connected folded
  graph `F` is the Stallings graph of `H`. Since `H` has finite index, that
  core is the Schreier graph of `Q`, where every vertex carries all four
  labels. A hanging tree would have to attach at such a vertex, and `F` is
  folded, so no hanging tree exists. Hence `F` has `n` vertices.

Every `h ∈ Stab_L(q_0)` is the generator `t` of the chord `(q_0, h)`. So `d(Q)`
is the least number of elements that must be added to `Stab_K(q_0)` to
generate `Stab_L(q_0)`, that is, the relative rank.

**Ranks.** By Schreier's formula, both stabilizers have rank `n + 1`. The group
`Stab_L(q_0)` has index `n` in `L`, and `Stab_K(q_0)` has index `n` in `K`,
both of rank 2.

**Malnormality.** The group `Stab_K(q_0) = K ∩ Stab_L(q_0)` is malnormal in
`Stab_L(q_0)`, because `K` is malnormal in `L`. For
`h ∈ Stab_L(q_0) \ K`,

```text
h (K ∩ Stab_L) h^{-1} ∩ (K ∩ Stab_L) ⊆ hKh^{-1} ∩ K = 1.
```

## 3. Profinite identity (part (3))

Let `X = lim Q_m`, where the `Q_m` are finite transitive `L`-sets and the
maps `Q_{m+1} → Q_m` are equivariant. The level-`m` cylinders
`π_m^{-1}(p)` form an `L`-invariant partition, and clopen sets are finite
unions of cylinders.

**Upper bound, for every X with factor Q.** Pull back an optimal set of chords
through `π`. By §1 sufficiency, they generate `E_L` together with `E_K`, at
cost `d(Q)/n`. So `relC(X) ≤ d(Q)/|Q|`.

**Monotonicity.** Each level-`m` chord `(p, w)` is the union of the chords
`(p', w)` over `p'` in the fibre above `p`. These chords work on every action
with factor `Q_{m+1}`, since such an action also has factor `Q_m`. So

```text
d(Q_{m+1})/|Q_{m+1}| ≤ d(Q_m)/|Q_m|,
```

and the limit exists and equals the infimum.

**Patterns.** Let `Φ = {(g_i, A_i)}` be a set of pieces with
`E_K ∨ Φ = E_L`. A *pattern* is a finite sequence of steps.
- Each step is `a^{±1}`, `c^{±1}`, a piece `(g_i, A_i)` taken forward, or a
  piece taken backward.
- The product of the steps must equal `b`.
- The *pattern set* is the set of `x` at which every step is defined along
  the way. A piece taken forward needs the current point in `A_i`, and a piece
  taken backward needs it in `A_i·g_i`.
- So a pattern set is a finite intersection of translates of the sets `A_i`
  and `A_i·g_i`.
- Every `x` in a pattern set has `x·b ∈ [x]_{E_K ∨ Φ}`.

**Lower bound, for essentially free profinite X.** Take `ε > 0`, and choose
`Φ` with `E_K ∨ Φ = E_L` and `C(Φ) < relC(X) + ε`.
- Almost every `x` lies in some pattern set. By countable additivity, a finite
  index set `I` and a finite list `P` of patterns over `I`, each of length at
  most `R`, cover a set `G_0` with `μ(G_0) ≥ 1 − ε`.
- Choose a level `m` and clopen sets `A_i'` of level `m`, for `i ∈ I`, with
  `μ(A_i Δ A_i') < δ`. Translation preserves the measure, and
  `A_i g_i Δ A_i' g_i = (A_i Δ A_i') g_i`.
- Let `G_0'` be defined from the `A_i'` by the same patterns. Then
  `μ(G_0 Δ G_0') ≤ |P| R δ`. The partition into level-`m` cylinders is
  `L`-invariant, so `G_0'` is a union of level-`m` cylinders.
- Put `B = X \ G_0'`, and let
  `Φ' = {(g_i, A_i')}_{i ∈ I} ∪ {(b, B)}`.
- Then `E_K ∨ Φ'` contains `(x, x·b)` for every `x`, so it equals `E_L`.
- `Φ'` is a finite set of level-`m` chords, with
  `N = |Q_m| · C(Φ')` of them.
- By §1 necessity, applied to the free action `X`, `N ≥ d(Q_m)`.
- Take `δ` with `|I| δ + |P| R δ < ε`. Then

```text
d(Q_m)/|Q_m| ≤ C(Φ') ≤ C(Φ) + |I|δ + μ(B) < relC(X) + 3ε .
```

With monotonicity, `inf_m d(Q_m)/|Q_m| ≤ relC(X)`. Hence equality holds.

## 4. Transfer along weak containment

**Lemma.** Let `Y` and `X` be p.m.p. actions of `L`, and suppose `Y ≺ X`. Then
`relC(X) ≤ relC(Y)`.

This is Kechris's argument for cost (see `cost-weak-containment-monotonicity-citation`)
run with `E_K` kept for free. The proof follows.

**Transfer the pattern sets.** Take `Φ`, `I`, `P` and `G_0` for `Y` as in §3,
with `μ(G_0) ≥ 1 − ε`.
- Let `T ⊂ L` be a finite set that contains `e` and every `h` such that some
  translate `A_i·h` occurs in a pattern set of `P`.
- Let `𝒫` be the partition of `Y` into atoms of the algebra generated by the
  sets `A_i·t`, for `i ∈ I` and `t ∈ T`. Label each atom `α` by
  `α(i, t) ∈ {0, 1}`.
- By the partition form of weak containment, there is a partition `𝒫'` of `X`
  indexed by the same atoms. It satisfies
  `|μ(P'_α ∩ P'_β·h) − μ(P_α ∩ P_β·h)| < η` for all `h ∈ T T^{-1}`.
- Put `A_i' = ∪ { P'_α : α(i, e) = 1 }`.
- In `Y`, the atom `P_α` meets `P_β·t` in measure zero whenever
  `α(i, t) ≠ β(i, e)`. So in `X`,
  `μ( A_i'·t Δ ∪{ P'_α : α(i,t) = 1 } ) ≤ |𝒫|^2 η`.

**Conclude.**
- Every pattern set, computed in `X` from the `A_i'`, lies within
  `R |𝒫|^2 η` of the union of the atoms `P'_α` whose labels satisfy the
  pattern.
- That union has measure within `|𝒫| η` of the corresponding measure in `Y`.
- So `G_0'` has measure at least `1 − ε − O(η)`, and
  `Σ μ(A_i') ≤ C(Φ) + O(η)`.
- Adding `(b, X \ G_0')` gives a graphing admissible for `relC(X)` of cost at
  most `relC(Y) + 2ε + O(η)`.

## 5. Consequence (part (4))

Let `ρ` be the Bernoulli shift of `L`, and let `X` be an essentially free
profinite action with tower `(Q_m)`.
1. `ρ ≺ X` by `abert-weiss-free-actions-weakly-contain-bernoulli`.
2. §4 then gives `relC(X) ≤ relC(ρ)`.
3. `relC(ρ) = Q_0` by the definition in `fpbs-mal-floor-iff-deep-promotion-floor`,
   since `S_0 = E_ρ` and `S_1 = E_{ρ|K}`.

With §3,

```text
Q_0 ≥ lim_m d(Q_m)/|Q_m| .
```

**Reading the bound.**
- If this limit is positive for one free tower, then `Q_0 > 0`.
- `Q_0 > 0` contradicts `relC(ρ) = 0`, which `fpbs-relative-fixed-price-free-pairs`
  asserts.
- Contrapositively, that claim forces `d(Q_m) = o(|Q_m|)` along every
  essentially free tower.
- Nothing here bounds `d(Q_m)` from below, so neither side is decided.
