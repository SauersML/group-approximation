---
rg: 2
id: rational-germ-singular-sets-graph-path-space-proof
kind: route
title: Proof that singular sets of rational homeomorphisms are path spaces of finite graphs, with the finite-or-Cantor dichotomy
target: rational-germ-singular-sets-are-finite-graph-path-spaces
requires:
  - germ-complex-and-bux-gonzalez-morse-inputs
artifacts:
  - research/artifacts/gq-bh-bh-free-21-automatic-germ-extensions.md
---

Notation as in the claim. Write `u_n = ξ_1 … ξ_n`.

## 0. Two facts from perfectness

**(P1)** For every prefix `u`, the set `h([u])` is infinite, so its longest common prefix is a
finite word. Indeed `[u]` is infinite because `∂L` is compact with no isolated points.

**(P2)** For every `ξ ∈ ∂L` there are infinitely many `n` such that `Fol(u_n)` contains two
points with distinct first letters. Otherwise, for all large `n` every point of `[u_n]` has the
same next letter, so by induction `[u_N] = {ξ}` for some `N`, making `ξ` isolated.

## 1. Pointwise criterion

**(⇐)** Suppose the triple at `u = u_n` is regular, say `h_u(η) = eη` for all `η ∈ Fol(u)` with
`Fol(u) = Fol(out(u)e)`. Then `h(uη) = out(u)·e·η` for every `η ∈ Fol(u)`, so `h` agrees on the
neighbourhood `[u]` of `ξ` with the prefix replacement `u ↦ out(u)e`, which lies in `B`.

**(⇒)** Suppose `h` agrees with `b ∈ B` on a neighbourhood of `ξ`. Shrinking, there are
prefixes `α < ξ` and `β < h(ξ)` with `Fol(α) = Fol(β)` and `h(αζ) = βζ` for all
`ζ ∈ Fol(α)`. Fix `n ≥ |α|` and put `z = ξ_{|α|+1} … ξ_n`, so `u_n = αz`. For every
`η ∈ Fol(u_n)` we have `zη ∈ Fol(α)` and hence

    h(u_n η) = β z η.                                                        (1)

Also `h(u_n η) = out(u_n)·h_{u_n}(η)`. Both `out(u_n)` and `βz` are prefixes of `h(ξ)`, so one
is a prefix of the other. Choose `n` as in (P2), so that the longest common prefix of
`Fol(u_n)` is empty. If `out(u_n)` strictly contained `βz`, say `out(u_n) = βz·f` with `f`
nonempty, then (1) would give `η = f·h_{u_n}(η)` for all `η ∈ Fol(u_n)`, so every element of
`Fol(u_n)` would begin with `f`, contradicting the choice of `n`. Hence `out(u_n)` is a prefix
of `βz`; write `βz = out(u_n)·e`. Then (1) gives `h_{u_n}(η) = eη` for all `η ∈ Fol(u_n)`, and
`Fol(out(u_n)e) = Fol(βz) = Fol(αz) = Fol(u_n)`, using `Fol(α) = Fol(β)`. So the triple at
`u_n` is regular, for every `n` as in (P2). ∎

## 2. Graph description

By item 1, `ξ ∈ sing_B(h)` if and only if the triple at `u_n` is non-regular for every `n`. The
triple `(h_{u_n}, Fol(u_n), Fol(out(u_n)))` together with the next letter `x` determines the
next triple: the section transforms as `h_{u_n x} = (h_{u_n})·x` in the transducer, `Fol(u_n x)`
is determined by `Fol(u_n)` and `x` in the `∂L` automaton, and `Fol(out(u_n x))` is determined
by `Fol(out(u_n))` and the emitted word `λ(h_{u_n}, x)`. So the triples along points of
`sing_B(h)` are exactly the infinite paths of `Λ_h` from the start vertex. Conversely an
infinite path of `Λ_h` reads a word all of whose prefixes are prefixes of points of `∂L`, hence
a point of `∂L`, since the `∂L` automaton has all states accepting. The section set and the set
of follower sets are both finite, so `Λ_h` is finite and `sing_B(h)` is the path space of a
finite graph, hence closed and rational. ∎

## 3. The dichotomy for path spaces of finite graphs

Let `Λ` be a finite directed graph with a start vertex and let `P` be its set of infinite paths
from the start. Prune by repeatedly deleting vertices with no outgoing edge; this does not
change `P`, and in the pruned graph `Λ'` every vertex lies on an infinite forward path. Call a
vertex of `Λ'` *recurrent* if it lies on a cycle of `Λ'`.

**(a) If every recurrent vertex has out-degree one in `Λ'`, then `P` is finite and each of its
elements is eventually periodic.** Let `v` be recurrent with unique successor `w`. Some cycle
through `v` starts with the edge `v → w`, so `w` is recurrent. Hence the forward orbit of a
recurrent vertex is determined, consists of recurrent vertices, and is the cycle through `v`
traversed forever. Now let `π ∈ P`. The set of vertices `π` visits infinitely often is strongly
connected, hence recurrent, so `π` reaches a recurrent vertex and is deterministic from then on.
The non-recurrent part of `Λ'` has no cycle, so it is a finite acyclic graph with finitely many
paths from the start. Therefore `P` is finite and each element is a finite path followed by one
cycle. ∎

**(b) If some recurrent vertex `v` of `Λ'` has out-degree at least two, then `P` is infinite.**
Let `c` be a cycle at `v` and `w_1 ≠ w_2` two successors of `v`, each with an infinite forward
path `π_i` in `Λ'`. The paths `c^k·(v → w_1)·π_1`, `k ≥ 0`, are pairwise distinct. ∎

**(c) If a recurrent vertex `v` has two distinct return paths to itself, then `P` contains a
Cantor set.** Let `c_1 ≠ c_2` be paths from `v` to `v`. Replacing them by `c_1^{|c_2|}` and
`c_2^{|c_1|}` we may assume `|c_1| = |c_2|` and `c_1 ≠ c_2`. Fix a path `α` from the start to
`v`. The map `{1,2}^ℕ → P`, `(ε_i) ↦ α c_{ε_1} c_{ε_2} …`, is injective, because the blocks have
equal length and `c_1 ≠ c_2`, and continuous, hence a homeomorphism onto its image. ∎

Items (a) and (b) give item 3 of the claim; (c) gives item 4, since a strongly connected
component that is not a single cycle has a vertex with two distinct return paths.

## 4. Decidability

Pruning, computing strongly connected components and out-degrees, and listing the finitely many
eventually periodic paths are standard finite graph computations on `Λ_h`, which is built from a
transducer for `h` and an automaton for `∂L`. Regularity of a triple is decidable: `h_u` is
prefix-prepending with witness `e` iff the minimal transducer of `h_u` is the corresponding
one-way word-prepending machine, and the follower-set equality is a finite automaton
comparison. ∎

## 5. Trust surface

- BBCMP Cor 1.8 and Thm 1.7 are read at source and used only to say the hypothesis applies to
  continuous asynchronous automatic groups.
- The definitions of `sing_B` and of a finite germ extension are BHM §1, quoted in
  `germ-complex-and-bux-gonzalez-morse-inputs`.
- Everything else is elementary and self-contained. In particular the two perfectness facts in
  step 0 are used exactly where a forced continuation would otherwise break the argument.
