---
rg: 2
id: aperiodic-tree-almost-automorphism-fg-subgroups-are-rf
kind: claim
title: On a rooted tree whose branching is not eventually periodic, every finitely generated group of almost automorphisms is residually finite, so none contains (Q,+)
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that asks for a finitely presented simple host of GL_n(Q); this excludes, as finitely generated intermediate hosts, all almost-automorphism groups of trees with aperiodic branching, in particular of every spherically homogeneous tree whose branching involves infinitely many primes.
  piecewise-commutative-linear-hosts-miss-linear-gl-n-q: that excludes finitely generated hosts whose pieces lie in a group linear over a commutative ring; this excludes finitely generated almost-automorphism hosts of aperiodic trees whatever their local actions are.
  almost-automorphism-conjugate-to-proper-power-is-equicontinuous: that studies almost automorphisms of regular trees, where cones at different levels are isomorphic; this shows that with aperiodic branching no level shift exists and the almost-automorphism group is an ascending union of profinite groups.
---

**ESTABLISHED** through `aperiodic-tree-almost-automorphism-fg-subgroups-are-rf-proof`.
Lane proof, not independently reviewed. Elementary; no novelty is claimed.

## Setting

- `m = (m_1, m_2, ...)` with every `m_i >= 2`, and `T` the spherically homogeneous
  rooted tree with branching `m`: each vertex at level `k-1` has `m_k` children.
- For a vertex `u` at level `k`, the subtree `T_u` below `u` is spherically
  homogeneous with branching `s^k m = (m_{k+1}, m_{k+2}, ...)`. Its end set is the
  cone `C(u)` of the Cantor set `∂T = ∏_i Z/m_i`.
- An **almost automorphism** of `T` is a homeomorphism `h` of `∂T` with finite
  partitions `∂T = ⊔_i C(u_i) = ⊔_i C(w_i)` into cones and tree isomorphisms
  `T_{u_i} -> T_{w_i}` that induce `h` on each `C(u_i)`. They form a group
  `AAut(T)`. It contains every Röver–Nekrashevych-type group built on `T` from
  prefix permutations and tree automorphisms acting on cones.

## Statement

Suppose `m` is **not eventually periodic**. Then:

1. `AAut(T)` is the ascending union of the groups `G_K`, `K >= 0`. Here `G_K`
   consists of the homeomorphisms that permute the level-`K` vertices and act on
   each level-`K` cone by a tree isomorphism. `G_K` is isomorphic to
   `Aut(T_(K)) wr Sym(L_K)`, where `L_K` is level `K` and `T_(K)` has branching
   `s^K m`. It is profinite, and `G_K <= G_(K+1)`.
2. Every finitely generated subgroup of `AAut(T)` is residually finite.
   Therefore:
   - no finitely generated subgroup contains a nontrivial divisible group, in
     particular `(Q,+)` or `GL_n(Q)` for `n >= 2`;
   - every finitely generated simple subgroup of `AAut(T)` is finite, so
     `AAut(T)` contains no infinite finitely presented simple group.
3. If `m` **is** eventually periodic, only finitely many primes divide the
   numbers `m_i`. So every tree whose branching involves infinitely many primes
   (for example `m = (2, 3, 5, 7, 11, ...)` or `m = (2, 3, 4, 5, ...)`) falls
   under items 1 and 2.

## Consequence for GL_n(Q)

Varying-degree and all-primes trees cannot supply the non-residually-finite
divisible part that obstruction O1 of `gl-n-q-embeds-in-fp-simple-group`
demands of a finitely generated host. A tree device needs level shifts, meaning
isomorphic cones at different levels. By item 1 that forces eventually periodic
branching, and then only finitely many primes occur (item 3).

One prime is already enough in one case: `pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori`
puts all of `PGL_2(Q)` inside the Röver–Nekrashevych group of a self-similar
group on the `p`-ary tree, whose level shifts supply the `p`-divisibility.

Nothing is claimed about `AAut(T)` itself, which is not finitely generated.
