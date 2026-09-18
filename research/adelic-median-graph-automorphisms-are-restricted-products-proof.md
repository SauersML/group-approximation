---
rg: 2
id: adelic-median-graph-automorphisms-are-restricted-products-proof
kind: route
title: Proof via squares, fibres and profinite point stabilizers that automorphisms of the adelic median graph are restricted products
target: adelic-median-graph-automorphisms-are-restricted-products
requires: []
---

**Step 1 (directions are detected by squares).** Let `e = [v, a]` and
`e' = [v, b]` be distinct edges at a vertex `v`.

- If their directions `p ≠ q` differ, let `w` agree with `a` in coordinate `p`,
  with `b` in coordinate `q`, and with `v` elsewhere. Then `v, a, w, b` is a
  4-cycle.
- If both have direction `p`, then `a_p ≠ b_p` are neighbours of `v_p` in
  `T_p`, and `a`, `b` agree with `v` elsewhere. Suppose `w ≠ v` is adjacent to
  both. If `w` differed from `a` in a coordinate `r ≠ p`, then
  `w_p = a_p ≠ b_p` and `w_r ≠ v_r = b_r`, so `w` would differ from `b` in two
  coordinates. So `w` differs from `a`, and likewise from `b`, only in
  coordinate `p`. Then `w_p ≠ v_p` is a common neighbour of `a_p` and `b_p` in
  the tree `T_p`, which is impossible.

So two distinct edges at `v` have the same direction exactly when they lie in
no common 4-cycle. This relation is defined by the graph alone, so every
automorphism `φ` preserves it. At each vertex the classes of this relation are
the directions, and the class of `p` has `p + 1` edges. `φ` maps the classes at
`v` bijectively onto the classes at `φ(v)` and preserves their sizes. Since the
sizes `p + 1` are pairwise distinct, `φ` maps direction `p` at `v` to direction
`p` at `φ(v)`. So `φ` preserves the direction of every edge.

**Step 2 (coordinates).** The `p`-fibre of `x` is the set of vertices that
agree with `x` outside coordinate `p`. It is a copy of `T_p`, and it is the
component of `x` in the subgraph of `p`-edges. By Step 1, `φ` maps `p`-fibres
to `p`-fibres. So `φ(y)_r = φ(x)_r` whenever `y` and `x` differ only in a
coordinate `p ≠ r`.

Two vertices with the same `r`-coordinate differ in finitely many coordinates,
all different from `r`, and can be joined by moving in one fibre at a time. So
`φ(x)_r` depends only on `x_r`. Write `φ(x)_r = φ_r(x_r)`. Each `φ_r` preserves
adjacency, since `r`-edges go to `r`-edges, and is bijective, as we see by
applying the same argument to `φ^-1`. So `φ_r ∈ Aut(T_r)`. Since `φ(o)` is a
vertex of `X`, `φ_r(o_r) = o_r` for almost all `r`.

Conversely, such a family maps restricted families to restricted families and
preserves adjacency. This proves item 1.

**Step 3 (finitely generated subgroups).** Let `g_1, ..., g_k` generate `E`,
and let `S` be the finite set of primes `r` at which some `g_i` moves `o_r`. For
`q` not in `S`, the elements `φ` with `φ_q(o_q) = o_q` form a subgroup that
contains every `g_i`, hence contains `E`. So `E ≤ A_S × K_S`.

Each `Aut(T_q)_(o_q)` is the inverse limit of the finite automorphism groups of
the balls of radius `m` about `o_q`, so it is profinite, and hence so is
`K_S`. This proves item 2.

**Step 4 (residual finiteness).** A profinite group is residually finite. A
residually finite group has no nontrivial divisible subgroup. Indeed, if
`π(g) ≠ 1` in a finite quotient `F`, write `g = h^|F|` inside the divisible
subgroup; then `π(g) = π(h)^|F| = 1`, a contradiction.

`PSL_2(Q)` is an infinite simple group (Jordan--Dickson, since `|Q| > 3`), so
it is not residually finite. So every homomorphism from it to a residually
finite group is trivial. For `SL_2(Q)`, let `N` be the kernel of a homomorphism to a residually finite
group. If `N ⊆ {±I}`, the image is `SL_2(Q)` or `PSL_2(Q)`, which is residually
finite as a subgroup. But both contain the divisible unipotent `(Q,+)`, which
meets `{±I}` trivially. So `N` is not central. The normal subgroups of
`SL_2(Q)` are `1`, `{±I}` and `SL_2(Q)`, since `SL_2(Q)` is perfect with
simple central quotient: a noncentral normal `N` maps onto `PSL_2(Q)`, so
`N{±I} = SL_2(Q)` and `SL_2(Q) = [N{±I}, N{±I}] ⊆ N`. Hence `N = SL_2(Q)`. For `GL_2(Q)` and
`PGL_2(Q)`, apply this to the commutator subgroups `SL_2(Q)` and `PSL_2(Q)`.
Applied to `E -> K_S`, this proves item 3.

**Step 5 (the standard action).** An element `g ∈ PGL_2(Q)` fixes `o_q` exactly
when `g Z_q^2 = λ Z_q^2` for a representative `g` and some `λ ∈ Q_q^x`. For
`g = e_12(1/q)` this is false, as in
`cocompact-fg-stabilizer-actions-force-finite-generation-proof`, item 2.
So the standard `SL_2(Q)` moves `o_q` for every `q`, and it is not contained in
`A_S × K_S` for any finite `S`.

For `g ∈ GL_2(Q)` fixing `o_q` for every `q` not in `S`, rescale `g` by the
finitely many primes `q` not in `S` with `λ_q` not a unit. Then `g` lies in
`GL_2(Z_q)` for every `q` not in `S`. So `E ∩ PGL_2(Q) ⊆ PGL_2(Z[1/S])` and,
with determinant one, `E ∩ SL_2(Q) ⊆ SL_2(Z[1/S])`. This proves item 4.
