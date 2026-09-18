---
rg: 2
id: divisible-elements-act-elliptically-on-trees-proof
kind: route
target: divisible-elements-act-elliptically-on-trees
requires:
  - sl-n-q-lies-in-finite-residual-of-every-overgroup
---

Direct proof. Not independently reviewed. The only input from the required node
is its Step 1: a residually finite group contains no nontrivial divisible
subgroup, since a divisible group has no nontrivial finite quotient.

## Input: Tits' dichotomy

(Serre, *Trees*, Ch. I §6.4, Prop. 24.) Let `s` be an automorphism of a tree
without inversion and `l(s) = min_P d(P, sP)` over vertices `P`. If `l(s) = 0`,
`s` fixes a vertex. If `l(s) > 0`, the set of vertices realizing the minimum is a
line `A_s` (the axis), `s` translates `A_s` by `l(s)`, and
`d(P, sP) = l(s) + 2 d(P, A_s)` for every vertex `P`. The fixed-vertex set of an
automorphism, or of a group of automorphisms, without inversion is a subtree,
since geodesics between fixed vertices are fixed.

Work on `T'`, where `H` acts without inversions.

## Part 1

Let `h` be hyperbolic with axis `A` and `l = l(h) >= 1`, and let `k >= 1`. Then
`h^k` preserves `A` and translates it by `kl`, and for a vertex `P` with
projection `π` onto `A`, the path `P -> π -> h^k π -> h^k P` is a geodesic (its
middle part lies on `A`, the outer legs meet `A` only at their ends, and
`kl > 0`). So `d(P, h^k P) = kl + 2 d(P, A) >= k`, and `h^k` is hyperbolic with
`l(h^k) = k l(h)`. An elliptic `h` has elliptic powers.

Now let `g = h^k` be hyperbolic. Then `h` is hyperbolic, and `l(g) = k l(h) >= k`.
So `g` has `k`-th roots only for `k <= l(g)`. An element with roots of infinitely
many orders is therefore elliptic.

## Part 2

Let `A ~ (Q,+)` and `A_m = <a_m>` with `a_m = 1/m!`. The `A_m` increase and their
union is `A`. Each `a_m` has a `k`-th root in `A` for every `k`, so it is elliptic
by Part 1. The sets `F_m = Fix(A_m) = Fix(a_m)` are nonempty subtrees of `T'`, and
they decrease.

Fix a vertex `x`, and let `y_m` be the vertex of `F_m` nearest to `x` (the
projection onto a subtree). For every `z in F_m` the geodesic `[x, z]` passes
through `y_m`. Since `y_(m+1) in F_(m+1) ⊆ F_m`, the geodesic `[x, y_(m+1)]` passes
through `y_m`. So the `y_m` lie in order on one geodesic from `x`, and `d(x, y_m)`
does not decrease.

- If the `y_m` are eventually constant, equal to `y`, then `y in F_m` for all large
  `m`, hence for all `m`, and `A` fixes `y`.
- Otherwise the `y_m` run along a ray `ρ` from `x` to an end `ξ`. For `k >= m`,
  `y_k in F_k ⊆ F_m`, and `F_m` is convex, so `A_m` fixes pointwise the subray of
  `ρ` from `y_m`. So every `A_m`, hence `A`, fixes `ξ`.

**Uniqueness of the end.** Suppose `A` fixes no vertex of `T'` but fixes two ends
`ξ != η`, and let `L` be the line joining them. Each `a in A` preserves `L`, fixing
both of its ends, so it translates `L`. Also `a` is elliptic with a fixed vertex
`Q`. Then `a` fixes the projection of `Q` onto `L`, so the translation is trivial
and `a` fixes `L` pointwise. Hence `A` fixes every vertex of `L`, a contradiction.

## Part 3

The stabilizer of a vertex of `T'` is either a vertex stabilizer of `T`, or the
setwise stabilizer of an edge `{u, v}`. The latter contains `Stab(u) ∩ Stab(v)`
with index at most 2. A group with a residually finite subgroup of finite index is
residually finite. So all vertex stabilizers of `T'` are residually finite. If `A`
fixed a vertex of `T'`, it would be a nontrivial divisible subgroup of a
residually finite group, which is impossible. So `A` is in the second case of
Part 2. The root groups `U_ij(Q)` of `GL_n(Q)` are copies of `(Q,+)`.
