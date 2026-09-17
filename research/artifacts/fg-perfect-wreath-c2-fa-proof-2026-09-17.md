# Commuting conjugate factors force each other's axes to be fixed

*Attempt artifact (2026-09-17), formerly route `fg-perfect-wreath-c2-fa-proof` into `fg-perfect-wreath-c2-has-property-fa`, requires []. Demoted from the graph because one of three referee votes was lost; the two returned votes found no gap. Restore it as a route once a full referee pass survives.*

Standard facts, Serre, *Trees*, Chapter I, §6.1--6.5: an automorphism of a tree
without inversions is either elliptic (it fixes a vertex) or hyperbolic (it
translates a unique line, its axis, by a nonzero amount); `b L_h = L_(b h b^-1)`
for axes; a finitely generated group acting so that every element is elliptic has
a global fixed point; the fixed set of a group is a subtree; a group with a
bounded orbit fixes a vertex or an edge, hence, without inversions, a vertex.

Suppose `W = (A_1 x A_2) ⋊ <sigma>` acts on a tree `T` without inversions, with
`A_1, A_2` the two copies of `A` and `sigma A_1 sigma^-1 = A_2`.

**Step 1 (reduce to a factor).** If `N = A_1 x A_2` fixes a vertex `v`, the
`W`-orbit of `v` is `{v, sigma v}`, which is bounded, so `W` fixes a vertex. If
`A_1` and `A_2` each fix a vertex, then `Fix(A_1)` is a nonempty subtree and is
`A_2`-invariant because the factors commute. Nearest-point projection onto
`Fix(A_1)` is `A_2`-equivariant, so it sends a vertex fixed by `A_2` to a vertex
fixed by `A_1` and `A_2`, and `N` has a fixed vertex. So if `W` has no fixed
vertex, some `A_i` has none, and since `A_2 = sigma A_1 sigma^-1`, neither has.

**Step 2 (a commuting group fixes the axes).** `A_1` is finitely generated and
fixes no vertex, so it contains a hyperbolic `h` with axis `L`. Let `b in A_2`.
Since `b h b^-1 = h`, `b` preserves `L`, so `b|_L` is a translation or a
reflection. A reflection `r` gives `r h|_L r^-1 = h^-1|_L != h|_L`, which is
impossible. So `b` translates `L` by some `tau`. If `tau != 0`, `b` is hyperbolic
with axis `L`. The same holds for every hyperbolic `h' in A_1`: `b` preserves
`L_(h')` and cannot fix it pointwise, since a hyperbolic element fixes no vertex,
so `L_(h') = L_b = L`. Then `g L = L_(g h g^-1) = L` for all `g in A_1`, so `A_1`
acts on `L` through a homomorphism into `Aut(L)`, the infinite dihedral group,
which is solvable. As `A_1` is perfect, the image is trivial, so `h` fixes `L`
pointwise, a contradiction. Hence `tau = 0` and `b` fixes `L` pointwise.

So `A_2` fixes `L` pointwise, contradicting Step 1. Therefore `W` has a fixed
vertex. `∎`

**Where perfectness is used.** Only in Step 2, to kill the action on a common
axis. For `A = Z` the statement is false: `Z wr C_2` maps onto `Z` by
`(m, n, e) -> m + n`, and `Z` acts on a line without fixed point.
