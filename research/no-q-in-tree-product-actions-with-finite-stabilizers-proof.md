---
rg: 2
id: no-q-in-tree-product-actions-with-finite-stabilizers-proof
kind: route
target: no-q-in-tree-product-actions-with-finite-stabilizers
requires:
  - divisible-elements-act-elliptically-on-trees
  - sl-n-q-lies-in-finite-residual-of-every-overgroup
---

Direct proof. Not independently reviewed.

Let `A <= H` with `A ~ (Q,+)`.

## Step 1. `A` preserves every factor

Let `H_0` be the kernel of the homomorphism `H -> Sym(r)` recording how factors
are permuted. It has index at most `r!`. The image of `A` in `H/H_0` is a finite
quotient of a divisible group, hence trivial (Step 1 of
`sl-n-q-lies-in-finite-residual-of-every-overgroup-proof`). So `A <= H_0`, and
`H_0` acts on each `T_i`.

## Step 2. Every element of `A` fixes a point of `X`

Let `a in A`. It has a `k`-th root in `A <= H_0` for every `k`. By part 1 of
`divisible-elements-act-elliptically-on-trees`, applied to the action of `H_0` on
`T_i`, it fixes a vertex `v_i` of the subdivision `T_i'`: a vertex of `T_i` or the
midpoint of an edge. Then `a` fixes the point `x = (v_1, ..., v_r)` of `X`, which
is a vertex of `X` or the barycentre of a cube `C` of `X` (a product of vertices
and edges).

## Step 3. Point stabilizers are finite

The stabilizer of such an `x` preserves the cube `C` (the unique cube containing
`x` in its relative interior), so it permutes the at most `2^r` vertices of `C`.
The kernel of that permutation action fixes a vertex of `X`, so it is finite. So
`Stab_H(x)` is finite, and `a` has finite order.

## Step 4. Conclusion

Every element of `A` has finite order, but `(Q,+)` is torsion-free. So `A = 1`, a
contradiction with `A ~ (Q,+)`. Each group listed in the claim contains a copy of
`(Q,+)`: an elementary root group, or the translation subgroup of `Aff(Q)`, or the
centre of `U_3(Q)`. So none embeds in `H`.

## The discrete case

For locally finite `T_i` the vertex stabilizers of `Aut(T_1) x ... x Aut(T_r)`,
extended by factor permutations, are compact and open. A discrete subgroup meets a
compact set in a finite set, so its vertex stabilizers are finite.
