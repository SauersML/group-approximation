# A bit-level transporter with no finite-dimensional boundary submodules

Date: 2026-09-08. This gives an explicit transporter outside the scope
of the proved macro-prefix obstruction. It does not construct a split
`L P_0[g]f_0=f_0`, rule out such a split, or solve Kaplansky's conjecture.
No computation is used.

## The chart and the transporter

Represent each coordinate of `F_4^2` by its two `F_2` coordinates in
the basis `1,omega`, with `omega^2=omega+1`. The original finite chart
`K=GL_2(F_4)` therefore acts on four binary root coordinates:
roots `1,2` encode the first field coordinate, and roots `3,4` the
second. Multiplication by `omega` on each pair has matrix

```
Omega = [0 1; 1 1].
```

Let `V` be the free `F_2` vector space on the disjoint union of four
binary Cantor boundaries. Every vector has finite support. Constant
chart matrices act on the root-coordinate index and preserve the
infinite tail.

Define a binary prefix permutation `g` by the complete table

```
1 -> 10,    20 -> 11,    21 -> 2,    3 -> 3,    4 -> 4.
```

The tails following the displayed prefixes are unchanged. Both the
domain and range cylinders partition the four-root boundary, so
this is an invertible boundary permutation.

For an algebraic check, let `s_0,s_1` prepend a binary digit and let
`t_0,t_1` remove that digit, annihilating a basis ray whose first
digit does not match. They satisfy the binary Leavitt relations.
On the first two binary roots the matrix of `g` is

```
a = [s_0   s_1 t_0;  0   t_1],
a^-1 = [t_0   0;  s_0 t_1   s_1].
```

Multiplying in either order gives identity, using
`t_i s_j=delta_ij` and `s_0 t_0+s_1 t_1=1`. On roots `3,4`, `g`
is identity. Thus it is also a concrete unit in `M_4(L_2(F_2))`.
The usual length-two Leavitt identification places that unit in
the ambient binary Leavitt unit group.

This `g` is not `F_4` linear: the `(1,1)` entries of `a Omega` and
`Omega a` are respectively `s_1 t_0` and zero. The former is nonzero,
since `t_1(s_1 t_0)s_0=1`. It is therefore not a macro-prefix
permutation on the chosen `F_4` boundary basis. The distinction is
the explicit field structure, not the mere use of a binary table.

## No finite-dimensional submodule for the two charts

Put `H=<K,g^-1 K g>`. The restriction of `V` to `H` has no nonzero
finite-dimensional invariant subspace.

Suppose such a subspace `W` exists. A finite basis of `W` has a finite
union `S` of boundary supports. For any fixed infinite tail `xi`,
evaluation of its four coefficients is a `K`-equivariant map

```
ev_xi: W -> F_2^4.
```

The natural `F_2` representation of `GL_2(F_4)` is irreducible:
the group is transitive on the fifteen nonzero vectors of `F_4^2`,
so any nonzero invariant `F_2` subspace contains them all. Consequently
every nonzero evaluation image is all of `F_2^4`. The support union
therefore has the exact form

```
S={1,2,3,4} x T
```

for a finite nonempty set of tails `T`.

Since `W` is invariant under `g^-1 K g`, the space `gW` is invariant
under `K`. Its support union is exactly `gS`, because `g` permutes
the boundary basis. The same argument gives

```
gS={1,2,3,4} x T'
```

for another finite set `T'`. The prefix table fixes roots `3,4`,
and no other root is sent into either one. Comparing the support
on root `3` gives `T'=T`.

The rule `1->10` now forces `0T` to be a subset of `T`. Prefixing
zero is injective; on a finite set this inclusion makes it a
permutation. Every tail in `T` is therefore fixed by some positive
iterate of prefixing zero, and hence is `000...`. Nonemptiness gives
`T={000...}`. But the rule `20->11` sends the basis point `2 000...`
to `1 1000...`, forcing the different tail `1000...` into `T`.
This contradiction proves the assertion.

This argument covers arbitrary finite-dimensional invariant
subspaces of the free boundary module, not only spans of finite
invariant sets of boundary points.

## The obstruction method also fails in every positive exterior degree

For every integer `d>=1`, the exterior power `Lambda^d V` has no
nonzero finite-dimensional `H`-invariant subspace.

Indeed, suppose `E` were such a subspace. A finite basis of `E` uses
only finitely many vectors from a boundary basis, so its essential
vector support is finite-dimensional. Concretely, define `U` to be
the span of all iterated contractions of members of `E` by `d-1`
arbitrary linear functionals on `V`. These contractions lie in a
fixed finite-dimensional span of boundary vectors. They are not all
zero: contracting a nonzero basis-wedge coefficient against its
other `d-1` basis duals leaves a vector with that nonzero coefficient.

Contraction is natural under invertible linear maps:

```
h i_phi(w) = i_(phi composed with h^-1)(h w).
```

As `E` is `H` invariant and the dual forms range over all linear
functionals, `U` is `H` invariant. It is nonzero and finite-dimensional,
contradicting the preceding theorem for `V`. Iterated contraction
uses no factorial or division, so the proof applies in characteristic
two as stated. Degree zero, the trivial representation, is excluded.

The conclusion also holds after extending scalars to `F_4`. As an
`F_2[H]` module, each scalar extension is a direct sum of two copies
of the original module. A nonzero finite-dimensional invariant
subspace would have a nonzero finite-dimensional image under one
of the two coordinate projections. Exterior powers commute with
this scalar extension. Thus extending coefficients does not restore
the finite exterior submodules used in the macro-prefix proof.

## What remains open

The [macro-prefix theorem](kaplansky-single-macro-prefix-transporter-obstruction-2026-09-08.md)
uses a finite module inside the natural boundary representation and
its exterior powers for two conjugate finite charts. No such module
exists for this transporter in the displayed binary representation.
Repeating that particular finite-submodule construction cannot decide
this case.

The result does not exclude finite-dimensional quotients, other
representations of `H`, kernels in an infinite-dimensional exterior
power, or other group-algebra obstructions. It does not assert that
the relevant group is amenable or nonamenable. In particular it gives
no injectivity certificate for `P_0[g]f_0` and no proposed left inverse.
The comparison equation remains unresolved for this explicit actor.
