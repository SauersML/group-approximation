# A single seven-point permutation head already violates the first braid

2026-09-08. The proposed replacement of the natural linear boundary
head by its seven-point permutation action cannot satisfy the original
first braid. The obstruction is finite and does not depend on eventual
ray behavior, the TS relation, or the extra shifted finite packet.

Let `G=GL_3(F_2)` act on the seven boundary points
`X=F_2^3\{0}` in its natural permutation action, and fix an arbitrary
disjoint set `Y`. The tail factor fixes `X` pointwise and acts on `Y`.
Thus this includes the proposed action on seven rays with the head at
level zero and the tail on all positive levels.

Write

```text
A_i=e_i,                 B_i=sum_(j!=i)e_j,
C=e_1+e_2+e_3,
K=GL(<e_1,e_3>)_Q,       B=(w_23,w_23).
```

Let `H` be any permutation of `X disjoint-union Y` centralizing `K`.
Then, in the permutation representation on complex `ell^2`,

```text
||(HB)^3-I||=2.                                      (1)
```

In particular no such `H` gives a representation of `Gamma`, and
adding `R`, `W`, or further finite-packet relations cannot produce one.

## Proof

The nontrivial `K`-orbits are exactly the two triples

```text
X_0={A_1,A_3,B_2},
X_1={B_3,B_1,C}.
```

All other points, including `A_2` and `Y`, are fixed by `K`. On each
triple `K` acts as the full symmetric group on three points, whose
permutation centralizer is trivial. There is a unique equivariant
bijection from `X_0` to `X_1`, namely `v |-> v+e_2`:

```text
A_1 <-> B_3,       A_3 <-> B_1,       B_2 <-> C.
```

A `K`-central permutation must preserve the union of the nontrivial
orbits. It therefore has exactly two possibilities there: fix both
triples pointwise, or exchange them by this bijection. Its behavior on
the `K`-fixed set can be arbitrary and will not enter the argument.

On the boundary, `B` acts as the coordinate swap `w_23`. It fixes
`A_1,C` and interchanges `B_2,B_3`.

If `H` fixes both triples, `HB` has the two-cycle

```text
(B_2 B_3).
```

If `H` exchanges the triples, `HB` has the four-cycle

```text
(A_1 B_3 C B_2).
```

These cycles lie entirely within the boundary. Their cubes are still
even cycles and therefore have eigenvalue `-1` on their finite
permutation subspace. This gives the lower bound two in (1). The upper
bound two holds for every unitary operator. No assumption `H^2=I` was
needed: the centralizer calculation itself forces the displayed
restriction of `H` to be an involution.

## Scope

This addresses exactly one seven-point head orbit together with
head-fixed points. It differs from the existing
[product-packet permutation bound](jacobson-natural-head-permutation-gap-2026-09-08.md),
which concerns a head action on `X x T`. Multiple seven-point head
orbits allow `H` to mix additional equivariant triples; the two-case
argument above does not cover them. It also does not apply to arbitrary
linear or unitary `H`.

The orbit and cycle calculations were independently audited. No search,
local computation, MSI job, or formal proof checker was used.
