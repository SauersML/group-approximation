---
rg: 2
id: leavitt-unit-internal-free-reflections-proof
kind: route
title: Use prefix ping-pong to create a wandering free orbit of Leavitt corners
target: leavitt-unit-internal-free-reflections
requires:
  - wandering-leavitt-corner-reflection-compiler
  - leavitt-cylinder-swaps-generate-thompson-in-el
artifacts:
  - GroupApproximation/Leavitt/PrefixCode.lean
---

Put `R=L_(F_2)(1,2)` and regard the finite binary prefix-table group as a
subgroup of its unit group `U`.

## A clopen ping-pong system

Choose `2r+1` nonempty cylinder sets

```text
A_1^+,A_1^-,...,A_r^+,A_r^-,D
```

which partition the binary Cantor space.  For each `i`, choose finite prefix
tables giving homeomorphisms

```text
X minus A_i^-  -> A_i^+,
A_i^-          -> X minus A_i^+.
```

Combining the two tables gives a prefix-table unit `a_i in U` satisfying

```text
a_i(X minus A_i^-)=A_i^+,
a_i^(-1)(X minus A_i^+)=A_i^-.                          (IFP1)
```

The ping-pong lemma makes `a_1,...,a_r` a free basis of a subgroup
`F~=F_r` of `U`.  More is true: `D` is wandering.  If `g!=1` is represented
by a reduced word, repeated use of `(IFP1)` puts `gD` inside the attracting
set of its first letter, hence outside `D`.  Therefore, for `g!=h`,

```text
gD intersect hD = empty,                                (IFP2)
```

because applying `g^(-1)` reduces the intersection to
`D intersect g^(-1)hD`.

## The regular base inside the wandering corners

Let `p=st` be the cylinder idempotent of `D`, with `ts=1`.  For `g in F`,
put

```text
s_g=g s,                  t_g=t g^(-1),                 (IFP3)
p_g=s_g t_g=g p g^(-1).
```

Equation `(IFP2)` gives

```text
t_g s_h=delta_(g,h),       p_g p_h=0 for g!=h.           (IFP4)
```

For a finitely supported tuple `u=(u_g) in U^(F)`, define

```text
beta(u)=1+sum_g s_g(u_g-1)t_g.                          (IFP5)
```

The relations `(IFP4)` show that `beta` is injective and multiplicative.
Conjugation by `k in F` sends the `g`th corner to the `kg`th corner, so it
implements the regular shift on the base.

The diagonal base fixes every `p_g`, while a nonidentity `k in F` moves
`p_1` to the distinct idempotent `p_k`.  Hence the generated semidirect
product is internal and the map

```text
U^(F) semidirectProduct F -> U
```

is injective.  A finite generating set for `U` in the identity corner,
together with `a_1,...,a_r`, generates it.

Thus `p` has a wandering `F_r`-orbit, and the wandering-corner reflection
compiler applies.

## Reflection and closure

Every MF-target homomorphism kills each coordinate copy of `U`, hence the
whole base, and factors uniquely through `q_r:W_r->F_r`.  Conversely, `F_r`
is residually finite and therefore MF, so the quotient detects every element
outside the base.  This proves `(IF2)` and `(IF3)`.  Triviality of all maps
from `U` to the other target classes gives their factorization statements in
the same way.

For a normal subgroup `N` of `W_r`, MF-target maps killing `N` correspond
exactly to MF-target maps from `F_r` killing `q_r(N)`.  Intersecting kernels
and pulling back proves `(IF4)`.  The final quotient and nonisomorphism
statements follow immediately from the universal property of the MF
reflection.
