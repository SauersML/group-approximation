---
rg: 2
id: depth-mismatched-qutrit-root-bridge-proof
kind: route
title: Convert the depth return into a polynomial matrix parameter
target: depth-mismatched-qutrit-root-bridge-is-residually-finite
requires:
  - matched-leavitt-opposite-root-qutrit-bridge-is-gl28
  - thompson-27-cylinder-qutrit-cell-is-fd-invisible
  - leavitt-gl-equals-el-and-perfect-unit-group
  - thompson-v-lifts-through-binary-leavitt-steinberg-cover
  - finite-support-corner-localizes-obstruction
---

Use the same right-module chart as in the one-chart theorem:

```text
Phi:R^D direct_sum R^(n-1) -> R^n,
Phi((c_d)_(d in D),b_2,...,b_n)
  =(sum_(d in D)s_d c_d,b_2,...,b_n).                  (DMQ4)
```

Prefix-freeness gives, for `d in D`,

```text
t_(d_0 a)s_d =
  t_a,   if d=d_0,
  0,     if d!=d_0.                                    (DMQ5)
```

Let `star` denote coordinate `2).  Conjugating the generators by
`Phi` therefore gives

```text
D_n(f)              |-> the permutation f on D,
e_12(s_(d_0))       |-> 1+E_(d_0,star),
e_21(t_(d_0 a))     |-> 1+E_(star,d_0)(t_a).            (DMQ6)
```

All other module coordinates are fixed.  The pure words
`1,t_a,t_a^2,...` are linearly independent by the standard Leavitt normal
form.  Hence

```text
F_2[T] -> R,                 T |-> t_a                  (DMQ7)
```

is an injective unital algebra map.  Formula `(DMQ6)` places every
generator in the corresponding scalar polynomial matrix group.  The scalar
matrix map is injective entry by entry, and `Phi` is an isomorphism, so

```text
H <= GL_(m+1)(F_2[T])                                    (DMQ8)
```

is a literal embedding, not a specialization.  Packet conjugation makes the
two root families

```text
1+E_(d,star),       1+E_(star,d)(T),          d in D,   (DMQ9)
```

which also makes clear why one extra prefix depth leaves exactly one
polynomial parameter.

We next prove that the initial pair is infinite dihedral.  On the
`{d_0,star}` coordinates write

```text
x=[[1,1],[0,1]],       y=[[1,0],[T,1]],
z=xy=[[1+T,1],[T,1]].                                  (DMQ10)
```

Both `x` and `y` are involutions.  Define polynomials `P_k,Q_k` by

```text
z^k [0,1]^t=[P_k,Q_k]^t.
```

From `(DMQ10)`,

```text
P_1=Q_1=1,
P_(k+1)=(1+T)P_k+Q_k,
Q_(k+1)=T P_k+Q_k.                                     (DMQ11)
```

Inductively, both `P_k` and `Q_k` are monic of degree `k-1`.
Indeed `T P_k` supplies the unique degree-`k` term of `Q_(k+1)`,
and then `P_(k+1)=P_k+Q_(k+1)` has the same leading term.  Thus
`z^k!=1` for every `k>=1` (for `k=1` this is immediate, and for
`k>=2` the lower coordinate `Q_k` has positive degree).  The product of
the two involutions has infinite order.  Every reduced word in two
involutions is an alternating power or an involution times one, so no further
relation is possible; the pair generates `C_2*C_2=D_infinity`.  In
particular `H` is infinite.

Finally, `GL_(m+1)(F_2[T])` is residually finite by elementary coefficient
reduction.  If a matrix `g` is not the identity, choose a nonzero polynomial
entry of `g-1` and take `N` larger than its degree.  Reduction modulo
`(T^N)` maps `g` nontrivially into the finite group

```text
GL_(m+1)(F_2[T]/(T^N)).                                 (DMQ12)
```

Therefore its subgroup `H` is residually finite, hence sofic and
hyperlinear.  Finite-support localization rules out a no-CE atlas supported
inside `C[H]`.

For the standard Steinberg lifts, projection sends the generators onto those
of `H`, so

```text
1 -> Gamma intersect ker(pi) -> Gamma -> H -> 1         (DMQ13)
```

is exact with central kernel in the stable range.  The argument above proves
nothing about whether this particular central extension splits.  That kernel
question, rather than the downstairs opposite-root subgroup, is the precise
remaining issue for this depth-one candidate.
