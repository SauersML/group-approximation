---
rg: 2
id: right-u-reynolds-has-torus-hecke-blocks
kind: claim
title: The right-unipotent Reynolds space decomposes into torus-character Hecke blocks
distinct_from:
  constrained-reynolds-column-has-a-diagonal-scalar-shadow: that identifies the whole sign-induced column; this gives its exact right-unipotent Mackey/Fourier decomposition and corrects the projective-slice dimension.
  full-torus-reynolds-is-multipartite-curl: that resolves deeper root fibers when the cyclic dilation fills the torus; this isolates the additional proper-subtorus blocks already over the residue field.
---

**ESTABLISHED; EXACT REDUCTION, NOT A UNIFORM BOUND.**  Let

```text
G=PSL_2(F_p),       U={u(a)},       T={h(a)},
H=<h(2)>,           N=<H,w>,       chi|_H=1, chi(w)=-1.
```

Write `D=Ind_N^G chi`, the scalar tangent domain `(DSS7)`.  Since `U` is a
`p`-group and `|N|=2|H|` is prime to `p`,

```text
N cap gUg^(-1)={1}                                    (RUB1)
```

for every `g`.  Thus every double coset contributes one basis vector and

```text
dim D^U=|N\G/U|
 =|G|/(|N||U|)
 =(p^2-1)/(4|H|)
 =((p+1)/2)i_p.                                        (RUB2)
```

The torus `T` normalizes `U`, so right translation by `T` acts on `D^U`.
For `theta in dual(T)`, put

```text
P_theta=|T|^(-1) sum_(t in T) conjugate(theta(t)) R_t. (RUB3)
```

The scalar column is built from left translations and therefore commutes
with every `P_theta`.  Consequently

```text
C_G^U = direct_sum_(theta in dual(T)) C_(G,theta),
C_(G,theta)=C_G P_theta,                                (RUB4)
```

and the normal operator and Moore--Penrose inverse have the same orthogonal
block decomposition.

There is a completely explicit principal-series realization of each
block.  The quotient `G/U` is the set of nonzero column vectors in
`F_p^2`, modulo the central sign.  Right multiplication by `h(a)` scales
the first column by `a`.  Thus the `theta` block consists of homogeneous
functions

```text
F(av)=theta(a)F(v).                                    (RUB4a)
```

On the affine chart write `F(z,1)=phi(z)`.  Left `H` invariance and the
left Weyl sign become

```text
phi(4z)=theta(2)phi(z),
theta(z)phi(-1/z)=-phi(z)                              (RUB4b)
```

for nonzero `z`, together with the analogous `0,infinity` pair.  If
`g=[[a,b],[c,d]]`, its block action is the weighted Mobius operator

```text
(T_g^theta phi)(z)
 =theta(cz+d) phi((az+b)/(cz+d)),                      (RUB4c)
```

with the homogeneous interpretation when `cz+d=0`.  Hence the two rows
are explicitly

```text
T_(S^2)^theta+T_(S^2A^(-1))^theta+T_(S^2A^(-2))^theta,
T_S^theta+T_(SB^(-1))^theta+T_(SB^(-2))^theta.         (RUB4d)
```

After choosing one representative from each multiplication-by-`4` orbit,
these are finite matrices with three character phases in every row.  They
are circulant along each torus orbit, while the Mobius transitions couple
the different orbits.

This is a concrete finite Fourier/Hecke model.  The right-`T` orbits in
`N\G/U` are the double cosets `N\G/B`, where `B=TU`.  For a representative
`g`, the orbit is `T/T_g`, with

```text
T_g = image in T of (g^(-1)Ng cap B).                  (RUB5)
```

The `theta` block has one Fourier coordinate on this orbit exactly when
`theta|_(T_g)=1`.  In those coordinates each of the two Reynolds rows is a
three-term matrix whose nonzero entries are the character phases of the
corresponding transitions by

```text
S^2, S^2A^(-1), S^2A^(-2)
```

or

```text
S, SB^(-1), SB^(-2).                                   (RUB6)
```

Thus every block is an explicit finite twisted-circulant Hecke operator on
the orbit cycles `(RUB5)`.  Stabilizers and transition cocycles can vary
between the `N\G/B` orbits, so the whole column is not one circulant matrix.

The previously computed `P^1(F_p)` slice is only

```text
(D^U)^T=D^B=P_1 D^U,                                  (RUB7)
```

the **trivial** torus-character block.  Its functions satisfy

```text
f(4z)=f(z),              f(-1/z)=-f(z),
```

but it has dimension only `i_p` or `i_p+1`, versus the full dimension
`((p+1)/2)i_p` in `(RUB2)`.  Hence bounded Green norms on the projective
block do not control the many nontrivial torus characters.  This exactly
explains why the projective probe can remain small while the full scalar
inverse grows.

The reduction proves neither a uniform bound nor divergence.  It replaces
the incorrect single-projective-slice target by the exact finite family

```text
sup_(p,theta) ||C_(G,theta)^dagger||_(infinity -> infinity). (RUB8)
```

A uniform estimate for all the twisted orbit matrices `(RUB6)`, together
with the full-torus prime-power theorem, advances the exact-endpoint gate.
A divergent character block refutes it.  Controlling each block in its
Hilbert norm is insufficient by itself, because Fourier recombination is
not unconditional in `l_infinity`.

`near-trivial-torus-characters-track-the-moving-kernel` rules out the
simplest proposed divergent block.  Perturbing the trivial character moves
its gradient kernel continuously; after Moore--Penrose projection and
normalization the residual retains the nonzero Hilbert singular gap.  A
bad infinity mode must therefore exploit genuinely dimension-dependent
geometry rather than character continuity alone.
