---
rg: 2
id: stw81-two-colour-af-field-proof
title: Two-colour proof for locally trivial AF-fibre fields
kind: route
target: stw81-one-dim-simple-af-fields-have-dim-one
requires: []
artifacts:
  - research/artifacts/stw81-one-dimensional-af-field-audit-2026-08-30.md
---

# Two-colour proof for locally trivial AF-fibre fields

Let `X,D,A` be as in the theorem. We prove the nuclear-dimension estimate
directly and then verify the hereditary-shadow assertion.

## 1. Compact localization

Fix a finite self-adjoint set `F` in `A` and `epsilon>0`. Because the norm
functions of sections in `A` vanish at infinity, there is
`h in C_c(X)_+`, with `0<=h<=1`, such that

```text
||a-ha|| < epsilon/4     (a in F).
```

Thus it is enough to approximate `hF`, whose relevant base is contained in
the compact set `K=supp(h)`.

For every `x in K`, choose a bundle trivialization

```text
theta_x: A|U_x -> C_0(U_x,D).
```

After shrinking around `x`, continuity of the finitely many local sections
gives an open neighborhood `V_x` with closure in `U_x` on which

```text
||theta_x(a(y))-theta_x(a(z))|| < delta                 (1)
```

for `a in F` and `y,z in V_x`, where `delta>0` will be chosen at the end.

## 2. The two-coloured cover

The coloured-refinement characterization of covering dimension for
second-countable locally compact spaces gives a finite refinement of the
cover of `K` which splits as

```text
V = V^(0) disjoint-union V^(1),
```

where closures remain in trivializing neighborhoods and the members of each
`V^(c)` are pairwise disjoint. Concretely, first take a locally finite
refinement of order at most two and then pull back the open stars in the
barycentric subdivision of its one-dimensional nerve. Colour a vertex by
the dimension of the face it barycentrizes. Equal-coloured open stars are
disjoint.

Choose points `x_i in V_i` and functions `f_i in C_c(V_i)_+` such that
`sum_i f_i=1` on a neighborhood of `K`. Put `g_i=hf_i`. Then

```text
sum_i g_i = h,                                           (2)
```

and supports of the `g_i` are disjoint within each colour.

## 3. Zero-colour fibre approximations

For each `i`, use the AF property of `D` to choose a unital
finite-dimensional subalgebra `F_i` of `D` within `delta` of

```text
{theta_i(a(x_i)) : a in F}.
```

Finite-dimensional C-star algebras are injective, so the identity on `F_i`
extends to a unital completely positive contraction

```text
E_i: D -> F_i.
```

If `z` is within `delta` of `F_i`, contractivity and `E_i|F_i=id` give

```text
||E_i(z)-z|| < 2 delta.                                  (3)
```

Define a completely positive contraction

```text
psi: A -> F_total := direct-sum_i F_i,
psi_i(a) = E_i(theta_i(a(x_i))).
```

For `c in F_i`, define a section by

```text
phi_i(c)(y) = g_i(y) theta_i,y^(-1)(c)   if y in V_i,
              0                           otherwise.
```

The support condition on `g_i` makes this a continuous section vanishing at
infinity. The map `phi_i:F_i->A` is c.p.c. and order zero: it is a fibrewise
star-homomorphism multiplied by one scalar positive contraction.

For `c=0,1`, set

```text
F^(c) = direct-sum_(i in V^(c)) F_i,
phi^(c) = sum_(i in V^(c)) phi_i.
```

Because equal-coloured supports are disjoint, each `phi^(c)` is again c.p.c.
and order zero. The total completely positive map
`phi=phi^(0)+phi^(1)` is contractive as well: fibrewise,

```text
phi(1_F_total) = (sum_i g_i) 1 = h 1 <= 1,
```

where the unit is interpreted in the multiplier bundle when `X` is
noncompact.

## 4. Approximation estimate

For `a in F`, `y in X`, and each `i` with `g_i(y)!=0`, (1) and (3) imply

```text
||theta_i(a(y))-E_i(theta_i(a(x_i)))|| < 3 delta.
```

Using (2) and positivity of the `g_i`,

```text
||ha-(phi^(0)+phi^(1))psi(a)|| < 3 delta.
```

Taking `delta<epsilon/4` and combining this with compact localization gives

```text
||a-(phi^(0)+phi^(1))psi(a)|| < epsilon     (a in F).
```

This is a two-coloured finite-dimensional c.p. approximation. Hence

```text
dim_nuc(A) <= 1.
```

The identical proof for `dim(X)=n<infinity`, using an `(n+1)`-coloured
refinement, gives `dim_nuc(A)<=n`.

## 5. Quotients have no commutative hereditary shadows

Because the bundle is locally trivial and its fibre `D` is simple, the map
`Prim(A)->X` is a homeomorphism. Thus every ideal is the section ideal over
an open subset `U` of `X`, and the corresponding quotient is the restriction
of the bundle to the closed subset `X minus U`.

Suppose a quotient `B` contains a nonzero commutative hereditary subalgebra
`C`. Choose `0!=c in C_+`, and choose `x` in the quotient base with
`c(x)!=0`. The singly generated hereditary algebra

```text
H = closure(cBc)
```

lies in `C`, hence is commutative. Evaluation at `x` maps it onto

```text
H(x) = closure(c(x)Dc(x)),
```

which is a nonzero commutative hereditary subalgebra of `D`.

Since `D` is simple, `H(x)` is full in `D`. A full hereditary subalgebra is
strongly Morita equivalent to its ambient algebra. Hence `D` is Morita
equivalent to the commutative algebra `H(x)`. Because `D` is simple, this
forces `H(x)` to have one-point spectrum and `D` to be elementary, isomorphic
to `K(Hilbert-space)`. This contradicts the assumption that `D` is both
infinite-dimensional and unital. Therefore `C=0`.
