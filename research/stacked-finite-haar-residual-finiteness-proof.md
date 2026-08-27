---
rg: 2
id: stacked-finite-haar-residual-finiteness-proof
kind: route
title: Separate a lamp element by its finite invariant coordinate support
target: stacked-finite-haar-modules-are-residually-finite
requires: []
---

Pontryagin duality gives

```text
A = K-hat = direct_sum_(n>=1) A_n,       A_n=K_n-hat,
```

where every `A_n` is a finite `H`-invariant abelian group.  We show directly
that `G=A rtimes H` is residually finite.

Take `(a,h) != (0,e)` in `G`.  If `h != e`, residual finiteness of `H`
provides a finite quotient `q:H->Q` with `q(h)!=e`.  The composite

```text
G -> H -> Q
```

separates `(a,h)`.

It remains to treat `(a,e)` with `a!=0`.  Since `A` is a direct sum, there is
a finite set `F` of coordinates containing the support of `a`.  Put

```text
B_F = direct_sum_(n in F) A_n.
```

Coordinate invariance makes the projection `p_F:A->B_F` `H`-equivariant.
The finite group `B_F` has finite automorphism group, so the action gives a
finite quotient

```text
rho_F:H -> Q_F <= Aut(B_F).
```

Therefore

```text
(x,g) |-> (p_F(x),rho_F(g))
```

is a homomorphism from `G` to the finite semidirect product
`B_F rtimes Q_F`.  Its value at `(a,e)` is nontrivial.  This proves residual
finiteness.

Residual finiteness implies soficity and hence hyperlinearity.  Fourier
transform identifies the displayed Haar crossed product trace-preservingly
with `L(G)`, so it is Connes embeddable.  Notice that no uniform finite
quotient of the entire action is required: the separating quotient is chosen
only after reading the finite support of the particular dual lamp element.

