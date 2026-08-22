# The rank-one braid identity closes the last two centralizer directions

Put

```text
b=x_beta,       B=x_(-beta),       w=b B^(-1)b,       z=w^4.
```

Kassel Lemma 2.2 states

```text
w_beta=w_(-beta)^(-1).
```

Since `w_(-beta)=B b^(-1)B`, this is exactly

```text
b B^(-1)b = B^(-1)b B^(-1).                            (BR)
```

Thus the remaining seam is the ordinary three-letter braid relation for
`x=b` and `y=B^(-1)`.

## Exact centrality

Write `w=xyx=yxy`. Then

```text
w x = y w,       w y = x w.
```

Consequently conjugation by `w` exchanges `x` and `y`, so `w^2` centralizes
both. In particular

```text
[z,b]=[z,B]=1.                                          (C)
```

Combined with `kassel-210-forces-long-weyl-quarter-turn`, which proves that
`z` centralizes `x_alpha,x_(alpha+beta),x_(2alpha+beta)`, and the symmetric
negative-root formulas in Kassel Lemma 2.3, this recovers centrality of the
long-root fourth power on all eight root generators.

The displayed 24-relator presentation does not list `(BR)` as a primitive
rank-one relator. Kassel derives it as Lemma 2.2 using the Steinberg
parametrization `x_gamma(-1)=x_gamma^(-1)`. Therefore no single one of
(2.11),(2.13)--(2.15) should be mislabeled as the missing relation: their
role, together with the earlier mixed relations, is to realize the full
Steinberg presentation from which the rank-one identity follows. The exact
interface needed by any local atlas is `(BR)` itself.

## Dimension-free HS propagation

For arbitrary unitaries `x,y`, put

```text
w=xyx,       v=yxy,       epsilon=||w-v||_2.
```

Then

```text
||w x-y w||_2 = epsilon,
||w y-x w||_2 = epsilon.
```

Unitary invariance and two applications of the triangle inequality give

```text
||[w^2,x]||_2 <= 2 epsilon,
||[w^2,y]||_2 <= 2 epsilon,
||[w^4,x]||_2 <= 4 epsilon,
||[w^4,y]||_2 <= 4 epsilon.                             (HS)
```

Together with the bounded-word perturbation of the quarter-turn identities,
`(HS)` gives a dimension-free estimate from presentation defect to the
commutators of `z` with every root generator, once a bounded-area derivation
of `(BR)` from the chosen presentation is included.

## Why this still does not prove the Maslov gap

In the nontrivial Maslov sector, `z=omega I` is already perfectly central.
Deligne finite-dimensional invisibility says that an **exact**
finite-dimensional representation cannot have this scalar. It does not say
that an approximate representation whose relators tend to zero must be near
an exact one. Thus centralization plus invisibility proves exact-sector
emptiness, but no positive normalized-HS defect floor.

To pass from `(HS)` to non-hyperlinearity one still needs the ucp/stability
input already isolated in `maslov-sector-tracial-generator-ucp-liftability`
(or an equivalent positive-kernel/SOS inequality). No approximate collapse
is claimed here.

