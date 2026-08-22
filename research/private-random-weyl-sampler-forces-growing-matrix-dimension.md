---
rg: 2
id: private-random-weyl-sampler-forces-growing-matrix-dimension
kind: claim
title: A private random Weyl sampler forces growing matrix dimension
distinct_from:
  private-random-generator-columns-form-affine-rank-condenser: that proves constant syndrome distance only for scalar bilinear Weyl forms; this uniformly controls every pair of exact additive matrix-valued representations up to a growing dimension cutoff.
  generator-column-pauli-test-globalizes-but-does-not-pin-sites: that uses a complete product of two short code-column supports and yields exponential dimension/global exactification; this uses a private matching of random pairs and yields the weaker but sufficient lower bound d greater than sqrt(N).
  expander-cloud-reduction-preserves-pauli-dimension-gap: that duplicates dense logical tests and synchronizes occurrences by equality expanders; this uses distinct private random pairs and no mixed occurrence reuse.
---

For every fixed `K>=1` there are constants `C_K,eta>0` such that, for every
sufficiently large `r`, one can choose

```text
m<=C_K r^2
```

private pairs `(a_t,b_t) in F_2^r times F_2^r` with the following property.
For every `d<=K r` and every two exact additive unitary representations

```text
X,Z:F_2^r -> U(d),
```

the sampled normalized-HS Weyl energy satisfies

```text
(1/m) sum_t ||X(a_t)Z(b_t)
 -(-1)^(a_t.b_t)Z(b_t)X(a_t)||_2^2 >= eta.             (PRW1)
```

Hence sampled energy below `eta` forces `d>K r` on the same Hilbert space.
After increasing the lower threshold for `r`, `eta` may be chosen
independently of `K`; only the sampling constant depends on `K`.
Embedding the active `r`-space in ambient dimension `N=r^2`, appending any
asymptotically good dimension-`N` generator block, and treating every sample
as its own left/right occurrence gives

```text
K,K'=Theta(N),       maximum mixed occurrence degree=1,
d>sqrt(N).                                                  (PRW2)
```

The appended base block preserves uniform spectral constants.  Thus
`bounded-incidence-generator-column-minrank-witness` is established for
exact additive X/Z laws, including arbitrary matrix-valued multiplicity and
relative basis position.  The scalar affine-rank condenser was not an
artifact of Pauli normal form.

The theorem itself is proved by probabilistic existence, but
`private-weyl-samplers-admit-recursive-selection` turns it into a recursive
family: goodness of a finite candidate is decidable by real quantifier
elimination and lexicographic search therefore terminates.  What remains is
not sample effectivity.  It is bounded-area group-word naming together with
uniform correction of approximate same-basis laws to exact additive actions,
the interface isolated in
`same-basis-rounding-interface-for-sparse-weyl-sampler`.

## Bounded-factor flexibility

The strengthened `d<=K r` quantifier is the form needed by the occurrence
compiler.  A decoder may pass from an original `d`-dimensional tuple to an
exact additive model of dimension at most `K d`, for one fixed `K`, without
weakening the contradiction: choose the sampler parameter after `d` and use
the theorem with the same fixed enlargement factor.  Thus no same-dimension
rounding hypothesis is required at this point.
