---
rg: 2
id: fd-invisible-hecke-type-necessity-proof
kind: route
title: Compress every finite-dimensional host representation and tensor-generate the finite packet
target: no-ce-hecke-host-needs-an-fd-invisible-type
requires:
  - nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear
  - augmentation-one-corner-retains-a-character
  - finite-support-corner-localizes-obstruction
---

Extend `(FVI2)` linearly to a star homomorphism

```text
pi:C[G] -> M_n(C).
```

The element `pi(q)` is a projection.  If it were nonzero, composition with
`Phi` would give a unital star homomorphism

```text
B -> pi(q) M_n(C) pi(q),                              (FVP1)
```

where the unit on the right is `pi(q)`.  Pulling back the normalized matrix
trace of this nonzero corner gives a finite-dimensional, hence
Connes-embeddable, tracial state on `B`.  This contradicts the defining
hypothesis on `B` and proves `(FVI3)`.  Fourier decomposition of `C[K]`
gives the equivalent `K`-type formulation.

Now suppose finite-dimensional representations of `G` separate its points.
Because `K` is finite, a finite direct sum of such representations restricts
to a faithful representation `rho` of `K`.  The matrix coefficients of
`rho` and its contragredient separate the points of `K`; since `K` is a
finite set, the unital algebra they generate is all of `C^K`.  Equivalently,
every irreducible representation of `K` occurs in a tensor word built from
`rho` and `rho^*`.  These tensor words are restrictions of
finite-dimensional representations of `G`.

Choose an irreducible block on which the nonzero projection `q` is nonzero.
One of those tensor-word representations contains that block and therefore
does not annihilate `q`, contradicting `(FVI3)`.  Hence `G` is not maximally
almost periodic.  Residual finiteness implies maximal almost periodicity
(alternatively, one finite quotient injective on `K` has a regular
representation containing every `K`-type), proving the final assertion.
