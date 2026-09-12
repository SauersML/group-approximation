---
rg: 2
id: stone-additive-semidir-product-loses-manzoor-measure
kind: claim
title: The canonical additive Stone semidirect product loses the Manzoor action measure
distinct_from:
  stone-multiplicative-locus-is-haar-null-in-additive-dual: that is the abstract Boolean-algebra theorem; this applies it to a countable invariant generator of a Manzoor stabilizer realization and writes the proposed group explicitly.
  random-coset-lamp-correlations-realize-every-irs-character: that preserves the IRS membership values in subgroup-dependent wreath fibers; this shows why replacing the random fibers by the additive group of one measure algebra changes their trace.
---

Let `F actson (X,mu)` be any standard pmp stabilizer realization of Manzoor's
IRS; one may take the labeled-Schreier realization.  Choose a countable
`F`-invariant Boolean algebra `A` generating the measurable sigma algebra
modulo null sets, and put `K=(A,symmetric_difference)`.  This gives the
concrete countable amenable-by-free group

```text
G_Stone=K semidirect F.                                  (SAS1)
```

The intended event projections would be
`p_a=(1-lambda_K(a))/2`.  But the canonical trace of `L(G_Stone)` restricts
to the regular trace of `K`, hence

```text
tau_(L(G_Stone))(p_a)=1/2       for every nonnull a.      (SAS2)
```

In contrast, the Stone representation of the original probability algebra
requires `tau(p_a)=mu(a)`.  In the labeled-Schreier realization, enlarge `A`
to contain the event that the root label lies in a fixed interval of length
`1/3`; then `(SAS2)` gives `1/2` while the desired trace is `1/3`.

By `stone-multiplicative-locus-is-haar-null-in-additive-dual`, the original
probability space sits as a singular Boolean-multiplicative locus in the
additive dual, so no nonzero central corner of `L(G_Stone)` recovers it.
Any corner that still makes the literal `K` elements a representation must
commute with `K` and has additive-Haar-absolutely-continuous spectral measure.

Therefore `(SAS1)` is an explicit algebraic action envelope only for the
wrong uniform trace.  Correcting it requires enforcing all intersection
relations `p_(a meet b)=p_a p_b` in a nonregular sector.  That is exactly the
nonlinear BCS/groupification gate and supplies no shortcut to a
non-hyperlinear group.

