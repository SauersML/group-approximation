---
rg: 2
id: hs-stable-kazhdan-finite-bi-index-pair-gives-site-coherence
kind: claim
title: HS stability of the acting group and a Kazhdan stabilizer give uniform coset-site coherence
distinct_from:
  scaled-kazhdan-transport: that rounds almost invariant matrix coefficients for a fixed exact Kazhdan representation; this first exactifies the acting group and then uses that projection to make a lamp independent of every coset representative.
  uniform-hs-site-coherence-for-finite-bi-index-pair: that asks for one concrete subgroup pair with the complete property; this proves a reusable sufficient criterion in terms of same-dimension HS stability and a stabilizer spectral gap.
---

Let `L=<S|R>` be same-dimension stable for normalized Hilbert--Schmidt
approximate representations, with a modulus tending to zero.  Let `H=<T>` be
a finitely generated property-(T) subgroup, where the finite words `T` are
fixed in `S`.  Assume `H\L/H` is finite.

Then the subgroup pair has the site-coherence conclusion of `(FSC1)`, with a
modulus depending only on the stability modulus of `L`, the Kazhdan constant
of `(H,T)`, and the finite presentation data.  In particular, if the
stability modulus is linear in squared normalized-HS energy, the constant in
`(FSC1)` is dimension independent.

More explicitly, on any positive marked block on which the restriction of a
microstate to `L` has defect `delta`, replace its `S`-tuple by an exact
same-dimensional representation `sigma` at generator distance `eta(delta)`.
If the lamp involution `A_0` almost commutes with the words in `T`, the
adjoint Kazhdan inequality gives

```text
dist_2(A_0, Comm(sigma(H)))
  <= kappa^(-1) max_(t in T) ||[A_0,sigma(t)]||_2.                 (SKC1)
```

Conditional expectation followed by spectral sign rounding produces an
involution `A in Comm(sigma(H))` with the same asymptotic bound.  Therefore

```text
A_(gH)=sigma(g) A sigma(g)^*
```

is exactly independent of the representative.  Every ordered pair of
distinct cosets is an `L`-translate of one of the finitely many double-coset
representatives, so unitary conjugation propagates the corresponding base
pair error with no word-length or orbit-size loss.

The same argument applies blockwise after rounding the central marked
involution and its almost invariant negative spectral projection.  A lower
bound on marked separation keeps that block at positive normalized density;
discarding the rounding residue costs only the original relator energy.

