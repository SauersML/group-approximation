---
rg: 2
id: all-abelian-uniform-hs-rounding-gives-global-pvm
kind: claim
title: Uniform all-pairs control of an arbitrary abelian lamp module rounds to one same-dimensional global PVM
distinct_from:
  finite-abelian-hs-almost-actions-round-in-the-same-dimension: that proves same-dimensional rounding for one finite abelian table from Gowers-Hatami; this is uniform over all countable abelian groups, including one infinite augmentation module.
  property-t-must-upgrade-global-augmentation-rounding: that asks how a finite semidirect presentation can expose the whole module with uniform defect; this proves the analytic rounding after such exposure.
  same-basis-rounding-interface-for-sparse-weyl-sampler: that starts from bounded occurrence tests rather than a map on every element of the abelian group.
---

ESTABLISHED.  There is a universal modulus `omega(epsilon)->0` with the
following property.  For every countable abelian group `M`, every `d`, and
every map

```text
phi:M -> U(d)
```

satisfying

```text
sup_(x,y in M) ||phi(x+y)-phi(x)phi(y)||_(2,d) <= epsilon,   (AUR1)
```

there is an exact representation `rho:M->U(d)` such that

```text
sup_(x in M) ||phi(x)-rho(x)||_(2,d) <= omega(epsilon).      (AUR2)
```

This is the `d=1` irreducible-dimension case of Akhtiamov--Dogon,
arXiv:2010.10304, Theorem 3.2: the class of amenable groups whose
finite-dimensional irreducibles have dimension at most `d` is uniformly
Hilbert--Schmidt stable, with a modulus uniform over the class.  Every
abelian group is amenable and all its irreducibles are one-dimensional.

If `M` has exponent two, `rho` is a commuting family of selfadjoint
involutions and hence has one finite-support joint spectral PVM

```text
rho(m)=sum_(chi in F) chi(m) P_chi,       |F|<=d.             (AUR3)
```

Thus the **analytic** infinite-family simultaneous-rounding problem is
solved once `(AUR1)` is available.  A fixed seed is preserved quantitatively
by `(AUR2)`, and any uniformly controlled actor covariance for `phi`
transfers to `rho` with an additional `2 omega(epsilon)` error.

This theorem does not say that a finite presentation supplies `(AUR1)`.
Evaluating one word for each virtual lamp gives multiplication errors bounded
by the van Kampen areas of the corresponding identities, which may be
unbounded.  The remaining same-basis gate is therefore a finite-template
all-pairs exposure/compiler problem, not a cardinality-dependent matrix
diagonalization problem.
