---
rg: 2
id: relative-symmetry-norms-small-density-residual
kind: claim
title: One trace-zero symmetry exactly norms a residual under small-density orthogonality constraints
distinct_from:
  separable-finite-algebras-have-symmetry-bases: that constructs a complete basis in the separable diffuse case; this is one relative norming step in a nonseparable II1 factor with a strict density gap.
  non-ce-algebras-have-finite-symmetry-moment-witnesses: that extracts a finite amplification-invariant obstruction to Connes embeddability; this detects one bounded residual but supplies no uniform word packet or non-CE separation.
---

Let `M` be a `II_1` factor with

```text
dens L^2(M)=kappa>aleph_0.
```

Let `N subset M` have smaller `L^2` density and let
`Gamma subset M_sa` have cardinality below `kappa`.  If
`0!=r=r^* in M` satisfies

```text
E_N(r)=0,                 tau(gamma r)=0  for gamma in Gamma,
```

then there is a trace-zero symmetry `s=s^*=s^(-1)` satisfying the same
orthogonality conditions and

```text
<r,s>_2=||r||_2^2/||r||_infinity.                     (RSN1)
```

This is an exact one-involution detector for a bounded residual.  The
symmetry depends on the ambient residual and constraint set, so the lemma
does not supply a uniform finite group-word decoder or a groupification of a
non-CE factor.
