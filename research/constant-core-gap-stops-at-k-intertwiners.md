---
rg: 2
id: constant-core-gap-stops-at-k-intertwiners
kind: claim
title: The constant core spectral gap cannot identify finite-section isotypes
distinct_from:
  two-sheet-projective-closure-forces-equivalent-carriers: that shows full-carrier coefficient closure forces equivalent isotypes; this proves the constant subgroup alone cannot supply that full-carrier hypothesis
  presentation-defect-does-not-control-off-commutant-mass: that gives arbitrary regular-carrier countermodels; this isolates the exact zero mode surviving even after direct constant-core covariance tests
  jacobson-projective-two-sheet-actions-collapse: that kills a closed SO(3) coefficient action; this locates the nonclosed Hecke-intertwiner face where such an action fails
---

Let

```text
K=GL_28(F_2) < F_N=GL_(28N)(F_2),             N>=2.
```

For representations `pi_i:K->U(H_i)` and
`T in Hom(H_1,H_0)`, let `P_KT` be the orthogonal projection onto
`Hom_K(H_1,H_0)`. Then

```text
||T-P_KT||_(HS)^2
 = (1/(2|K|)) sum_(k in K)
      ||pi_0(k)T-Tpi_1(k)||_(HS)^2.                    (CCG1)
```

A fixed generating set and the finite-group spectral gap replace the
all-group average by a dimension-free generator bound. Thus direct core
covariance tests do force an off-diagonal coefficient toward
`Hom_K`.

They do not force it toward `Hom_(F_N)`. Put `F=F_N`,
`d=[F:K]`, and take the equal-dimensional pair

```text
Pi_0=1_F^(directSum d) on C^d,
Pi_1=Ind_K^F(1) on ell^2(F/K).                          (CCG2)
```

There is a unit Hilbert--Schmidt operator `T:H_1->H_0` such that

```text
T in Hom_K(Pi_1|K,Pi_0|K),
T orthogonal to Hom_F(Pi_1,Pi_0).                       (CCG3)
```

Hence the left side and every covariance error in `(CCG1)` vanish, while

```text
dist_(HS)(T,Hom_F(Pi_1,Pi_0))=1.                        (CCG4)
```

After decomposing `Pi_1` into irreducibles, `(CCG3)` yields a nontrivial
irreducible `F`-isotype with a `K`-fixed vector and therefore an exact
off-diagonal `K`-intertwiner to a trivial carrier multiplicity. The two
full `F`-sectors are inequivalent.

Consequently the constant-core spectral gap cannot prove that a
carrier-assisted two-sheet cancellation comes from equivalent isotypes.
It reduces the survivor to a concrete Hecke face, `Hom_K` minus
`Hom_F`. Additional long-router or nonconstant-root relations must control
that face. This counterexample is a spectral firewall, not a
head-retaining microstate construction.

DERIVATION
quasiregular-fixed-coset-produces-a-false-intertwiner-proof
