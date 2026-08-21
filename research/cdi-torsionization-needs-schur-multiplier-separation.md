---
rg: 2
id: cdi-torsionization-needs-schur-multiplier-separation
kind: claim
title: CDI torsionization reduces to finite separation in the Schur multiplier of the projective quotient
distinct_from:
  cdi-input-projective-word-law-remains-a-group-factor-gate: that is the prior gate producing a twisted group factor; this determines when an arbitrary resulting multiplier can be replaced by a torsion one.
  cdi-noncartan-bridge-has-two-exact-gates: that requires the original class itself to be torsion; this uses density and CE closure to weaken that requirement.
---

Suppose the fixed CDI input factor `X` passes the projective-word gate, so

```text
X=L_omega(Gamma)
```

for the quotient `Gamma` of the free group on the chosen projective-word
generators.  Since `X` is non-CE, a non-hyperlinear finite central extension
exists as soon as

```text
[omega] annihilates R_fin(H_2(Gamma,Z)).                (CDI-T1)
```

In particular it is enough that `H_2(Gamma,Z)` be residually finite, or that
`Gamma` be finitely presented.  This strictly weakens gate `(G2)` in
`cdi-noncartan-bridge-has-two-exact-gates`: the original multiplier need not
be torsion; torsion classes need only be dense at it.

The current CDI/Manzoor source does not establish `(CDI-T1)`.  The projective
quotient is `F/N_scalar`; even when the original generator set is finite,
the scalar kernel is not shown finitely normally generated, and no finite
separation theorem for its Schur multiplier is provided.  For the actual
CDI wreath extension the scalar phase group is inherited from the input
representation, but that controls values of the extension cocycle, not the
finite residual of `H_2(Gamma,Z)`.

Thus the torsionization route has one exact remaining algebraic test after a
projective basis is found: compute the class on the finite residual of the
Schur multiplier.  A nonzero value there is a decisive obstruction to this
density argument; vanishing closes the non-hyperlinear-group problem.
