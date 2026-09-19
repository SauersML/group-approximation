---
rg: 2
id: torsion-dense-schur-multiplier-compiles-twisted-nonce
kind: claim
title: Torsion density in the Schur multiplier converts a non-CE twist into a non-hyperlinear finite central extension
distinct_from:
  cdi-noncartan-bridge-has-two-exact-gates: that asks whether one fixed multiplier is itself torsion; this shows it is enough for its class to be approximable by torsion classes.
  thom-central-corner-criterion: that compiles one already finite-valued twist; this produces such a non-CE torsion twist by a closure argument.
---

Let `Gamma` be a countable group, let

```text
A=H_2(Gamma,Z),
R_fin(A)=intersection_(f:A->F, F finite) ker(f),
```

and let `[omega] in H^2(Gamma,T)`.  Under the universal-coefficient
identification

```text
H^2(Gamma,T)=Hom(A,T),                                  (TDS1)
```

assume `[omega]` annihilates `R_fin(A)`.  If the twisted group factor
`L_omega(Gamma)` is not Connes embeddable, then there is a torsion class
`[theta] in H^2(Gamma,T)` such that `L_theta(Gamma)` is not Connes
embeddable.  Rephase `theta` to a finite-valued cocycle and form its finite
central extension `Gamma_tilde`.  The corresponding central corner is
`L_theta(Gamma)`, so `Gamma_tilde` is non-hyperlinear.

Equivalently, the closure of the torsion subgroup of `H^2(Gamma,T)` is

```text
ann(R_fin(H_2(Gamma,Z))).                               (TDS2)
```

In particular the hypothesis holds for every multiplier if the Schur
multiplier `H_2(Gamma,Z)` is residually finite.  It holds automatically when
`Gamma` is finitely presented, because then `H_2(Gamma,Z)` is a finitely
generated abelian group.

The obstruction is exact: a class nontrivial on `R_fin(A)` cannot be
approximated by torsion classes.  For example, if `A` has a nonzero divisible
subgroup invisible to every finite quotient, characters nontrivial on that
subgroup lie outside the torsion closure.
