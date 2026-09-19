---
rg: 2
id: cdi-torsionization-schur-gate-proof
kind: route
title: Apply torsion-density to the projective quotient and audit finite presentability
target: cdi-torsionization-needs-schur-multiplier-separation
requires:
  - cdi-input-projective-word-law-remains-a-group-factor-gate
  - torsion-dense-schur-multiplier-compiles-twisted-nonce
---

Once the projective-word law identifies `X=L_omega(Gamma)`, apply
`torsion-dense-schur-multiplier-compiles-twisted-nonce`.  Condition
`(CDI-T1)` puts `[omega]` in the closure of the torsion classes.  Non-CE is
closed under the contrapositive diagonal argument there, so one torsion
twist is non-CE and its finite central extension is non-hyperlinear.

If `Gamma` is finitely presented, its Schur multiplier is finitely generated
abelian and `(CDI-T1)` is automatic.  In the CDI construction, however,
`Gamma` is obtained by quotienting a finitely generated free group (or the
chosen property-`(T)` host) by the scalar kernel of a von Neumann
representation.  Neither CDI Proposition 3.8 nor its three-generator lemma
states that this kernel is finitely normally generated.  A quotient of a
finitely presented group by an arbitrary normal subgroup need not be
finitely presented, so finite presentation cannot be inferred.

The universal-coefficient description also proves the negative assertion:
if `[omega]` is nontrivial on `R_fin(H_2(Gamma,Z))`, it lies outside the
closure of all torsion classes, so no finite-moment torsion approximation of
this cohomology class exists.
